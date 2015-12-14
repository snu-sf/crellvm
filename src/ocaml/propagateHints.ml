(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
open Interpreter
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open Vars_aux
open Validator_aux
open Extraction_defs
open Utility
open Dom_list
open Dom_tree

type atom = AtomImpl.atom

let rec string_of_dtree dtree =
  match dtree with
  | DT_node (a, dtrees) -> a ^ "->(" ^ (string_of_dtrees dtrees) ^  ")"
and string_of_dtrees dtrees =
  match dtrees with
  | DT_nil -> ""
  | DT_cons (dtree, dtrees) -> (string_of_dtree dtree) ^ ", " ^ (string_of_dtrees dtrees)

let rec find_in_dtree a dtree =
  match dtree with
  | DT_node (a', dtrees) ->
     if a = a'
     then Some dtree
     else find_in_dtrees a dtrees
and find_in_dtrees a dtrees =
  match dtrees with
  | DT_nil -> None
  | DT_cons (dtree, dtrees) ->
     (match find_in_dtree a dtree with
      | Some result -> Some result
      | None -> find_in_dtrees a dtrees)

let rec collapse_dtree ?(acc=AtomSetImpl.empty) dtree =
  match dtree with
  | DT_node (a, dtrees) -> collapse_dtrees ~acc:(AtomSetImpl.add a acc) dtrees
and collapse_dtrees ?(acc=AtomSetImpl.empty) dtrees =
  match dtrees with
  | DT_nil -> acc
  | DT_cons (dtree, dtrees) ->
     let acc' = collapse_dtree ~acc:acc dtree in
     let acc'' = collapse_dtrees ~acc:acc' dtrees in
     acc''

let dom_by a dtree =
  let dtree =
    match find_in_dtree a dtree with
    | None -> failwith "translateHints sdom_by"
    | Some dtree -> dtree
  in
  let result = collapse_dtree dtree in
  result

(* @arg f: block id
   @arg t: block id
   @arg succ: graph between block ids
   @return: set of block ids
     - reachable from f
     - without passing through t
 *)
let reachable_filtered (f:atom) (ids:AtomSetImpl.t) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : bool * AtomSetImpl.t =
  let visit_f = ref false in
  let rec r (worklist:atom list) (visit:AtomSetImpl.t) : bool * AtomSetImpl.t =
    match worklist with
    | [] -> (!visit_f, visit)
    | work::worklist ->
       let (worklist, visit) =
         (match Maps_ext.ATree.get work succs with
          | None -> (worklist, visit)
          | Some succs ->
             List.fold_left
               (fun (worklist, visit) succ ->
                let _ =
                  if succ = f
                  then
                    (* let _ = print_endline (sprintf "visit_f from %s to %s" work succ) in *)
                    visit_f := true
                  else ()
                in
                if AtomSetImpl.mem succ visit or not (AtomSetImpl.mem succ ids)
                then (worklist, visit)
                else (succ::worklist, AtomSetImpl.add succ visit))
               (worklist, visit)
               succs)
       in
       r worklist visit
  in
  r [f] (AtomSetImpl.singleton f)

(* @arg f: block id
   @arg succ: graph between block ids
   @return: set of block ids
     - reachable from f
 *)
let reachable (f:atom) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : AtomSetImpl.t =
  let rec r (worklist:atom list) (reached:AtomSetImpl.t) : AtomSetImpl.t =
    match worklist with
    | [] -> reached
    | work::worklist ->
       let (worklist, reached) =
         match Maps_ext.ATree.get work succs with
         | None -> (worklist, reached)
         | Some succs -> 
           List.fold_left
             (fun (worklist,reached) succ ->
               if AtomSetImpl.mem succ reached
               then (worklist, reached)
               else (succ::worklist, AtomSetImpl.add succ reached)
             )
             (worklist, reached)
             succs
       in
       r worklist reached
  in
  r [f] AtomSetImpl.empty

(* the set of nodes that is reachable to "t" without visiting "f" in "fd". *)
let reachable_to (t:atom) (ids:AtomSetImpl.t) (fd:LLVMsyntax.fdef) : bool * AtomSetImpl.t =
  if not (AtomSetImpl.mem t ids)
  then (false, AtomSetImpl.empty)
  else
    let predecessors = Cfg.predecessors fd in
    reachable_filtered t ids predecessors

(* the set of nodes that is reachable from "f". *)
let reachable_from (f:atom) (fd:LLVMsyntax.fdef) : AtomSetImpl.t =
  reachable f (Cfg.successors fd)

(* @arg var: variable
   @arg fd: function definition
   @return: defined block id, nth instr
 *)
let block_of_def_cmd (var:atom) (fd:LLVMsyntax.fdef) : atom * int =
  let LLVMsyntax.Coq_fdef_intro (fheader, blocks) = fd in
  let nth = ref 0 in
  let bid =
    List.find
      (fun (l, stmts) ->
       let LLVMsyntax.Coq_stmts_intro (_, cmds, _) = stmts in
       let rec f n cmds =
         match cmds with
         | [] -> None
         | cmd::cmds ->
            if Datatypes.Coq_inl var = def_cmd cmd
            then Some n
            else f (n + 1) cmds
       in
       match f 0 cmds with
       | None -> false
       | Some n -> nth := n; true)
      blocks
  in
  (fst bid, !nth)

type invariant_elt_t =
  | Eq_reg of id_ext * rhs_ext
  | Eq_heap of value_ext * LLVMsyntax.typ * LLVMsyntax.align * value_ext
  | Neq_reg of id_ext * id_ext
  | Neq_reg_global of id_ext * atom
  | OldAlloca of id_ext

type hint_elt_t =
  | Hint_maydiff of id_ext
  | Hint_original of invariant_elt_t
  | Hint_optimized of invariant_elt_t
  | Hint_iso_original of id_ext
  | Hint_iso_optimized of id_ext

let make_eq_reg lhs rhs =
  match lhs, rhs with
  | LLVMsyntax.Coq_value_id l', LLVMsyntax.Coq_value_id r' ->
     Eq_reg (add_ntag l', Coq_rhs_ext_value (Coq_value_ext_id (add_ntag r')))
  | LLVMsyntax.Coq_value_id i, LLVMsyntax.Coq_value_const c
  | LLVMsyntax.Coq_value_const c, LLVMsyntax.Coq_value_id i ->
     Eq_reg (add_ntag i, Coq_rhs_ext_value (Coq_value_ext_const c))
  | LLVMsyntax.Coq_value_const _, LLVMsyntax.Coq_value_const _ ->
     failwith "make_eq_reg: eq_reg with (const, const)"

let make_eq_insn lhs insn (phivars:atom list) (pbid_opt:atom option) =
  match insn with
  | LLVMsyntax.Coq_insn_phinode (LLVMsyntax.Coq_insn_phi (_, _, values)) ->
     let (value, _) =
       match pbid_opt with
       | None -> failwith "make_eq_insn phinode without pbid"
       | Some pbid ->
          List.find
            (fun (_, bid) -> bid = pbid)
            values
     in
     Eq_reg (add_ntag lhs, Coq_rhs_ext_value (oldify_value_ext phivars (add_ntag_value value)))
  | LLVMsyntax.Coq_insn_cmd cmd ->
     (match add_ntag_cmd cmd with
      | Some rhs_ext ->
         Eq_reg (add_ntag lhs, rhs_ext)
      | None ->
         (match cmd with
          | LLVMsyntax.Coq_insn_load (x, ty, p, a) ->
             Eq_heap (add_ntag_value p, ty, a, Coq_value_ext_id (add_ntag x))
          | LLVMsyntax.Coq_insn_store (x, ty, v, p, a) ->
             Eq_heap (add_ntag_value p, ty, a, add_ntag_value v)
          | _ ->
             failwith "make_eq_insn cmd"))
  | LLVMsyntax.Coq_insn_terminator terminator ->
     failwith "make_eq_insn terminator"

let make_neq_reg lhs rhs =
  match lhs, rhs with
  | LLVMsyntax.Coq_value_id l, LLVMsyntax.Coq_value_id r ->
     Neq_reg (add_ntag l, add_ntag r)
  | LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (_, l)), LLVMsyntax.Coq_value_id r ->
     Neq_reg_global (add_ntag r, l)
  | LLVMsyntax.Coq_value_id l, LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (_, r)) ->
     Neq_reg_global (add_ntag l, r)
  | _, _ ->
     failwith "make_neq_reg not with (id, id), (gid, id), (id, gid)"

let make_alloca var = OldAlloca (add_ntag var)

(*
let newlify_alloca hint_elt =
  match hint_elt with
  | Hint_original (OldAlloca var) -> Hint_original (NewAlloca var)
  | Hint_optimized (OldAlloca var) -> Hint_optimized (NewAlloca var)
  | _ -> hint_elt
*)

let propagate_in_eqs
      (inv:invariant_elt_t) (eqs:eqs_t) : eqs_t =
  match inv with
  | Eq_reg (id_ext, rhs_ext) ->
     {eqs with
       eqs_eq_reg = EqRegSetImpl.add (id_ext, rhs_ext) eqs.eqs_eq_reg}
  | Eq_heap (lhs, typ, align, rhs) ->
     {eqs with
       eqs_eq_heap = EqHeapSetImpl.add (((lhs, typ), align), rhs) eqs.eqs_eq_heap}
  | Neq_reg (lhs, rhs) ->
     {eqs with
       eqs_neq_reg =
         NeqRegSetImpl.add
           (lhs, Datatypes.Coq_inl rhs)
           eqs.eqs_neq_reg}
  | Neq_reg_global (lhs, rhs) ->
     {eqs with
       eqs_neq_reg =
         NeqRegSetImpl.add
           (lhs, Datatypes.Coq_inr rhs)
           eqs.eqs_neq_reg}
  | OldAlloca var ->
     {eqs with
       eqs_eq_reg = EqRegSetImpl.add (var, Coq_rhs_ext_old_alloca) eqs.eqs_eq_reg}

let propagate_in_insn_hint
      (hint:hint_elt_t) (insn_hint:insn_hint_t) : insn_hint_t =
  match hint with
  | Hint_maydiff m ->
     {insn_hint with
       hint_maydiff = IdExtSetImpl.add m insn_hint.hint_maydiff}
  | Hint_original inv ->
     {insn_hint with
       hint_invariant =
         {insn_hint.hint_invariant with
           invariant_original =
             propagate_in_eqs
               inv 
               insn_hint.hint_invariant.invariant_original}}
  | Hint_optimized inv ->
     {insn_hint with
       hint_invariant =
         {insn_hint.hint_invariant with
           invariant_optimized =
             propagate_in_eqs
               inv 
               insn_hint.hint_invariant.invariant_optimized}}
  | Hint_iso_original p ->
    {insn_hint with
      hint_invariant = 
        {insn_hint.hint_invariant with
          iso_original = IdExtSetImpl.add p insn_hint.hint_invariant.iso_original}}
  | Hint_iso_optimized p ->
    {insn_hint with
      hint_invariant = 
        {insn_hint.hint_invariant with
          iso_optimized = IdExtSetImpl.add p insn_hint.hint_invariant.iso_optimized}}

let propagate_in_cmds_hint nth_f nth_t hint_elt hints =
  mapi
    (fun i hint ->
     let hint =
       if (match nth_f with
           | ParseHints.PhinodePos -> true
           | ParseHints.CommandPos nth_f -> nth_f <= i
           | ParseHints.TerminatorPos -> false
           | ParseHints.UnspecifiedPos -> false)
          && (match nth_t with
              | ParseHints.PhinodePos -> false
              | ParseHints.CommandPos nth_t -> i <= nth_t
              | ParseHints.TerminatorPos -> true
              | ParseHints.UnspecifiedPos -> false)
       then propagate_in_insn_hint hint_elt hint
       else hint
     in
     hint)
    hints

(* propagate equation in a block
   @arg nth_f: from nth instruction
   @arg nth_t: to nth instruction
 *)
let propagate_in_block_hint
      ?(phiid_opt:atom option=None)
      (nth_f:ParseHints.rhint_block_pos_t) (nth_t:ParseHints.rhint_block_pos_t)
      (hint_elt:hint_elt_t)
      (block_hint:block_hint_t) : block_hint_t =
  let block_hint =
    if nth_f <> ParseHints.PhinodePos
    then block_hint
    else
      let phi_hint =
        match phiid_opt with
        | Some phiid ->
           let split_phi_hint =
             match Alist.lookupAL block_hint.phi_hint phiid with
             | None -> failwith "propagate_in_block_hint"
             | Some hint -> hint
           in
           let split_phi_hint =
             propagate_in_insn_hint hint_elt split_phi_hint
           in
           let phi_hint = 
             Alist.updateAddAL
               block_hint.phi_hint
               phiid
               split_phi_hint
           in
           phi_hint
        | None ->
           List.map
             (fun (phiid, hint) ->
              (phiid,
               (propagate_in_insn_hint hint_elt hint)))
             block_hint.phi_hint
      in
      {block_hint with phi_hint = phi_hint}
  in

  let block_hint =
    let cmds_hint =
      match phiid_opt with
      | Some phiid ->
         let split_cmds_hint =
           match Alist.lookupAL block_hint.cmds_hint phiid with
           | None -> failwith "propagate_in_block_hint"
           | Some hint -> hint
         in
         let split_cmds_hint =
           propagate_in_cmds_hint nth_f nth_t hint_elt split_cmds_hint
         in
         let cmds_hint = 
           Alist.updateAddAL
             block_hint.cmds_hint
             phiid
             split_cmds_hint
         in
         cmds_hint
      | None ->
         List.map
           (fun (phiid, hint) ->
            (phiid,
             (propagate_in_cmds_hint nth_f nth_t hint_elt hint)))
           block_hint.cmds_hint
    in
    {block_hint with cmds_hint = cmds_hint}
  in

  let block_hint =
    if nth_f = ParseHints.UnspecifiedPos || nth_t <> ParseHints.TerminatorPos
    then block_hint
    else
      let term_hint =
        propagate_in_insn_hint hint_elt block_hint.term_hint
      in
      {block_hint with term_hint = term_hint}
  in
  block_hint

let oldify_invariant_elt (ids:atom list) (elt:invariant_elt_t) : invariant_elt_t =
  match elt with
  | Eq_reg (id, Coq_rhs_ext_value rhs) -> Eq_reg (id, Coq_rhs_ext_value (oldify_value_ext ids rhs))
  | _ -> elt

let oldify_hint_elt (ids:atom list) (elt:hint_elt_t) : hint_elt_t =
  match elt with
  | Hint_maydiff _ -> elt
  | Hint_original elt -> Hint_original (oldify_invariant_elt ids elt)
  | Hint_optimized elt -> Hint_optimized (oldify_invariant_elt ids elt)
  | Hint_iso_original _ -> elt
  | Hint_iso_optimized _ -> elt

let next_pos pos =
  match pos with
  | ParseHints.PhinodePos -> ParseHints.CommandPos 0
  | ParseHints.CommandPos i -> ParseHints.CommandPos (i + 1)
  | ParseHints.TerminatorPos -> ParseHints.UnspecifiedPos
  | ParseHints.UnspecifiedPos -> pos

let propagate_iso 
      (block_f, nth_f) 
      (hint_elt:hint_elt_t)
      (fd:LLVMsyntax.fdef) (hint:fdef_hint_t) (dom_tree:atom coq_DTree)
    : fdef_hint_t =
  (* get all reachable blocks *)
  let reachable_to_t = reachable_from block_f fd in
  
  (* propagate to all the reachable blocks *)
  let block_hints =
    AtomSetImpl.fold
      (fun bid hint ->
        let block_hint =
          match Alist.lookupAL hint bid with
          | None -> failwith "propagate: no bid in hint"
          | Some block_hint -> block_hint
        in
        let nth_f =
          if bid = block_f && AtomSetImpl.mem block_f reachable_to_t
          then ParseHints.PhinodePos
          else next_pos nth_f
        in
        let nth_t = ParseHints.TerminatorPos in
        let block_hint =
          propagate_in_block_hint
            nth_f nth_t
            hint_elt
            block_hint
        in
        Alist.updateAddAL hint bid block_hint)
      (AtomSetImpl.add block_f reachable_to_t)
      hint
  in
  block_hints

(* propagate "cmd" as an invariant from "f" to "t" in "hint".
   lr=false means the left program, lr=true means the right program.
 *)
let propagate
      ?(block_prev_opt=None)
      (block_f, nth_f) (block_t', nth_t')
      (hint_elt:hint_elt_t)
      (fd:LLVMsyntax.fdef) (hint:fdef_hint_t) (dom_tree:atom coq_DTree)
    : fdef_hint_t =
  let (block_t, nth_t) =
    match block_prev_opt with
    | Some block_prev -> (block_prev, ParseHints.TerminatorPos)
    | None -> (block_t', nth_t')
  in
  let (pass_through_t, reachable_to_t) =
    if block_f = block_t && ParseHints.rhint_block_pos_lt nth_f nth_t
    then (false, AtomSetImpl.singleton block_f)
    else if block_f = block_t' && ParseHints.rhint_block_pos_lt nth_f nth_t'
    then (false, AtomSetImpl.empty)
    else
      let dom_by_f = dom_by block_f dom_tree in
      reachable_to block_t dom_by_f fd
  in
  (* let _ = print_endline ("block_f: " ^ (ParseHints.string_of_pos (block_f, nth_f))) in *)
  (* let _ = print_endline ("block_t': " ^ (ParseHints.string_of_pos (block_t', nth_t'))) in *)
  (* let _ = print_endline ("block_t: " ^ (ParseHints.string_of_pos (block_t, nth_t))) in *)
  (* let _ = print_endline ("pass_through_t, reachable_to_t: " ^ (string_of_bool pass_through_t) ^ ", " ^ (PrintHints.string_of_atoms reachable_to_t)) in *)
  
  let block_hints =
    AtomSetImpl.fold
      (fun bid hint ->
       let block_hint =
         match Alist.lookupAL hint bid with
         | None -> failwith "propagate: no bid in hint"
         | Some block_hint -> block_hint
       in
       let nth_f =
         if bid = block_f
         then next_pos nth_f
         else ParseHints.PhinodePos
       in
       let nth_t =
         if bid = block_t && (not pass_through_t)
         then nth_t
         else ParseHints.TerminatorPos
       in
       let block_hint =
         propagate_in_block_hint
           nth_f nth_t
           hint_elt
           block_hint
       in
       Alist.updateAddAL hint bid block_hint)
      reachable_to_t
      hint(*.block_hints*)
  in
  let block_hints =
    match block_prev_opt with
    | None -> block_hints
    | Some block_prev ->
       (* 1. phinode pos *)
       let block_hint =
         match Alist.lookupAL block_hints block_t' with
         | None -> failwith "propagate: no bid in hint"
         | Some block_hint -> block_hint
       in
       let (block_hint, nth_f) =
         if block_f = block_t' && ParseHints.rhint_block_pos_lt nth_f nth_t'
         then (block_hint, next_pos nth_f)
         else
           let block_hint =
             propagate_in_block_hint
               ~phiid_opt:block_prev_opt
               ParseHints.PhinodePos ParseHints.PhinodePos
               hint_elt
               block_hint
           in
           let nth_f = ParseHints.CommandPos 0 in
           (block_hint, nth_f)
       in
       (* 2. command/terminator pos *)
       let block =
         match LLVMinfra.lookupBlockViaLabelFromFdef fd block_t' with
         | Some block -> block
         | None -> failwith "propagate block"
       in
       let phivars =
         let LLVMsyntax.Coq_stmts_intro (phinodes, _, _) = block in
         List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
       in
       let hint_elt = oldify_hint_elt phivars hint_elt in
       let block_hint =
         propagate_in_block_hint
           ~phiid_opt:block_prev_opt
           nth_f nth_t'
           hint_elt
           block_hint
       in
       Alist.updateAddAL block_hints block_t' block_hint
  in
  (*{hint with block_hints =*) block_hints(*}*)

(* is_global checks whether a variable is global or not by its name, 
   so it may be incorrect. *)

let is_global x : bool = try x.[0] = '@' with _ -> false

let var2val x xtyp : LLVMsyntax.value = 
  if is_global x
  then LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (xtyp,x))
  else LLVMsyntax.Coq_value_id x

let getVar n args =
  match List.nth args n with
  | ParseHints.AtomVar (pos, lr, v, typ) -> (pos, lr, v, typ)
  | _ -> failwith "getVar"

let getVal n args =
  match List.nth args n with
  | ParseHints.AtomVar (_, _, v, typ) -> var2val v typ
  | ParseHints.AtomIntConst (_, v, typ) ->
    let s = 
      match typ with
      | LLVMsyntax.Coq_typ_int s -> s
      | _ -> failwith "getVal int"
    in
    let api = Llvm.APInt.of_int64 s (Int64.of_int v) true in
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_int (s,api))
  | ParseHints.AtomFpConst (_, v, typ) ->
     let fp =
       match typ with
       | LLVMsyntax.Coq_typ_floatpoint fp -> fp
       | _ -> failwith "getVal fp"
     in
     let ctx = Llvm.global_context () in
     let llvalue = Llvm.const_float (Coq2llvm.translate_floating_point ctx fp) v in
     let apfloat = Llvm.APFloat.const_float_get_value llvalue in
     LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_floatpoint (fp, apfloat))
  | _ -> failwith "getVal"

let getPos n args =
  match List.nth args n with
  | ParseHints.AtomVar (pos, _, _, _) -> pos
  | ParseHints.AtomFpConst (pos, _, _) -> pos
  | ParseHints.AtomIntConst (pos, _, _) -> pos
  | ParseHints.AtomPos (bb, i) -> (bb, i)

let getBlock n args =
  try
    let (bb, _) = getPos n args in
    Some bb
  with
    Failure "nth" -> None

let alist_map f m = List.map (fun (id, x) -> (id, f x)) m
    
let tag_lr lr elt =
  match lr with
  | ParseHints.Original -> Hint_original elt
  | ParseHints.Optimized -> Hint_optimized elt

let propagate_maydiff_in_maydiff id_ext hint =
  let hint = IdExtSetImpl.add id_ext hint in
  hint

let propagate_maydiff_in_insn_hint id_ext hint =
  let hint_maydiff = hint.hint_maydiff in
  let hint_maydiff = propagate_maydiff_in_maydiff id_ext hint_maydiff in
  {hint with hint_maydiff = hint_maydiff}

let propagate_maydiff_in_block_hints id_ext hint =
  alist_map
    (fun hint ->
     let phi_hint =
       alist_map
         (propagate_maydiff_in_insn_hint id_ext)
         hint.phi_hint
     in
     let cmds_hint =
       alist_map
         (List.map (propagate_maydiff_in_insn_hint id_ext))
         hint.cmds_hint
     in
     let term_hint = propagate_maydiff_in_insn_hint id_ext hint.term_hint in
     {phi_hint = phi_hint;
      cmds_hint = cmds_hint;
      term_hint = term_hint})
    hint

let propagate_maydiff_in_fdef_hint id_ext hint =
  let block_hints = hint(*.block_hints*) in
  let block_hints = propagate_maydiff_in_block_hints id_ext block_hints in
  (*{hint with block_hints =*) block_hints(*}*)
