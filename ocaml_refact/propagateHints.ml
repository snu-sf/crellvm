(*********************************)
(* propagate information in hint *)
(*********************************)
(* refactoring *)
open Infrastructure
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
open CoreHint_t
open CoreHintUtil

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

(* scope and object for propagation *)
type scope =
  | Left_scope
  | Right_scope

type propagate_obj =
  | Lessdef_obj of ExprPair.t
  | Noalias_obj of ValueTPair.t
  | Allocas_obj of IdT.t
  | Private_obj of IdT.t

type position_stmt =
  | Phinode of atom
  | After_phinodes
  | Command of int
  | End_pos

type position = atom * position_stmt

let position_lt (p1:position) (p2:position): bool =
  let (bid1, pib1) = p1 in
  let (bid2, pib2) = p2 in
  if bid1 = bid2 then
    match pib2 with
    | Phinode _ -> false
    | Command n2 ->
       (match pib1 with
        | Phinode _ -> true
        | Command n1 -> n1 < n2)
  else false

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

let propagate_in_cmds_hint (nth_f:CoreHint_t.instr_index) (nth_t:CoreHint_t.instr_index) hint_elt hints =
  mapi
    (fun i hint ->
     let hint =
       if (match nth_f with
           | CoreHint_t.Phinode -> true
	   | CoreHint_t.Command nth_f -> nth_f <= i
	   | CoreHint_t.Terminator -> false
	   )
          && (match nth_t with
	      | CoreHint_t.Phinode -> false
	      | CoreHint_t.Command nth_t -> i <= nth_t
	      | CoreHint_t.Terminator -> true
	      )
       then propagate_in_insn_hint hint_elt hint
       else hint
     in
     hint)
    hints

(* propagate equation in a block
   @arg nth_f: from nth instruction
   @arg nth_t: to nth instruction
 *)
let propagate_in_hints_stmts
      (pos_from:position_stmt) (pos_to:position_stmt)
      (prop_obj:propagate_obj)
      (hints_stmts:Hints.stmts)
    : Hints.stmts =
  let hints_stmts =
    if nth_f <> CoreHint_t.Phinode
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
    if nth_t <> CoreHint_t.Terminator
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

(* let oldify_hint_elt (ids:atom list) (elt:hint_elt_t) : hint_elt_t = *)
(*   match elt with *)
(*   | Hint_maydiff _ -> elt *)
(*   | Hint_original elt -> Hint_original (oldify_invariant_elt ids elt) *)
(*   | Hint_optimized elt -> Hint_optimized (oldify_invariant_elt ids elt) *)
(*   | Hint_iso_original _ -> elt *)
(*   | Hint_iso_optimized _ -> elt *)

(* let next_pos pos = *)
(*   match pos with *)
(*   | CoreHint_t.Phinode ->  CoreHint_t.Command 0 *)
(*   | CoreHint_t.Command i -> CoreHint_t.Command (i + 1) *)
(*   | _ -> failwith "PropagateHints.next_pos : (juneyoung lee) we cannot define next position of CoreHint_t.Terminator" *)

let propagate_iso 
      (pos_from : CoreHint_t.position)
      (hint_elt:hint_elt_t)
      (fd:LLVMsyntax.fdef) (hint:fdef_hint_t) (dom_tree:atom coq_DTree)
    : fdef_hint_t =
  let (block_f, nth_f) = (pos_from.block_name, pos_from.instr_index) in
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
          if bid = block_f && (not (AtomSetImpl.mem block_f reachable_to_t))
          then next_pos nth_f
          else CoreHint_t.Phinode
        in
        let nth_t = CoreHint_t.Terminator in
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
      (pos_from:position) (pos_to:position)
      (prop_obj: propagate_obj)
      (fdef:LLVMsyntax.fdef)
      (dom_tree:atom coq_DTree)
      (hints_f:Hints.fdef)
    : Hints.fdef =
  let bid_from = fst pos_from in
  let bid_to = fst pos_to in
  let ((pass_through_t : bool), reachable_to_t) =
    if position_lt pos_from pos_to
    then (false, AtomSetImpl.singleton block_f)
    else
      let dom_by_f = dom_by bid_from dom_tree in
      reachable_to bid_to dom_by_f fdef
  in
  
  let hints_f =
    AtomSetImpl.fold
      (fun bid hints_f ->
        let hints_stmts =
          match Alist.lookupAL hints_f bid with
          | None -> failwith "propagateHints: no bid in hint"
          | Some hs -> hs
        in
        let pos_in_b_from =
          if bid = bid_from
          then (snd pos_from)
          else After_phinodes
        in
        let pos_in_b_to =
          if bid = bid_to && (not pass_through_t)
          then (snd pos_to)
          else End_pos
        in
        let hints_stmts =
          propagate_in_hints_stmts
            pos_in_b_from pos_in_b_to
            prop_obj
            hints_stmts
        in
        Alist.updateAddAL hints_f bid hints_stmts)
      reachable_to_t
      hints_f
  in
  hints_f

let alist_map f m = List.map (fun (id, x) -> (id, f x)) m
                             
let add_variable_to_invariant (idt:IdT.t) (inv:Invariant.t) =
  Invariant.update_maydiff
    (fun idtset -> (IdTSet.add idt idtset))
    inv

let propagate_maydiff_in_hints_fdef (idt:IdT.t) (hint_f:Hints.fdef) =
  alist_map
    (fun hint_stmts ->
      let inv_after_phi_new =
        add_variable_to_invariant
          idt hint_stmts.invariant_after_phinodes
      in
      let cmds_new =
        List.map (fun (infr_l, inv) ->
                   (infr_l, add_variable_to_invariant idt inv))
                 hint_stmts.cmds
      in
      { phinodes = hint_stmts.phinodes;
        invariant_after_phinodes = inv_after_phi_new;
        cmds = cmds_new })
    hint_f
