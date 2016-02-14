open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open MicroHints
open CommandArg
open Vars_aux
open Validator_aux
open Dom_list
open Dom_tree
open Maps
open CoreHint_t

type atom = AtomSetImpl.t

let is_parent_terminator (t:LLVMsyntax.terminator) (bb:LLVMsyntax.l) : bool =
  match t with
  | LLVMsyntax.Coq_insn_br (_,_,l1,l2) -> l1=bb || l2=bb
  | LLVMsyntax.Coq_insn_br_uncond (_,l1) -> l1=bb
  | _ -> false

let is_parent (blk:LLVMsyntax.block) (bb:LLVMsyntax.l) : bool =
  let LLVMsyntax.Coq_stmts_intro (_,_,t) = snd blk in
  is_parent_terminator t bb

let get_parent_bbs_blocks (blks:LLVMsyntax.block list) (bb:LLVMsyntax.l) : LLVMsyntax.l list =
  List.map (fun blk -> fst blk) (List.filter (fun blk -> is_parent blk bb) blks)

let get_parent_bbs (fdef:LLVMsyntax.fdef) (bb:LLVMsyntax.l) : LLVMsyntax.l list =
  let LLVMsyntax.Coq_fdef_intro (_,blks) = fdef in
  match blks with
  | hd::_ ->
     if fst hd == bb
     then [""]
     else get_parent_bbs_blocks blks bb
  | [] -> []

(***********************)
(* generate empty hint *)
(***********************)

let string_of_one_noop noop =
  "bb=" ^ noop.bb_noop
  ^ "|idx=" ^ (string_of_int noop.idx_noop)

let string_of_noop noop = CoreHintUtil.string_of_list_endline string_of_one_noop noop

let string_of_product_noop noop = CoreHintUtil.string_of_alist_endline string_of_noop noop

let rec empty_hint_system (s:LLVMsyntax.system) (noop:products_noop_t)
        : modules_hint_t =
  List.fold_left
    (fun mhints modu -> (empty_hint_module modu noop)::mhints)
    []
    s


and empty_hint_module (m:LLVMsyntax.coq_module) (noop:products_noop_t)
    : products_hint_t =
  match m with
  | LLVMsyntax.Coq_module_intro (_, _, products) -> (
	  List.fold_left
	    (fun phints prd ->
	     match prd with
	     | LLVMsyntax.Coq_product_gvar _ -> phints
	     | LLVMsyntax.Coq_product_fdec _ -> phints
	     | LLVMsyntax.Coq_product_fdef fdef -> (empty_hint_fdef fdef noop)::phints
	    )
	    []
	    products
  )

and empty_hint_fdef (fdef:LLVMsyntax.fdef) (noop:products_noop_t)
    : (MetatheoryAtom.AtomImpl.atom * fdef_hint_t) =
  match fdef with
  | LLVMsyntax.Coq_fdef_intro (fhead, blks) -> (
	  match fhead with
	  | LLVMsyntax.Coq_fheader_intro (_, _, atom, _, _) ->
       let noop_f = get_noop_by_fname atom noop in
	     let blks_hint =
		     List.fold_left
			     (fun bhints blk ->
            let bb = fst blk in
            let parent_bbs = get_parent_bbs fdef bb in
            (bb,(empty_hint_block blk noop_f parent_bbs))::bhints
           )
			     []
			     blks
	     in
		   (atom, blks_hint))

and empty_hint_block (blk:LLVMsyntax.block) (noop:noop_t) (parent_bbs:LLVMsyntax.l list)
    : block_hint_t =
  let (bb, statements) = blk in
  let noop = get_noop_by_bb bb noop in
  match statements with
  | LLVMsyntax.Coq_stmts_intro (phinodes, commands, _) -> (
    let phivars =
      List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
    in
    let phi_hint prev_bb =
      let infrules =
        List.map
          (fun (LLVMsyntax.Coq_insn_phi (var, _, values)) ->
           let var_ext = (var, Coq_ntag_new) in
           let values =
             List.filter
               (fun (value, bb) -> prev_bb = bb)
               values
           in
           let value =
             match values with
             | (value, _)::_ -> value
             | nil -> failwith "empty_hint_block no such prev_bb"
           in
           let value_ext = add_ntag_value value in
           Coq_rule_remove_maydiff (var_ext, Coq_rhs_ext_value (oldify_value_ext phivars value_ext)))
          phinodes
      in
      {empty_hint_insn with hint_infrules = infrules}
    in
	  let cmds_hint_one =
      [empty_hint_insn]
      @(List.map (fun _ -> empty_hint_insn) commands)
      @(List.map (fun _ -> empty_hint_insn) noop)
	  in
    let phi_hint = List.map (fun bb -> (bb,phi_hint bb)) parent_bbs in
    let cmds_hint = List.map (fun bb -> (bb,cmds_hint_one)) parent_bbs in
	  {
	    phi_hint = phi_hint;
	    cmds_hint = cmds_hint;
	    term_hint = empty_hint_insn
	  }
	)

and empty_hint_eqs : eqs_t = {
  eqs_eq_reg = EqRegSetImpl.empty;
  eqs_eq_heap = EqHeapSetImpl.empty;
  eqs_neq_reg = NeqRegSetImpl.empty
}

and empty_hint_maydiff : maydiff_t = IdExtSetImpl.empty

and empty_iso : isolated_t = IdExtSetImpl.empty

and empty_hint_insn : insn_hint_t =
  {hint_maydiff = empty_hint_maydiff;
   hint_invariant = {
     invariant_original = empty_hint_eqs;
     invariant_optimized = empty_hint_eqs;
     iso_original = empty_iso;
     iso_optimized = empty_iso;
   };
   hint_infrules = []
  }

(********)
(* main *)
(********)


let generate_noop_from_corehint (fid : string) (hint:CoreHint_t.hints) : products_noop_t * products_noop_t =
  let _convert_to_one_noop_t (itm:CoreHint_t.position) : Syntax_ext.one_noop_t =
    let bb = itm.block_name in
    let idx = (match itm.instr_index with
      | CoreHint_t.Phinode -> failwith "_convert_to_products_noop_t : Unexpected case : Erasing phinode.."
      | CoreHint_t.Terminator -> failwith "_convert_to_products_noop_t : Unexpected case : Erasing terminator.."
      | CoreHint_t.Command idx -> idx) in
    let new_noop = {bb_noop = bb; idx_noop = idx} in
    new_noop
  in
  let _accumulate_products_noop_t (itms:products_noop_t) (newitm_pos:CoreHint_t.position) : products_noop_t = 
    let newitm = _convert_to_one_noop_t newitm_pos in
    let bb = newitm.bb_noop in
    let new_noop = (get_noop_by_fname fid itms) @ [newitm] in
    let new_pnoop = Alist.updateAddAL itms fid new_noop in
    new_pnoop
  in
  ((List.fold_left _accumulate_products_noop_t [] hint.added_instr_positions),
  (List.fold_left _accumulate_products_noop_t [] hint.removed_instr_positions))

(* Returns micro hints list that should be added by the noret
   attribute. *)
let noret_maydiff_cmd (c: LLVMsyntax.cmd) : string option =
  match c with
  | LLVMsyntax.Coq_insn_call (x,nrt,_,_,_,_,_) -> if nrt then Some x else None
  | _ -> None

let noret_maydiff_cmds (cs: LLVMsyntax.cmds) : string list =
  List.fold_left
    (fun acc c ->
      match noret_maydiff_cmd c with
      | Some x -> x :: acc
      | None -> acc
    )
    [] cs

let noret_maydiff_stmts (stmts: LLVMsyntax.stmts) : string list =
  match stmts with
  | LLVMsyntax.Coq_stmts_intro (_,cs,_) -> noret_maydiff_cmds cs

let noret_maydiff_block (blk: LLVMsyntax.block) : string list =
  noret_maydiff_stmts (snd blk)

let noret_maydiff_blocks (blks: LLVMsyntax.blocks) : string list =
  List.fold_left (fun acc blk -> (noret_maydiff_block blk) @ acc) [] blks

let noret_maydiff_products (ps: LLVMsyntax.products) (f:string) : string list =
  let rec get_blks (ps: LLVMsyntax.products) (f:string) : LLVMsyntax.blocks option =
    match ps with
    | [] -> None
    | LLVMsyntax.Coq_product_fdef
        (LLVMsyntax.Coq_fdef_intro
           (LLVMsyntax.Coq_fheader_intro (_,_,g,_,_),blks))::_
        when f = g -> Some blks
    | _::tl -> get_blks tl f
  in
  match get_blks ps f with
  | Some blks -> noret_maydiff_blocks blks
  | None -> []

let noret_maydiff (m:LLVMsyntax.coq_module) (f:string) : string list =
  match m with
  | LLVMsyntax.Coq_module_intro (_,_,ps) -> noret_maydiff_products ps f

let translate_corehint_to_hint
      (lm:LLVMsyntax.coq_module) (rm:LLVMsyntax.coq_module)
      (raw_hint:CoreHint_t.hints)
    : products_hint_t * products_noop_t * products_noop_t =
  let fid = raw_hint.function_id in
  let (lpnoop, rpnoop) = generate_noop_from_corehint raw_hint.function_id raw_hint in
  let lnoop = get_noop_by_fname fid lpnoop in
  let rnoop = get_noop_by_fname fid rpnoop in
  let module_hint = empty_hint_module lm lpnoop in
  (* add maydiff globals by noret call *)
  let module_hint =
    List.map
      (fun (f,fdef_hint) ->
        let fdef_hint =
          List.fold_left
            (fun fdef_hint x ->
              let fdef_hint = PropagateHints.propagate_maydiff_in_fdef_hint (x, Coq_ntag_old) fdef_hint in
              let fdef_hint = PropagateHints.propagate_maydiff_in_fdef_hint (x, Coq_ntag_new) fdef_hint in
              fdef_hint)
            fdef_hint (noret_maydiff lm f)
        in
        (f,fdef_hint)
      )
      module_hint
  in

  let (fdef_hint, lfdef, rfdef) =
    match Alist.lookupAL module_hint fid,
          LLVMinfra.lookupFdefViaIDFromModule lm fid,
          LLVMinfra.lookupFdefViaIDFromModule rm fid
    with
    | Some fdef_hint, Some lfdef, Some rfdef -> (fdef_hint, lfdef, rfdef)
    | p1, p2, p3 ->
    Printf.printf "translate_corehint_to_hint : fid : %s %d %d %d\n%!" fid
      (match p1 with | None -> 0 | _ -> 1) (match p2 with | None -> 0 | _ -> 1) (match p3 with | None -> 0 | _ -> 1);
    failwith ("translate_corehint_to_hint : fid : " ^ fid)
  in

  let dom_tree =
    match AlgDom.create_dom_tree lfdef with
    | None -> failwith "translateHints create_dom_tree"
    | Some dom_tree -> dom_tree
  in

  let apply_micro (raw_hint:CoreHint_t.command) fdef_hint =
    let options : CommandArg.microhint_args = {
      lfdef = lfdef;
      lnoop = lnoop;
      rfdef = rfdef;
      rnoop = rnoop;
      left_m = lm;
      right_m = rm;
      fdef_hint = fdef_hint;
      dom_tree = dom_tree
    } in
    let fdef_hint = propagate_micro raw_hint options (*lfdef lnoop rfdef rnoop lm rm fdef_hint dom_tree*) in
    fdef_hint
  in

  let (propagating_micros, infrule_micros)(*:CoreHint_t.command list * CoreHint_t.command list*) =
    List.partition
      (fun (x:CoreHint_t.command) ->
      match x with
      | CoreHint_t.Propagate _ -> true
      | _ -> false) raw_hint.commands
  in
  let fdef_hint =
    List.fold_left
      (fun hint raw_hint ->
       apply_micro raw_hint hint)
      fdef_hint
      propagating_micros
  in
  let fdef_hint =
    List.fold_left
      (fun hint (raw_hint:CoreHint_t.command) ->
       let result = apply_micro raw_hint hint in
       result)
      fdef_hint
      infrule_micros
  in
  let module_hint = Alist.updateAL module_hint fid fdef_hint in
  (module_hint, lpnoop, rpnoop)