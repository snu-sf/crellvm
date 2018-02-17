(*********************************)
(* propagate information in hint *)
(*********************************)
(* refactoring *)
open Infrastructure
open Printf
open Llvm
open Arg
open Syntax
open MetatheoryAtom
open Extract_defs
open Dom_list
open Dom_tree
open CoreHint_t
open ConvertUtil
open DomTreeUtil
open Hints
open Exprs

type atom = AtomImpl.atom

(* TODO: need refactoring *)
module Reachable = struct
  (* @arg f: block id
   @arg t: block id
   @arg succ: graph between block ids
   @return: set of block ids
     - reachable from f
     - without passing through t
   *)
  let _filtered (f:atom) (t:atom) (ids:AtomSetImpl.t) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : bool * AtomSetImpl.t =
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
                   if succ = t || AtomSetImpl.mem succ visit || not (AtomSetImpl.mem succ ids)
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
  let _from (f:atom) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : AtomSetImpl.t =
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
  let to_block (f:atom) (t:atom) (ids:AtomSetImpl.t) (fd:LLVMsyntax.fdef) : bool * AtomSetImpl.t =
    if not (AtomSetImpl.mem t ids)
    then (false, AtomSetImpl.empty)
    else
      let is_t_in_ids = AtomSetImpl.mem t ids in
      let predecessors = Cfg.predecessors fd in
      let res = _filtered t f ids predecessors in
      if not is_t_in_ids then (fst res, AtomSetImpl.remove t (snd res)) else res

  (* the set of nodes that is reachable from "f". *)
  let from_block (block_id_from:atom) (fdef:LLVMsyntax.fdef) : AtomSetImpl.t =
    _from block_id_from (Cfg.successors fdef)

  let get_intermediate_block_ids
        (bid_from:atom)
        (bid_to:atom)
        (fdef:LLVMsyntax.fdef)
        (dtree:atom coq_DTree)
      : bool * AtomSetImpl.t =
    let dominated_by_from = dom_by bid_from dtree in
    (* let _ = print_endline ("dom num: "^(string_of_int (AtomSetImpl.cardinal dominated_by_from))) in *)
    (* let _ = print_endline (if (AtomSetImpl.is_empty dominated_by_from) then "empty" else "nonempty") in *)
    let res = to_block bid_from bid_to dominated_by_from fdef in
    (* let _ = print_endline (if (AtomSetImpl.is_empty (snd res)) then "empty2" else "nonempty2") in *)
    (* let _ = print_endline ("res num: "^(string_of_int (AtomSetImpl.cardinal res))) in *)
    res
    (* to_block bid_from bid_to dominated_by_from fdef *)
end

(* object for propagation *)
module AssertionObject = struct
    type scope =
      | Source
      | Target

    type unary =
      | Lessdef of ExprPair.t
      | Noalias of PtrPair.t
      | Diffblock of ValueTPair.t
      | Unique of atom
      | Private of IdT.t

    type t =
      | Unary of scope * unary
      | Maydiff of IdT.t

    let convert_scope (s:CoreHint_t.scope): scope =
      if s = CoreHint_t.Source then Source else Target

    let convert
          (prop_obj:CoreHint_t.propagate_object)
          (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
        : t =
      match prop_obj with
      | CoreHint_t.Lessdef prop_ld ->
         Unary (convert_scope prop_ld.scope,
                Lessdef (Convert.expr prop_ld.lhs lfdef rfdef,
                         Convert.expr prop_ld.rhs lfdef rfdef))
      | CoreHint_t.Noalias prop_na ->
         Unary (convert_scope prop_na.scope,
                Noalias (Convert.pointer prop_na.lhs,
                         Convert.pointer prop_na.rhs))
      | CoreHint_t.Maydiff v ->
         Maydiff (Convert.register v)
      | CoreHint_t.Unique prop_a ->
         Unary (convert_scope prop_a.scope,
                Unique prop_a.register_name)
      | CoreHint_t.Private prop_a ->
         Unary (convert_scope prop_a.scope,
                Private (Convert.register prop_a.p))
      | CoreHint_t.Diffblock prop_a ->
         Unary (convert_scope prop_a.scope,
                Diffblock (Convert.value prop_a.lhs, Convert.value prop_a.rhs))

    let insert (obj:t) (inv:Assertion.t): Assertion.t =
      match obj with
      | Unary (scope, unary_obj) ->
         let update_unary unary =
           match unary_obj with
           | Lessdef expr_pair ->
              Assertion.update_lessdef (ExprPairSet.add expr_pair) unary
           | Noalias (ptr1, ptr2) ->
              Assertion.update_noalias (PtrPairSet.add (ptr1, ptr2)) unary
           | Diffblock (v1, v2) ->
              Assertion.update_diffblock (ValueTPairSet.add (v1, v2)) unary
           | Unique idt ->
              Assertion.update_unique (AtomSetImpl.add idt) unary
           | Private idt ->
              Assertion.update_private (IdTSet.add idt) unary
         in
         (if scope = Source then Assertion.update_src else Assertion.update_tgt)
           update_unary
           inv
      | Maydiff idt ->
         Assertion.update_maydiff (IdTSet.add idt) inv
  end

module PropagateStmts = struct
    let final_idx_from_hint (hint_stmts:ValidationHint.stmts) =
      Position.Command (List.length hint_stmts.ValidationHint.cmds)

    let _proceed
          (idx_from:Position.idx)
          (idx_to:Position.idx)
          (inv_obj:AssertionObject.t)
          (hint_stmts:ValidationHint.stmts)
        : ValidationHint.stmts =
      let inv_after_phi =
        let curr_inv = hint_stmts.ValidationHint.assertion_after_phinodes in
        if Position.idx_le idx_from Position.idx_any_phinode
        then AssertionObject.insert inv_obj curr_inv
        else curr_inv
      in
      let cmds =
        List.mapi
          (fun c_idx (infr_l, curr_inv) ->
           let curr_idx = (Position.Command c_idx) in
           let new_inv =
             if (Position.idx_le idx_from curr_idx)
                && (Position.idx_lt curr_idx idx_to)
             then AssertionObject.insert inv_obj curr_inv
             else curr_inv
           in
           (infr_l, new_inv))
          hint_stmts.ValidationHint.cmds
      in
      { hint_stmts with ValidationHint.assertion_after_phinodes = inv_after_phi;
                        ValidationHint.cmds = cmds;
      }

    let bounds
          (idx_from:Position.idx)
          (idx_to:Position.idx)
          (inv_obj:AssertionObject.t)
          (hint_stmts:ValidationHint.stmts)
        : ValidationHint.stmts =
      if Position.idx_lt idx_from idx_to
      then _proceed idx_from idx_to inv_obj hint_stmts
      else failwith "PropagateStmts.bounds: idx_from >= idx_to"

    let bounds_from
          (idx_from:Position.idx)
          (inv_obj:AssertionObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed idx_from (final_idx_from_hint hint_stmts) inv_obj hint_stmts

    let bounds_to
          (idx_to:Position.idx)
          (inv_obj:AssertionObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed Position.idx_any_phinode idx_to inv_obj hint_stmts

    let global
          (inv_obj:AssertionObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed Position.idx_any_phinode (final_idx_from_hint hint_stmts) inv_obj hint_stmts
  end

let propagate_global
      (assertion:AssertionObject.t)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  TODO.mapAL
    (fun hint_stmts -> PropagateStmts.global assertion hint_stmts)
    hint_fdef

(* return: fst is Global, snd is remaining *)
let filter_global
      (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (hints: (CoreHint_t.hint_command * CoreHint_t.cpp_debug_info) list)
    : AssertionObject.t list *
        (CoreHint_t.hint_command * CoreHint_t.cpp_debug_info) list =
  let f = (fun s i ->
           match (fst i) with
           | CoreHint_t.Propagate { propagate = prop ; propagate_range = CoreHint_t.Global } ->
              let inv_obj = AssertionObject.convert prop lfdef rfdef in
              (inv_obj :: fst s, snd s)
           | _ -> (fst s, i :: snd s)) in
  let (globals, others) = List.fold_left f ([], []) hints in
  (globals, List.rev others) (* to preserve order of "others" *)

let propagate_hint
      (lfdef:LLVMsyntax.fdef)
      (dtree_lfdef:atom coq_DTree)
      (assertion:AssertionObject.t)
      (range:Position.range)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  match range with
  | Position.Bounds (position_from, position_to) ->
     let (bid_from, idx_from) = position_from in
     let (bid_to, idx_to) = position_to in
     let (bid_to, idx_to) =
       match idx_to with
       | Position.Phinode bid_prev ->
          (bid_prev, Position.idx_final bid_prev lfdef)
       | Position.Command _ -> position_to
     in
     if bid_from = bid_to then
       let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
       let hint_stmts = PropagateStmts.bounds idx_from idx_to assertion hint_stmts in
       Alist.updateAL hint_fdef bid_from hint_stmts
     else
       let (to_until_end, interm_bids) =
         Reachable.get_intermediate_block_ids bid_from bid_to lfdef dtree_lfdef
       in
       (* let _ = print_endline ("from: "^bid_from); print_endline ("to: "^bid_to) in *)
       let is_end_in_interm = AtomSetImpl.mem bid_to interm_bids in
       let interm_bids = AtomSetImpl.remove bid_from (AtomSetImpl.remove bid_to interm_bids) in
       
       let hint_stmts_from = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
       let hint_stmts_from = PropagateStmts.bounds_from idx_from assertion hint_stmts_from in
       let hint_stmts_to = TODOCAML.get (Alist.lookupAL hint_fdef bid_to) in
       let hint_stmts_to =
         if not is_end_in_interm then hint_stmts_to
         else (if to_until_end
               then PropagateStmts.global assertion hint_stmts_to
               else PropagateStmts.bounds_to idx_to assertion hint_stmts_to)
       in
       
       let hint_fdef = Alist.updateAL hint_fdef bid_from hint_stmts_from in
       let hint_fdef = Alist.updateAL hint_fdef bid_to hint_stmts_to in
       TODO.mapiAL
         (fun bid hint_stmts ->
          if AtomSetImpl.mem bid interm_bids
          then PropagateStmts.global assertion hint_stmts
          else hint_stmts)
         hint_fdef
  | Position.BoundSet (position_from, position_to_lst) ->
     let (bid_from, idx_from) = position_from in
     let rec remove_dups lst =
       match lst with
       | [] -> []
       | h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t)) in
     let position_to_lst_reduced = remove_dups position_to_lst in
     let position_to_lst_reduced =
       List.map
        (fun (bid_to, idx_to) ->
          match idx_to with
          | Position.Phinode bid_prev ->
             (bid_prev, Position.idx_final bid_prev lfdef)
          | Position.Command _ -> (bid_to, idx_to))
        position_to_lst_reduced in
    let position_to_lst_filtered =
      List.filter
       (fun (bid_to, idx_to) -> bid_to <> bid_from) position_to_lst_reduced in
    if position_to_lst_filtered = []
    then
      List.fold_left
        (fun hint_fdef (bid_to, idx_to) ->
          let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
          let hint_stmts = PropagateStmts.bounds idx_from idx_to assertion hint_stmts in
          Alist.updateAL hint_fdef bid_from hint_stmts)
        hint_fdef position_to_lst_reduced (* TODO: find furthermost idx_to *)
    else
      let hint_fdef =
        List.fold_left
         (fun hint_fdef (bid_to, idx_to) ->
           let (to_until_end, interm_bids) =
             Reachable.get_intermediate_block_ids bid_from bid_to lfdef dtree_lfdef in
           let hint_stmts_from = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
           let hint_stmts_from =
             PropagateStmts.bounds_from idx_from assertion hint_stmts_from in
           let hint_stmts_to = TODOCAML.get (Alist.lookupAL hint_fdef bid_to) in
           let hint_stmts_to =
             if to_until_end
             then PropagateStmts.global assertion hint_stmts_to
             else PropagateStmts.bounds_to idx_to assertion hint_stmts_to
           in
           let hint_fdef = Alist.updateAL hint_fdef bid_from hint_stmts_from in
           let hint_fdef = Alist.updateAL hint_fdef bid_to hint_stmts_to in
           hint_fdef)
         hint_fdef position_to_lst_filtered in
      let interm_bids_lst =
        List.map
         (fun (bid_to, idx_to) ->
           (* TODO: optimize below to prevent caliing same function again *)
           let (to_until_end, interm_bids) =
             Reachable.get_intermediate_block_ids bid_from bid_to lfdef dtree_lfdef in
           AtomSetImpl.remove bid_from (AtomSetImpl.remove bid_to interm_bids))
         position_to_lst_filtered in
      let interm_bids =
        List.fold_left
         (fun interm_bids_set interm_bids_elem ->
           AtomSetImpl.union interm_bids_set interm_bids_elem)
         AtomSetImpl.empty interm_bids_lst in
      TODO.mapiAL
        (fun bid hint_stmts ->
          if AtomSetImpl.mem bid interm_bids
          then PropagateStmts.global assertion hint_stmts
          else hint_stmts)
        hint_fdef
  | Position.Global ->
     propagate_global assertion hint_fdef
