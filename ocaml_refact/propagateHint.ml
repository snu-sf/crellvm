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
open Extraction_defs
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
  let _filtered (f:atom) (ids:AtomSetImpl.t) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : bool * AtomSetImpl.t =
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
                   if AtomSetImpl.mem succ visit || not (AtomSetImpl.mem succ ids)
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
  let to_block (t:atom) (ids:AtomSetImpl.t) (fd:LLVMsyntax.fdef) : bool * AtomSetImpl.t =
        if not (AtomSetImpl.mem t ids)
        then (false, AtomSetImpl.empty)
        else
          let predecessors = Cfg.predecessors fd in
          _filtered t ids predecessors

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
    to_block bid_to dominated_by_from fdef
end
(* object for propagation *)

module InvariantObject = struct
    type unary_scope =
      | Src
      | Tgt

    type unary_object =
      | Lessdef of ExprPair.t
      | Noalias of IdT.t * IdT.t
      | Allocas of IdT.t
      | Private of IdT.t

    type t =
      | Unary of unary_scope * unary_object
      | Maydiff of IdT.t

    let convert_scope (s:CoreHint_t.scope): unary_scope =
      if s = CoreHint_t.Source then Src else Tgt

    let convert_propagate_expr_to_Expr
          (prop_expr:CoreHint_t.propagate_expr)
          (fdef:LLVMsyntax.fdef)
        : Expr.t =
      match prop_expr with
      | CoreHint_t.Var (var:CoreHint_t.variable) ->
         Expr.Coq_value (ValueT.Coq_id (Convert.variable var))
      | CoreHint_t.Rhs (var:CoreHint_t.variable) ->
         Convert.rhs_of var fdef
      | CoreHint_t.Const (c:CoreHint_t.constant) ->
         failwith "TODO: not supported yet"

    let convert_propagate_object
          (c_prop_obj:CoreHint_t.propagate_object)
          (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
        : t =
      match c_prop_obj with
      | CoreHint_t.Lessdef prop_ld ->
         let fdef = if prop_ld.scope = CoreHint_t.Source then lfdef else rfdef in
         Unary (convert_scope prop_ld.scope,
                Lessdef (convert_propagate_expr_to_Expr prop_ld.lhs fdef,
                         convert_propagate_expr_to_Expr prop_ld.rhs fdef))
      | CoreHint_t.Noalias prop_na ->
         Unary (convert_scope prop_na.scope,
                Noalias (Convert.variable prop_na.lhs,
                         Convert.variable prop_na.rhs))
      | CoreHint_t.Maydiff v ->
         Maydiff (Convert.variable v)

    let insert (obj:t) (inv:Invariant.t): Invariant.t =
      match obj with
      | Unary (scope, unary_obj) ->
         let update_unary unary =
           match unary_obj with
           | Lessdef expr_pair ->
              Invariant.update_lessdef (ExprPairSet.add expr_pair) unary
           | Noalias (idt1, idt2) ->
              Invariant.update_noalias (ValueTPairSet.add (ValueT.Coq_id idt1, ValueT.Coq_id idt2)) unary
           | Allocas idt ->
              Invariant.update_allocas (IdTSet.add idt) unary
           | Private idt ->
              Invariant.update_private (IdTSet.add idt) unary
         in
         if scope = Src then
           Invariant.update_src update_unary inv
         else
           Invariant.update_tgt update_unary inv
      | Maydiff idt ->
         Invariant.update_maydiff (IdTSet.add idt) inv

  end

module PropagateStmts = struct
    let final_idx_from_hint (hint_stmts:ValidationHint.stmts) =
      Position.Command (List.length hint_stmts.ValidationHint.cmds)

    let _proceed
          (idx_from:Position.idx)
          (idx_to:Position.idx)
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        : ValidationHint.stmts =
      let inv_after_phi =
        let curr_inv = hint_stmts.ValidationHint.invariant_after_phinodes in
        if Position.idx_le idx_from Position.any_phinode_idx
        then InvariantObject.insert inv_obj curr_inv
        else curr_inv
      in
      let cmds =
        List.mapi
          (fun c_idx (infr_l, curr_inv) ->
           let curr_idx = (Position.Command c_idx) in
           let new_inv =
             if (Position.idx_le idx_from curr_idx)
                && (Position.idx_lt curr_idx idx_to)
             then InvariantObject.insert inv_obj curr_inv
             else curr_inv
           in
           (infr_l, new_inv))
          hint_stmts.ValidationHint.cmds
      in
      { hint_stmts with ValidationHint.invariant_after_phinodes = inv_after_phi;
                        ValidationHint.cmds = cmds;
      }

    let bounds
          (idx_from:Position.idx)
          (idx_to:Position.idx)
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        : ValidationHint.stmts =
      if Position.idx_lt idx_from idx_to
      then _proceed idx_from idx_to inv_obj hint_stmts
      else failwith "PropagateStmts.bounds: idx_from >= idx_to"

    let bounds_from
          (idx_from:Position.idx)
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed idx_from (final_idx_from_hint hint_stmts) inv_obj hint_stmts

    let bounds_to
          (idx_to:Position.idx)
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed Position.any_phinode_idx idx_to inv_obj hint_stmts

    let global
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed Position.any_phinode_idx (final_idx_from_hint hint_stmts) inv_obj hint_stmts
  end

let propagate_global
      (invariant:InvariantObject.t)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  List.map
    (fun (l, hint_stmts) ->
     (l, PropagateStmts.global invariant hint_stmts))
    hint_fdef

let propagate_hint
      (lfdef:LLVMsyntax.fdef)
      (dtree_lfdef:atom coq_DTree)
      (invariant:InvariantObject.t)
      (range:Position.range)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  match range with
  | Position.Bounds (position_from, position_to) ->
     let (bid_from, idx_from) = position_from in
     let (bid_to_orig, idx_to_orig) = position_to in
     let (bid_to, idx_to) =
       match idx_to_orig with
       | Position.Phinode bid_prev ->
          (bid_prev, Position.final_idx bid_prev lfdef)
       | Position.Command _ -> position_to
     in
     if bid_from = bid_to then
       let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
       let hint_stmts =
         PropagateStmts.bounds idx_from idx_to invariant hint_stmts
       in
       Alist.updateAL hint_fdef bid_from hint_stmts
     else
       let (to_until_end, interm_bids) =
         Reachable.get_intermediate_block_ids bid_from bid_to lfdef dtree_lfdef
       in
       let interm_bids = AtomSetImpl.remove bid_from (AtomSetImpl.remove bid_to interm_bids) in

       let hint_stmts_from =
         let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
         PropagateStmts.bounds_from idx_from invariant hint_stmts
       in
       let hint_stmts_to =
         let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_to) in
         if to_until_end
         then PropagateStmts.global invariant hint_stmts
         else PropagateStmts.bounds_to idx_to invariant hint_stmts
       in

       let hint_fdef = Alist.updateAL hint_fdef bid_from hint_stmts_from in
       let hint_fdef = Alist.updateAL hint_fdef bid_to hint_stmts_to in
       List.map
         (fun (bid, hint_stmts) ->
          if AtomSetImpl.mem bid interm_bids
          then (bid, PropagateStmts.global invariant hint_stmts)
          else (bid, hint_stmts))
         hint_fdef
  | Position.Global ->
     propagate_global invariant hint_fdef
