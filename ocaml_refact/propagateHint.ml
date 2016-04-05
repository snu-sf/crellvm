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
    type scope =
      | Source
      | Target

    type unary =
      | Lessdef of ExprPair.t
      | Noalias of PtrPair.t
      | Allocas of Ptr.t
      | Private of IdT.t

    type t =
      | Unary of scope * unary
      | Maydiff of IdT.t

    let convert_scope (s:CoreHint_t.scope): scope =
      if s = CoreHint_t.Source then Source else Target

(*  let convert_expr
          (expr:CoreHint_t.expr)
          (lfdef:LLVMsyntax.fdef)
          (rfdef:LLVMsyntax.fdef)
        : Expr.t =
      Convert.expr expr lfdef rfdef
      match expr with
      | CoreHint_t.Var (register:CoreHint_t.register) ->
         Expr.Coq_value (ValueT.Coq_id (Convert.register register))
      | CoreHint_t.Rhs ((register:CoreHint_t.register), (scope:CoreHint_t.scope)) ->
         (match scope with
          | CoreHint_t.Source -> Convert.rhs_of register lfdef
          | CoreHint_t.Target -> Convert.rhs_of register rfdef)
      | CoreHint_t.Const (c:CoreHint_t.constant) ->
         failwith "TODO: convert_expr of const not supported yet"*)

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
                Noalias (Convert.pointer prop_na.lhs lfdef,
                         Convert.pointer prop_na.rhs lfdef))
      | CoreHint_t.Maydiff v ->
         Maydiff (Convert.register v)
      | CoreHint_t.Alloca prop_a ->
         Unary (convert_scope prop_a.scope,
                Allocas (Convert.pointer prop_a.p lfdef))

    let insert (obj:t) (inv:Invariant.t): Invariant.t =
      match obj with
      | Unary (scope, unary_obj) ->
         let update_unary unary =
           match unary_obj with
           | Lessdef expr_pair ->
              Invariant.update_lessdef (ExprPairSet.add expr_pair) unary
           | Noalias (ptr1, ptr2) ->
              Invariant.update_noalias (PtrPairSet.add (ptr1, ptr2)) unary
           | Allocas ptr ->
              Invariant.update_allocas (PtrSet.add ptr) unary
           | Private idt ->
              Invariant.update_private (IdTSet.add idt) unary
         in
         (if scope = Source then Invariant.update_src else Invariant.update_tgt)
           update_unary
           inv
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
        if Position.idx_le idx_from Position.idx_any_phinode
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
      _proceed Position.idx_any_phinode idx_to inv_obj hint_stmts

    let global
          (inv_obj:InvariantObject.t)
          (hint_stmts:ValidationHint.stmts)
        :ValidationHint.stmts =
      _proceed Position.idx_any_phinode (final_idx_from_hint hint_stmts) inv_obj hint_stmts
  end

let propagate_global
      (invariant:InvariantObject.t)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  TODO.mapAL
    (fun hint_stmts -> PropagateStmts.global invariant hint_stmts)
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
     let (bid_to, idx_to) = position_to in
     let (bid_to, idx_to) =
       match idx_to with
       | Position.Phinode bid_prev ->
          (bid_prev, Position.idx_final bid_prev lfdef)
       | Position.Command _ -> position_to
     in
     if bid_from = bid_to then
       let hint_stmts = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
       let hint_stmts = PropagateStmts.bounds idx_from idx_to invariant hint_stmts in
       Alist.updateAL hint_fdef bid_from hint_stmts
     else
       let (to_until_end, interm_bids) =
         Reachable.get_intermediate_block_ids bid_from bid_to lfdef dtree_lfdef
       in
       let interm_bids = AtomSetImpl.remove bid_from (AtomSetImpl.remove bid_to interm_bids) in
       
       let hint_stmts_from = TODOCAML.get (Alist.lookupAL hint_fdef bid_from) in
       let hint_stmts_from = PropagateStmts.bounds_from idx_from invariant hint_stmts_from in
       let hint_stmts_to = TODOCAML.get (Alist.lookupAL hint_fdef bid_to) in
       let hint_stmts_to =
         if to_until_end
         then PropagateStmts.global invariant hint_stmts_to
         else PropagateStmts.bounds_to idx_to invariant hint_stmts_to
       in
       
       let hint_fdef = Alist.updateAL hint_fdef bid_from hint_stmts_from in
       let hint_fdef = Alist.updateAL hint_fdef bid_to hint_stmts_to in
       TODO.mapiAL
         (fun bid hint_stmts ->
          if AtomSetImpl.mem bid interm_bids
          then PropagateStmts.global invariant hint_stmts
          else hint_stmts)
         hint_fdef
  | Position.Global ->
     propagate_global invariant hint_fdef
