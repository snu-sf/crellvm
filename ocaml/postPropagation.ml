(*********************************)
(* Post-propagation mechanisms   *)
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
open ValueT
open IdT
open Tag
open TODOCAML
open Printer

module PostProp = struct
    type t = Invariant.t -> Invariant.t -> Invariant.t option

    let counter:int ref = ref 0

    let update_lessdef_b (f:ExprPairSet.t -> (ExprPairSet.t * bool)) (invu:Invariant.unary)
        : Invariant.unary * bool =
      let (ld_post, flag) = f invu.Invariant.lessdef in
      (Invariant.update_lessdef (fun _ -> ld_post) invu, flag)

    let update_src_b (f:Invariant.unary -> (Invariant.unary * bool)) (inv:Invariant.t)
        : Invariant.t * bool =
      let (inv_src, flag) = f inv.Invariant.src in
      (Invariant.update_src (fun _ -> inv_src) inv, flag)

    let update_tgt_b (f:Invariant.unary -> (Invariant.unary * bool)) (inv:Invariant.t)
        : Invariant.t * bool =
      let (inv_tgt, flag) = f inv.Invariant.tgt in
      (Invariant.update_tgt (fun _ -> inv_tgt) inv, flag)

    let remove_inconsistent_gep (previnv:Invariant.t) (postinv:Invariant.t) =
      let rem_inc_ld (prev_ld:ExprPairSet.t) (post_ld:ExprPairSet.t) : (ExprPairSet.t * bool) =
        List.fold_left (fun (acc, cg) ep ->
                        match ep with
                        | (e1, Expr.Coq_gep (inb, ty1, v, lsz, ty2)) when inb = true ->
                           if ExprPairSet.mem (e1, Expr.Coq_gep (false, ty1, v, lsz, ty2)) prev_ld
                           then (ExprPairSet.remove ep acc, true)
                           else (acc, cg)
                        | (Expr.Coq_gep (inb, ty1, v, lsz, ty2), e2) when inb = false ->
                           if ExprPairSet.mem (Expr.Coq_gep (true, ty1, v, lsz, ty2), e2) prev_ld
                           then (ExprPairSet.remove ep acc, true)
                           else (acc, cg)
                        | _ -> (acc, cg)) (post_ld, false) (ExprPairSet.elements post_ld)
      in
      let _ = counter := !counter + 1 in
      let prev_ld_src = previnv.Invariant.src.Invariant.lessdef in
      let prev_ld_tgt = previnv.Invariant.tgt.Invariant.lessdef in
      let (postinv1, cg1) = update_src_b (update_lessdef_b (rem_inc_ld prev_ld_src)) postinv in
      let (postinv2, cg2) = update_tgt_b (update_lessdef_b (rem_inc_ld prev_ld_tgt)) postinv1 in
      if (cg1 || cg2) then Some postinv2 else None

    let default (previnv:Invariant.t) (postinv:Invariant.t) = None
  end

let _apply_func_to_block (hint_fdef:ValidationHint.fdef)
        (func: PostProp.t)
        (blockid: atom)
        (preds: atom list)
        : (ValidationHint.fdef * bool) (* updated invariants, ischanged *) =
  let stmtsinv: ValidationHint.stmts = TODOCAML.get (Alist.lookupAL hint_fdef blockid) in
  (* First, update invariant_after_phinodes *)
  let (stmtsinv, changed_phiinv): (ValidationHint.stmts * bool) = 
      List.fold_left
        (* return updated stmtsinv *)
        (fun ((stmtsinv, changed):(ValidationHint.stmts * bool)) prevblockid ->
            (* invariant of the previous block *)
            let prev_stmtsinv = TODOCAML.get (Alist.lookupAL hint_fdef prevblockid) in
            let prev_inv =
                (match (List.rev prev_stmtsinv.cmds) with
                 | (_, prev_lastinv)::_ -> prev_lastinv
                 | [] -> (* cmds invariant is empty! *)
                    prev_stmtsinv.invariant_after_phinodes) in
            let this_inv = stmtsinv.invariant_after_phinodes in

            let updated_phiinv_option = func prev_inv this_inv in
            match updated_phiinv_option with
            | Some updated_phiinv ->
                (ValidationHint.update_invariant_after_phinodes
                    (fun _ -> updated_phiinv) stmtsinv, true)
            | None -> (stmtsinv, changed)
        )
        (stmtsinv, false)
        preds (* previous block id *)
  in
  (* invariant_after_phinode is fully updatd. *)
  (* Now update cmds. *)
  let changed_cmdinv: bool ref = ref false in
  let cmdinv_updater =
      let _func_applier prev_inv this_inv = 
          match (func prev_inv this_inv) with
          | Some new_inv ->
              changed_cmdinv := true;
              new_inv
          | None -> this_inv
      in
      (fun (invlist:Invariant.t list) ->
          (* Now fold! *)
          let newinvlist = List.fold_left
              (fun prev_invs this_inv ->
                  match prev_invs with
                  | prev_inv::td ->
                      (_func_applier prev_inv this_inv)::prev_inv::td
                  | [] -> 
                      let phiinv = (stmtsinv.invariant_after_phinodes) in
                      [_func_applier phiinv this_inv]
              )
              []
              invlist
          in List.rev newinvlist
      ) in
  let stmtsinv = ValidationHint.update_cmd_invariants cmdinv_updater stmtsinv in
  (Alist.updateAL hint_fdef blockid stmtsinv, (changed_phiinv || !changed_cmdinv))

let _apply_func_to_f (hint_fdef:ValidationHint.fdef) (lfdef: LLVMsyntax.fdef)
        (dtree_lfdef: atom coq_DTree) 
        (func: PostProp.t)
        : (ValidationHint.fdef * bool) (* updated invariant, ischanged *) =
  let visitorder = bfs_traversal_of_tree dtree_lfdef in
  let _ = print_string "\n" in
  let preds = Cfg.predecessors lfdef in (* LLVMsyntax.ls ATree.t *)
  List.fold_left
      (fun (hint_fdef, changed) blockid ->
          let predlist = 
            match Maps_ext.ATree.get blockid preds with
            | Some t -> t
            | None -> []
          in
          let (hint_fdef, changed2) = _apply_func_to_block hint_fdef func blockid predlist in
          (hint_fdef, (changed || changed2))
      )
      (hint_fdef, false)
      visitorder

let update (hint_fdef:ValidationHint.fdef) (lfdef:LLVMsyntax.fdef)
        (dtree_lfdef: atom coq_DTree)
        (func: PostProp.t) (itrcnt: int)
        : ValidationHint.fdef =
  let rec _update (hint_fdef:ValidationHint.fdef) (n:int) : ValidationHint.fdef =
    if n <= 0 then hint_fdef
    else
      let (hint_fdef, changed) = _apply_func_to_f hint_fdef lfdef dtree_lfdef func in
      if not changed then
        hint_fdef
      else
        _update hint_fdef (n - 1)
  in _update hint_fdef itrcnt
