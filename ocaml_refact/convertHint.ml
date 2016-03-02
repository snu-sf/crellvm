open Infrastructure
open Printf
open Llvm
open Arg
open Syntax
open MetatheoryAtom
open Dom_list
open Dom_tree
open Maps
open LLVMsyntax
open CoreHint_t
open ConvertUtil
open PropagateHint
open ConvertInfrule
open Hints
open Exprs
open AddInfrule

type atom = AtomImpl.atom

(* TODO(@youngju.song): in Coq *)
let generate_nop (core_hint:CoreHint_t.hints) : int list =
  failwith "TODO"

let insert_nop (m:LLVMsyntax.coq_module) (nops:int list) : LLVMsyntax.coq_module =
  failwith "TODO"


module EmptyHint = struct
  (* TODO(@youngju.song): in Coq *)
  let unary_hint : Invariant.unary =
    { Invariant.lessdef = ExprPairSet.empty;
      Invariant.noalias = ValueTPairSet.empty;
      Invariant.allocas = IdTSet.empty;
      Invariant.coq_private = IdTSet.empty;
    }

  let invariant_hint : Invariant.t =
    { Invariant.src = unary_hint;
      Invariant.tgt = unary_hint;
      Invariant.maydiff = IdTSet.empty;
    }

  let stmts_hint (stmts: LLVMsyntax.stmts) : ValidationHint.stmts =
    let Coq_stmts_intro (phinodes, cmds, _) = stmts in

    let incoming_blocks =
      match phinodes with
      | [] -> []
      | (LLVMsyntax.Coq_insn_phi (_, _, vls))::_ -> List.map snd vls
    in
    let phinodes = List.map (fun bid -> (bid, [])) incoming_blocks in

    let cmds = List.map (fun _ -> ([], invariant_hint)) cmds in

    { ValidationHint.phinodes = phinodes;
      ValidationHint.invariant_after_phinodes = invariant_hint;
      ValidationHint.cmds = cmds;
    }

  let fdef_hint (fdef:LLVMsyntax.fdef) : ValidationHint.fdef =
    let Coq_fdef_intro (Coq_fheader_intro (_, _, id, _, _), blks) = fdef in
    List.map (fun (bid, bstmts) -> (bid, stmts_hint bstmts)) blks

  let module_hint (m:LLVMsyntax.coq_module) : ValidationHint.coq_module =
    let Coq_module_intro (lo, nts, prods) = m in
    TODOCAML.filter_map
      (fun prod ->
        match prod with
        | LLVMsyntax.Coq_product_fdef fd -> Some (LLVMinfra.getFdefID fd, fdef_hint fd)
        | _ -> None)
      prods
end

let noret (hint_module:ValidationHint.coq_module) : ValidationHint.coq_module =
  failwith "TODO: don't know yet"

(** execute corehint commands **)

let apply_corehint_command
      (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (dtree_lfdef:LLVMsyntax.l coq_DTree)
      (command:CoreHint_t.command)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  match command with
  | CoreHint_t.Propagate prop ->
     let invariant = PropagateHint.convert_propagate_object prop.propagate lfdef rfdef in
     let range = Position.convert_range prop.propagate_range lfdef rfdef in
     propagate_hint lfdef dtree_lfdef invariant range hint_fdef
  | CoreHint_t.Infrule (pos, infrule) ->
     let pos = Position.convert pos lfdef rfdef in
     let infrule = convert_infrule infrule in
     add_infrule pos infrule hint_fdef

let convert
      (lm:LLVMsyntax.coq_module)
      (rm:LLVMsyntax.coq_module)
      (core_hint:CoreHint_t.hints)
    : ValidationHint.coq_module =

  let fid = core_hint.function_id in
  let lfdef = TODOCAML.get (LLVMinfra.lookupFdefViaIDFromModule lm fid) in
  let rfdef = TODOCAML.get (LLVMinfra.lookupFdefViaIDFromModule rm fid) in
  let dtree_lfdef = TODOCAML.get (AlgDom.create_dom_tree lfdef) in

  let hint_fdef = EmptyHint.fdef_hint lfdef in
  let hint_fdef = List.fold_left
                    (TODOCAML.flip (apply_corehint_command lfdef rfdef dtree_lfdef))
                    hint_fdef core_hint.commands
  in

  let hint_module = EmptyHint.module_hint lm in
  let hint_module = noret hint_module in
  let hint_module = Alist.updateAL hint_module fid hint_fdef in
  hint_module