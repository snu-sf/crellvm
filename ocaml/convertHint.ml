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

let rec nat_of_int n =
  assert (n >= 0);
  if n = 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let nop_position_atd_to_coq (x : CoreHint_t.position) : Nop.nop_position =
  let nop_pos_i =
    match x.CoreHint_t.instr_index with
    | CoreHint_t.Phinode _ -> Nop.Coq_phi_node
    | CoreHint_t.Command pc -> Nop.Coq_command_index (nat_of_int pc.CoreHint_t.index)
  in
  (x.CoreHint_t.block_name, nop_pos_i)

let sort_nop nops =
  List.sort (fun p1 p2 ->
             match p1.CoreHint_t.instr_index, p2.CoreHint_t.instr_index with
             | CoreHint_t.Phinode _, CoreHint_t.Phinode _ -> 0
             | CoreHint_t.Phinode _, CoreHint_t.Command _ -> (-1)
             | CoreHint_t.Command _, CoreHint_t.Phinode _ -> 1
             | CoreHint_t.Command c1, CoreHint_t.Command c2 ->
                (compare c1.CoreHint_t.index c2.CoreHint_t.index))
            nops

let insert_nop (f_id : string) (m : LLVMsyntax.coq_module)
               (nops : CoreHint_t.position list) : LLVMsyntax.coq_module =
  let nops = sort_nop nops in
  let Coq_module_intro (l, ns, ps) = m in
  let ps = List.map (fun (x : product) ->
                      match x with
                      | LLVMsyntax.Coq_product_fdef f ->
                         if (f_id = LLVMinfra.getFdefID f)
                         then
                           let Coq_fdef_intro (h, blks) = f in
                           let blks = (Nop.insert_nops (List.map nop_position_atd_to_coq nops) blks) in
                           (LLVMsyntax.Coq_product_fdef (Coq_fdef_intro (h, blks)))
                         else x
                      | _ -> x
                     ) ps in
  Coq_module_intro (l, ns, ps)

module EmptyHint = struct
  (* TODO(@youngju.song): in Coq *)
  let unary_hint : Invariant.unary =
    { Invariant.lessdef = ExprPairSet.empty;
      Invariant.alias =
        { Invariant.noalias = PtrPairSet.empty;
          Invariant.diffblock = ValueTPairSet.empty;
        };
      Invariant.unique = AtomSetImpl.empty;
      Invariant.coq_private = IdTSet.empty;
    }

  let invariant_hint : Invariant.t =
    { Invariant.src = unary_hint;
      Invariant.tgt = unary_hint;
      Invariant.maydiff = IdTSet.empty;
    }

  let stmts_hint (stmts: LLVMsyntax.stmts) (incoming_blocks: string list) : ValidationHint.stmts =
    let Coq_stmts_intro (phinodes, cmds, _) = stmts in

    let phinodes = List.map (fun bid -> (bid, [])) incoming_blocks in

    let cmds = List.map (fun _ -> ([], invariant_hint)) cmds in

    { ValidationHint.phinodes = phinodes;
      ValidationHint.invariant_after_phinodes = invariant_hint;
      ValidationHint.cmds = cmds;
    }

  let fdef_hint (fdef:LLVMsyntax.fdef) : ValidationHint.fdef =
    let Coq_fdef_intro (Coq_fheader_intro (_, _, id, _, _), blks) = fdef in
    TODO.mapiAL (fun bname bstmts ->
                 let incoming_blocks =
                   let cfg_pred = Cfg.predecessors fdef in
                   let preds = Maps_ext.ATree.get bname cfg_pred in
                   match preds with
                   | None -> []
                   | Some t -> t
                 in
                 stmts_hint bstmts incoming_blocks) blks

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
      (nops:CoreHint_t.position list)
      (cmd_d:(CoreHint_t.hint_command * CoreHint_t.cpp_debug_info))
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  let (command, d) = cmd_d in
  match command with
  | CoreHint_t.Propagate prop ->
     let invariant = PropagateHint.InvariantObject.convert prop.propagate lfdef rfdef in
     let range = Position.convert_range prop.propagate_range nops lfdef rfdef in
     propagate_hint lfdef dtree_lfdef invariant range hint_fdef
  | CoreHint_t.Infrule (pos, infrule) ->
     let pos = Position.convert pos nops lfdef rfdef in
     let infrule = convert_infrule infrule lfdef rfdef in
     add_infrule pos infrule hint_fdef

let add_false_to_dead_block hint_fdef lfdef =
  let live_blocks =
    (* meaning of succs? *)
    (* A map from an id to its successors. *)
    (* Variable successors: T.t (list T.elt).*)
    (* cfg.v 57 line *)
    (* dfs spec = impl : dfs.v 1498 *)
    let entry_label = TODOCAML.get (LLVMinfra.getEntryLabel lfdef) in
    let po =
      let succs = Cfg.successors lfdef in
      Dfs.dfs succs entry_label BinNums.Coq_xH in
    (Dfs.coq_PO_a2p po) in

  let fill_with_false { ValidationHint.phinodes = phis;
                        ValidationHint.invariant_after_phinodes = iphis;
                        ValidationHint.cmds = cs } =
    let update_src_lessdef =
      TODOCAML.compose Invariant.update_src Invariant.update_lessdef in
    let insert_false =
      (fun y -> ExprPairSet.add Invariant.false_encoding y) in
    { ValidationHint.phinodes = phis ;
      ValidationHint.invariant_after_phinodes =
        update_src_lessdef insert_false iphis ;
      ValidationHint.cmds =
        List.map
          (fun (x, invariant) -> (x, update_src_lessdef insert_false invariant))
          cs } in

  let hint_fdef: Hints.ValidationHint.fdef =
    let f = (fun i -> (fun (x: ValidationHint.stmts) ->
                       let is_live = Maps_ext.ATree.get i live_blocks in
                       match is_live with
                       | Some _ -> x
                       | None -> fill_with_false x)) in
    TODO.mapiAL f hint_fdef in
  hint_fdef

module ConvertAuto = struct
    let convert_auto_option (opt:CoreHint_t.auto_opt)
        : InfruleGen.AutoOpt.pass_t =
      match opt with
      | CoreHint_t.AUTO_GVN -> InfruleGen.AutoOpt.GVN
      | CoreHint_t.AUTO_SROA -> InfruleGen.AutoOpt.SROA
      | CoreHint_t.AUTO_INSTCOMBINE -> InfruleGen.AutoOpt.INSTCOMBINE
      | _ -> InfruleGen.AutoOpt.DEFAULT

    let set_auto (opt:CoreHint_t.auto_opt): unit =
      let auto_opt = convert_auto_option opt in
      InfruleGen.AutoOpt.pass_option := auto_opt
  end

let convert
      (lm:LLVMsyntax.coq_module)
      (rm:LLVMsyntax.coq_module)
      (core_hint:CoreHint_t.hints)
    : ValidationHint.coq_module =
  let _ = ConvertAuto.set_auto core_hint.CoreHint_t.auto_option in

  let fid = core_hint.function_id in
  let lfdef = TODOCAML.get (LLVMinfra.lookupFdefViaIDFromModule lm fid) in
  let rfdef = TODOCAML.get (LLVMinfra.lookupFdefViaIDFromModule rm fid) in
  let dtree_lfdef = TODOCAML.get (AlgDom.create_dom_tree lfdef) in

  let nops = sort_nop core_hint.CoreHint_t.nop_positions in

  let hint_fdef = EmptyHint.fdef_hint lfdef in
  let hint_fdef = List.fold_left
                    (TODOCAML.flip (apply_corehint_command lfdef rfdef dtree_lfdef nops))
                    hint_fdef core_hint.CoreHint_t.commands in
  let hint_fdef = add_false_to_dead_block hint_fdef lfdef in

  let hint_module = EmptyHint.module_hint lm in
  (* let hint_module = noret hint_module in *) (*TODO*)
  let hint_module = Alist.updateAL hint_module fid hint_fdef in
  hint_module
