(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open Datatype_base
open Syntax
open BinInt
open BinPos
open Vars_aux
open Validator_aux
open Extraction_defs
open AddInferenceHints
open PropagateHints
open Utility
open CoreHint_t
open CommandArg


let new_temp_var_count = ref 0
let new_temp_var () =
  let result = "#stash" ^ (string_of_int !new_temp_var_count) in
  let _ = new_temp_var_count := !new_temp_var_count + 1 in
  result


let propagate_micro
(raw_hint : CoreHint_t.command)
(args : CommandArg.microhint_args)
: fdef_hint_t =
  match raw_hint with
  | CoreHint_t.Propagate (options:CoreHint_t.propagate) ->
      let (elt : PropagateHints.invariant_elt_t), (fdef : LLVMsyntax.fdef), (block_prev_opt : string option) =
        match options.propagate with
        | CoreHint_t.Instr instr_args ->
            (*let (lhspos, lhslr, lhs, lhstyp) = getVar 0 args in*)
            let lhsvar : CoreHint_t.variable = instr_args.lhs in
            let (lhs) = (lhsvar.name) in
            (*let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in*)
      let rhspos : CoreHint_t.position = instr_args.rhs_at in

      (*let tpos = getPos 2 args in*)
      (*let block_prev_opt = getBlock 3 args in*)
      let block_prev_opt : string option = None in

      let (lhsfdef, lhsnoop) =
        (args.lfdef, args.lnoop)
        (*match lhslr with
        | ParseHints.Original -> (lfdef, lnoop)
               | ParseHints.Optimized -> (rfdef, rnoop)*)
      in
      let (rhsfdef, rhsnoop) =
        (args.lfdef, args.lnoop)
        (*match rhslr with
        | ParseHints.Original -> (lfdef, lnoop)
              | ParseHints.Optimized -> (rfdef, rnoop)*)
      in
      let rhs_bb : string = rhspos.block_name in
      let rhs_block =
        match LLVMinfra.lookupBlockViaLabelFromFdef rhsfdef rhs_bb with
        | Some block -> block
        | None ->
            (*(match LLVMinfra.lookupBlockViaIDFromFdef rhsfdef rhs with
            | Some block -> snd block
            | None -> *)
            try
              (match rhsfdef with
              Syntax_base.LLVMsyntax_base.Coq_fdef_intro (_,blks) ->
                snd (List.nth blks (int_of_string rhs_bb))
                )
              with Failure "int_of_string" ->
                failwith "propagate_micro instr_propagate rhs_block (juneyoung lee)"
          (* ) *)
      in
      let rhs_insn =
        match rhspos.instr_index with
        | CoreHint_t.Command idx ->
            let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
            let orig_idx = Utility.get_orig_idx rhsnoop idx in
            let cmds = match rhs_block with Syntax_base.LLVMsyntax_base.Coq_stmts_intro (_,cmds,_) -> cmds in
            Syntax_base.LLVMsyntax_base.Coq_insn_cmd (List.nth cmds orig_idx)
        | _ ->
            (*
            (match LLVMinfra.lookupInsnViaIDFromFdef rhsfdef rhs with
            | Some insn -> insn
            | None ->
                *)
            failwith "propagate_micro instr2_propagate rhs_insn (juneyoung lee)"
            (* ) *)
            in
            let rhs_phivars =
              let LLVMsyntax.Coq_stmts_intro (phinodes, _, _) = rhs_block in
              List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
              in
              (make_eq_insn lhs rhs_insn rhs_phivars block_prev_opt), args.lfdef, block_prev_opt

        | CoreHint_t.Eq eq_args ->
            let v1 : CoreHint_t.value = eq_args.lhs in
            let v2 : CoreHint_t.value = eq_args.rhs in
            let llvm_v1 = PropagateHints.convert_to_LLVMvalue v1 args.lfdef in
            let llvm_v2 = PropagateHints.convert_to_LLVMvalue v2 args.lfdef in
            let block_prev_opt : string option = None (*getBlock 4 args *) in
            (make_eq_reg llvm_v1 llvm_v2), args.lfdef, block_prev_opt
            in
            let propagate_from : CoreHint_t.position = options.propagate_from in
            let propagate_to : CoreHint_t.position = options.propagate_to in
            let fdef_hint =
              propagate
              ~block_prev_opt:block_prev_opt
              propagate_from propagate_to
              (tag_lr (*lhslr // juneyoung lee : we assume that all propagate commands are applied to Source*) CoreHint_t.Source elt)
              fdef args.fdef_hint args.dom_tree
            in
            fdef_hint

        | CoreHint_t.AddAssoc (options:CoreHint_t.add_assoc) ->
            AddAssocApplier.apply options args
        | CoreHint_t.RemoveMaydiff (options : CoreHint_t.remove_maydiff) ->
            RemoveMaydiffApplier.apply options args
        | CoreHint_t.AddSub (options:CoreHint_t.add_sub) ->
            AddSubApplier.apply options args
        | CoreHint_t.AddComm (options:CoreHint_t.add_comm) ->
            AddCommApplier.apply options args
        | CoreHint_t.AddShift (options:CoreHint_t.add_shift) ->
            AddShiftApplier.apply options args
        | CoreHint_t.AddSignbit (options:CoreHint_t.add_signbit) ->
            AddSignbitApplier.apply options args
        | CoreHint_t.AddOnebit (options:CoreHint_t.add_onebit) ->
            AddOnebitApplier.apply options args
        | CoreHint_t.AddZextBool (options:CoreHint_t.add_zext_bool) ->
            AddZextBoolApplier.apply options args

        (* NOTE: Add here to add a new rule *)
