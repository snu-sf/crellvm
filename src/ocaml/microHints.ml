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
  | CoreHint_t.PropagateGlobal (options:CoreHint_t.propagate_global) ->
      (match options.propagate with
      | CoreHint_t.MaydiffGlobal maydiffglobal_args ->
          PropagateMaydiffGlobalApplier.apply maydiffglobal_args args
      )
  | CoreHint_t.Propagate (options:CoreHint_t.propagate) ->
      let (elt : PropagateHints.invariant_elt_t), (fdef : LLVMsyntax.fdef), (block_prev_opt : string option) =
        match options.propagate with
        | CoreHint_t.Instr instr_args ->
            PropagateInstrApplier.apply instr_args args options.scope
        | CoreHint_t.Eq eq_args ->
            PropagateEqApplier.apply eq_args args
        | CoreHint_t.Neq neq_args ->
            PropagateNeqApplier.apply neq_args args
      in
      let propagate_from : CoreHint_t.position = options.propagate_from in
      let propagate_to : CoreHint_t.position = options.propagate_to in
      let fdef_hint =
        propagate
        ~block_prev_opt:block_prev_opt
        propagate_from propagate_to
        (tag_lr options.scope elt)
        fdef args.fdef_hint args.dom_tree
      in
      fdef_hint

  | CoreHint_t.RemoveMaydiff (options : CoreHint_t.remove_maydiff) ->
      RemoveMaydiffApplier.apply options args
  | CoreHint_t.AddAssociative (options:CoreHint_t.add_associative) ->
      AddAssociativeApplier.apply options args
  | CoreHint_t.AddSub (options:CoreHint_t.add_sub) ->
      AddSubApplier.apply options args
  | CoreHint_t.AddCommutative (options:CoreHint_t.add_commutative) ->
      AddCommutativeApplier.apply options args
  | CoreHint_t.AddShift (options:CoreHint_t.add_shift) ->
      AddShiftApplier.apply options args
  | CoreHint_t.AddSignbit (options:CoreHint_t.add_signbit) ->
      AddSignbitApplier.apply options args
  | CoreHint_t.AddOnebit (options:CoreHint_t.add_onebit) ->
      AddOnebitApplier.apply options args
  | CoreHint_t.AddZextBool (options:CoreHint_t.add_zext_bool) ->
      AddZextBoolApplier.apply options args
  | CoreHint_t.AddConstNot (options:CoreHint_t.add_const_not) ->
      AddConstNotApplier.apply options args
  | CoreHint_t.AddMask (options:CoreHint_t.add_mask) ->
      AddMaskApplier.apply options args
  | CoreHint_t.AddSelectZero (options:CoreHint_t.add_select_zero) ->
      AddSelectZeroApplier.apply options args
  | CoreHint_t.AddSelectZero2 (options:CoreHint_t.add_select_zero2) ->
      AddSelectZero2Applier.apply options args
  | CoreHint_t.AddDistSub (options:CoreHint_t.add_dist_sub) ->
      AddDistSubApplier.apply options args
  | CoreHint_t.MulAddDistributive (options:CoreHint_t.mul_add_distributive) ->
      MulAddDistributiveApplier.apply options args
  | CoreHint_t.SubAdd (options:CoreHint_t.sub_add) ->
      SubAddApplier.apply options args
  | CoreHint_t.SubMone (options:CoreHint_t.sub_mone) ->
      SubMoneApplier.apply options args
  | CoreHint_t.SubConstNot (options:CoreHint_t.sub_const_not) ->
      SubConstNotApplier.apply options args
  | CoreHint_t.SubRemove (options:CoreHint_t.sub_remove) ->
      SubRemoveApplier.apply options args
  | CoreHint_t.SubRemove2 (options:CoreHint_t.sub_remove2) ->
      SubRemove2Applier.apply options args
  | CoreHint_t.SubOnebit (options:CoreHint_t.sub_onebit) ->
      SubOnebitApplier.apply options args
  | CoreHint_t.SubConstAdd (options:CoreHint_t.sub_const_add) ->
      SubConstAddApplier.apply options args
  | CoreHint_t.SubSdiv (options:CoreHint_t.sub_sdiv) ->
      SubSdivApplier.apply options args
  | CoreHint_t.SubShl (options:CoreHint_t.sub_shl) ->
      SubShlApplier.apply options args
  | CoreHint_t.MulBool (options:CoreHint_t.mul_bool) ->
      MulBoolApplier.apply options args
  | CoreHint_t.MulMone (options:CoreHint_t.mul_mone) ->
      MulMoneApplier.apply options args
  | CoreHint_t.MulNeg (options:CoreHint_t.mul_neg) ->
      MulNegApplier.apply options args
  | CoreHint_t.MulCommutative (options:CoreHint_t.mul_commutative) ->
      MulCommutativeApplier.apply options args
  | CoreHint_t.MulShl (options:CoreHint_t.mul_shl) ->
      MulShlApplier.apply options args
  | CoreHint_t.DivMone (options:CoreHint_t.div_mone) ->
      DivMoneApplier.apply options args

  (* NOTE: Add here to add a new rule *)
