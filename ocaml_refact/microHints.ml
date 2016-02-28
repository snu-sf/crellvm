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

  (* NOTE: Add here to add a new rule *)
