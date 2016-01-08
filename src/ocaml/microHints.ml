(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
(* open Interpreter *)
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
open HintParser_t

let is_propagating (raw_hint:HintParser_t.command) =
  match raw_hint with 
  | HintParser_t.Propagate _ -> true
  | _ -> false
(*  match raw_hint.ParseHints.rhint_type with
  | ParseHints.InstrPropagate
  | ParseHints.Instr2Propagate
  | ParseHints.EqPropagate
  | ParseHints.NeqPropagate
  | ParseHints.StoreEqPropagate
  | ParseHints.AllocaPropagate
  | ParseHints.MaydiffPropagate
  | ParseHints.MaydiffGlobal
  | ParseHints.StashVariable 
  | ParseHints.IsoPropagate1
  | ParseHints.IsoPropagate2
    ->
     true
  | _ ->
     false
*)
(* NOTE: Check here to add a new rule *)

let new_temp_var_count = ref 0
let new_temp_var () =
  let result = "#stash" ^ (string_of_int !new_temp_var_count) in
  let _ = new_temp_var_count := !new_temp_var_count + 1 in
  result

(*
let rec get_orig_idx (n:noop_t) (idx:int) : int =
  if noop_idx_zero_exists n
  then 1+(get_orig_idx (noop_idx_zero_remove n) idx)
  else if idx=0
  then 0
  else 1+(get_orig_idx n (idx-1))
*)

let propagate_micro 
     (raw_hint : HintParser_t.command) 
     (lfdef : LLVMsyntax.fdef) 
     (lnoop : noop_t)
     (rfdef : LLVMsyntax.fdef) 
     (rnoop : noop_t) 
     (left_m : LLVMsyntax.coq_module)
     (right_m : LLVMsyntax.coq_module)
     (fdef_hint : fdef_hint_t)
     dom_tree 
     : fdef_hint_t =
  match raw_hint with
  | HintParser_t.Propagate (options:HintParser_t.propagate) ->
     CmdPropagateApplier.apply options lfdef lnoop rfdef rnoop left_m right_m fdef_hint dom_tree
  | HintParser_t.AddAssoc (options:HintParser_t.add_assoc) ->
     AddAssocApplier.apply options lfdef lnoop rfdef rnoop left_m right_m fdef_hint dom_tree
  | HintParser_t.RemoveMaydiff (options : HintParser_t.remove_maydiff) ->
     RemoveMaydiffApplier.apply options lfdef lnoop rfdef rnoop left_m right_m fdef_hint dom_tree

(* NOTE: Add here to add a new rule *)
