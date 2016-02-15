(********************************************)
(* applying propagate command to invariants *)
(********************************************)

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
open CoreHint_t
open CommandArg


let apply
    (maydiffglobal_args : CoreHint_t.maydiff_global) 
    (args : CommandArg.microhint_args)
    : fdef_hint_t = 
    
  let variable = maydiffglobal_args.variable in
  let fdef_hint = propagate_maydiff_in_fdef_hint (variable.name, Coq_ntag_old) args.fdef_hint in
  let fdef_hint = propagate_maydiff_in_fdef_hint (variable.name, Coq_ntag_new) fdef_hint in
  fdef_hint
