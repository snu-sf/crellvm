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
    (neq_args : CoreHint_t.propagate_neq)
    (args : CommandArg.microhint_args)
    : (PropagateHints.invariant_elt_t * LLVMsyntax.fdef * string option) =

  let lhs : CoreHint_t.variable = neq_args.lhs in
  let rhs : CoreHint_t.variable = neq_args.rhs in
  let block_prev_opt : string option = None in
  (make_neq_reg (PropagateHints.convert_var_to_LLVMvalue lhs args.lfdef) (PropagateHints.convert_var_to_LLVMvalue rhs args.lfdef)), args.lfdef, block_prev_opt

