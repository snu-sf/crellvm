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


let make_coq_infrule (infrule:CoreHint_t.infrule) : Infrule.t =
  match infrule with
  | CoreHint_t.AddAssociative (args:CoreHint_t.add_associative) ->
      let (x, y, z, c1, c2, c3, sz) =
        (convert_variable_to_IdT args.x, convert_variable_to_IdT args.y,
        convert_variable_to_IdT args.z, convert_const_int_to_INTEGER args.c1,
        convert_const_int_to_INTEGER args.c2, convert_const_int_to_INTEGER args.c3,
        convert_size_to_sz args.sz) in
      Coq_add_associative (x, y, z, c1, c2, c3, sz)

