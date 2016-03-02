(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open MetatheoryAtom
open Datatype_base
open Syntax
open BinInt
open BinPos
open Extraction_defs
open AddInfrule
open CoreHint_t
open ConvertUtil

let convert_infrule (infrule:CoreHint_t.infrule) : Infrule.t =
  match infrule with
  | CoreHint_t.AddAssociative (args:CoreHint_t.add_associative) ->
     let x = Convert.variable_to_IdT args.x in
     let y = Convert.variable_to_IdT args.y in
     let z = Convert.variable_to_IdT args.z in
     let c1 = Convert.const_int_to_INTEGER args.c1 in
     let c2 = Convert.const_int_to_INTEGER args.c2 in
     let c3 = Convert.const_int_to_INTEGER args.c3 in
     let sz = Convert.size_to_sz args.sz in
     Coq_add_associative (x, y, z, c1, c2, c3, sz)
  | _ ->
     failwith "TODO"
