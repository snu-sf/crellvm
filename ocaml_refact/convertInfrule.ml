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
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let z = Convert.register args.z in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let c3 = Convert.const_int args.c3 in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_associative (x, y, z, c1, c2, c3, sz)
  | CoreHint_t.SubAdd (args:CoreHint_t.sub_add) ->
      let z = Convert.register args.z in
      let my = Convert.register args.my in
      let x = Convert.register args.x in
      let y = Convert.register args.y in
      let sz = Convert.size args.sz in
      Infrule.Coq_sub_add (z, my, x, y, sz)
  | CoreHint_t.MulBool (args:CoreHint_t.mul_bool) ->
      let z = Convert.register args.z in
      let x = Convert.register args.x in
      let y = Convert.register args.y in
      Infrule.Coq_mul_bool (z, x, y) 
  | _ ->
     failwith "TODO"
