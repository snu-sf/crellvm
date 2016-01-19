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
     (options : CoreHint_t.add_comm)
     (args : CommandArg.microhint_args)
     : fdef_hint_t =

     let pos = options.position in
     let z = options.z in
     let block_prev_opt:string option = None in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "add_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_add_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   args.lfdef args.lnoop args.rfdef args.rnoop args.left_m args.right_m
                                   args.fdef_hint
     in
     fdef_hint

