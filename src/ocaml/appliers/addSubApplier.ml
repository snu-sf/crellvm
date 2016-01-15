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
open MicroHintsArg


let apply
     (options : CoreHint_t.add_sub) 
     (args : MicroHintsArg.microhint_args)
     : fdef_hint_t = 

     let pos = options.position in
     let z = options.z in
     let my = options.minusy in
     let block_prev_opt:string option = None in

     let make_infrules insn_hint =
       let (minusy_ext, minusy_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (my.name) insn_hint in
       let rights = get_rhses_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
       let get_one_infrule (z_ext,z_rhs) =
         match minusy_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, y_ext),
       Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0, x_ext, (Coq_value_ext_id minusy_ext_0))
         when sz = sz_0 && minusy_ext = minusy_ext_0 ->
           [Coq_rule_add_sub (z_ext, minusy_ext, sz, x_ext, y_ext)]
         | _ -> []
       in
       List.fold_left
         (fun acc (z_ext,z_rhs) -> acc @ get_one_infrule (z_ext,z_rhs))
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   args.lfdef args.lnoop args.rfdef args.rnoop args.left_m args.right_m
                                   args.fdef_hint
     in
     fdef_hint

