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
    (options : CoreHint_t.mul_neg)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let mx = options.mx in
  let my = options.my in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (mx_ext, mx_rhs) = get_rhs_from_insn_hint CoreHint_t.Source mx.name insn_hint in
    let (my_ext, my_rhs) = get_rhs_from_insn_hint CoreHint_t.Source my.name insn_hint in
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Source z.name insn_hint in
    let (sz, x, y) =
      match mx_rhs, my_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, x),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, _, y),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz_1, Coq_value_ext_id mx_ext_0, Coq_value_ext_id my_ext_0)
        when (sz = sz_0 && sz = sz_1 && mx_ext = mx_ext_0 && my_ext = my_ext_0) ->
        (sz, x, y)
      | _, _, _ -> failwith "mul_neg : pattern matching failed"
    in 
    let infrule = Coq_rule_mul_neg (z_ext, mx_ext, my_ext, sz, x, y) in
    [infrule]
  in
  let fdef_hint = add_inference pos block_prev_opt
                                make_infrules
                                args.lfdef args.lnoop args.rfdef
                                args.rnoop args.left_m args.right_m
                                args.fdef_hint
  in
  fdef_hint

