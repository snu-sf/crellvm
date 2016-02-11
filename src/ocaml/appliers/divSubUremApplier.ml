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
    (options : CoreHint_t.div_sub_urem)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let b = options.b in
  let a = options.a in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (b_ext, b_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (b.name) insn_hint in
    let (a_ext, a_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (a.name) insn_hint in
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
    let (sz, x, y) =
      match b_rhs, a_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_urem, sz, x, y),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, x_0, Coq_value_ext_id b_ext_0),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_udiv, sz_1, Coq_value_ext_id a_ext_0, y_0)
        when (sz = sz_0 && sz = sz_1 && y = y_0 && x = x_0 && a_ext = a_ext_0 && b_ext = b_ext_0) ->
        (sz, x, y)
      | _, _, _ -> failwith "div_sub_urem: pattern matching failed"
    in
    let infrule = Coq_rule_div_sub_urem (z_ext, b_ext, a_ext, sz, x, y) in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint
