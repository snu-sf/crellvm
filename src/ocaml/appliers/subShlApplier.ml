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
    (options : CoreHint_t.sub_shl)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let y = options.y in
  let x = options.x in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (x_ext, x_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (x.name) insn_hint in
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (y.name) insn_hint in
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
    let (sz, mx, a) =
      match x_rhs, y_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, mx),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz_0, Coq_value_ext_id x_ext_0, a),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_1, _, Coq_value_ext_id y_ext_0)
        when (sz = sz_0 && sz = sz_1 && y_ext = y_ext_0 && x_ext = x_ext_0) ->
        (sz, mx, a)
      | _, _, _ -> failwith "sub_shl: pattern matching failed"
    in
    let infrule = Coq_rule_sub_shl (z_ext, x_ext, y_ext, sz, mx, a) in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint