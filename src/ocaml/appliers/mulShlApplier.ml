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
    (options : CoreHint_t.mul_shl)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let y = options.y in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (y.name) insn_hint in
    let rights = get_rhses_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
    List.fold_left
    (fun acc (z_ext, z_rhs) ->
      match y_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz, _, a),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz_0, x, Coq_value_ext_id y_ext_0)
        when sz = sz_0 && y_ext = y_ext_0 ->
          acc @ [Coq_rule_mul_shl (z_ext, y_ext, sz, x, a)]
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz, _, a),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, Coq_value_ext_id y_ext_0, x)
        when sz = sz_0 && y_ext = y_ext_0 ->
          acc @ [Coq_rule_mul_shl (z_ext, y_ext, sz, x, a)]
      | _ -> acc)
    [] rights
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint
