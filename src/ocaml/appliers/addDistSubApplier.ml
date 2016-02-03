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
    (options : CoreHint_t.add_dist_sub)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let mx = options.minusx in
  let my = options.minusy in
  let w = options.w in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Target (z.name) insn_hint in
    let (minusx_ext, minusx_rhs) = get_rhs_from_insn_hint CoreHint_t.Target (mx.name) insn_hint in
    let (minusy_ext, minusy_rhs) = get_rhs_from_insn_hint CoreHint_t.Target (my.name) insn_hint in
    let (w_ext, w_rhs) = get_rhs_from_insn_hint CoreHint_t.Target (w.name) insn_hint in
    let (sz1, x_ext, y_ext) =
      match minusx_rhs, minusy_rhs, w_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMSyntax.Coq_bop_sub, sz1, _, x_ext),
        Coq_rhs_ext_bop (LLVMSyntax.Coq_bop_sub, sz1_0, _, y_ext),
        Coq_rhs_ext_bop (LLVMSyntax.Coq_bop_add, sz1_1, x_ext', y_ext'),
        Coq_rhs_ext_bop (LLVMSyntax.Coq_bop_sub, sz1_2, _, Coq_value_ext_id w_ext')
      when sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 &&
      x_ext = x_ext' && y_ext = y_ext' && w_ext = w_ext' ->
        (sz1, x_ext, y_ext)
      | _ -> failwith "add_dist_sub: pattern matching failed"
    in
    let infrule = Coq_rule_add_dist_sub (z_ext, minusx_ext, minusy_ext, w_ext,
    sz1, x_ext, y_ext) in
    [infrule]
  in
  let fdef_hint = add_inference pos block_prev_opt
                                make_infrules
                                args.lfdef args.lnoop args.rfdef
                                args.rnoop args.left_m args.right_m
                                args.fdef_hint
  in
fdef_hint
