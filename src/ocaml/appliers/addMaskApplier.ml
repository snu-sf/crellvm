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
    (options : CoreHint_t.add_mask)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let y = options.y in
  let yp = options.yp in
  let block_prev_opt:string option = None in
  let make_infrules insn_hint =
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Target z.name insn_hint in
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Target y.name insn_hint in
    let (yp_ext, yp_rhs) = get_rhs_from_insn_hint CoreHint_t.Target yp.name insn_hint in
    let (sz1, x, c1, c2) =
      match y_rhs, yp_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, x,
      Coq_value_ext_const
      (LLVMsyntax.Coq_const_int (sz1_0, c2))),
      Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz1_1, _,
      Coq_value_ext_const
      (LLVMsyntax.Coq_const_int (sz1_2, c1))),
      Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1_3,
      Coq_value_ext_id yp_ext_0,
      Coq_value_ext_const
      (LLVMsyntax.Coq_const_int (sz1_4, c2_0)))
      when sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 && sz1 = sz1_3 &&
      sz1 = sz1_4 && yp_ext = yp_ext_0 ->
        (sz1, x, c1, c2)
         | _ -> failwith "add_mask: pattern matching failed"
    in
    let infrule = Coq_rule_add_mask (z_ext, y_ext, yp_ext, sz1, x, c1, c2) in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint

