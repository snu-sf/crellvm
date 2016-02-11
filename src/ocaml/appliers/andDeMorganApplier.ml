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
open PrintHints


let apply
    (options : CoreHint_t.and_de_morgan)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let x = options.x in
  let y = options.y in
  let z2 = options.z2 in
  let block_prev_opt:string option = None in
  let make_infrules insn_hint =
    let ((z_ext: Syntax_ext.id_ext), (z_rhs: Syntax_ext.rhs_ext)) = get_rhs_from_insn_hint CoreHint_t.Target z.name insn_hint in
    let (x_ext, x_rhs) = get_rhs_from_insn_hint CoreHint_t.Target x.name insn_hint in
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Target y.name insn_hint in
    let (z2_ext, z2_rhs) = get_rhs_from_insn_hint CoreHint_t.Target z2.name insn_hint in
    let (sz, a, b) = 
      match x_rhs, y_rhs, z2_rhs, z_rhs with 
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, a, _),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz_0, b, _),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz_1, _, _),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz_2, Coq_value_ext_id z'_ext_0, _)
           when sz = sz_0 && sz = sz_1 && sz = sz_2 && z2_ext = z'_ext_0 ->
        (sz, a, b)
      | _ -> failwith "and_demorgan: pattern matching failed"
    in
    let infrule = Coq_rule_and_demorgan (z_ext, x_ext, y_ext, z2_ext, sz, a, b) in
    [infrule]
		in
		let fdef_hint = add_inference pos block_prev_opt
																																make_infrules
																																args.lfdef args.lnoop args.rfdef
																																args.rnoop args.left_m args.right_m
																																args.fdef_hint
  in
  fdef_hint
