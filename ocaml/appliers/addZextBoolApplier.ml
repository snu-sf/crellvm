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
    (options : CoreHint_t.add_zext_bool)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let x = options.x in
  let y = options.y in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let x_insn = get_rhs_from_fdef x.name args.lfdef in
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Source y.name insn_hint in
    let (x_ext, b, sz, c) =
      match x_insn, y_rhs with
      | LLVMsyntax.Coq_insn_cmd
        (LLVMsyntax.Coq_insn_ext
        (_, LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int _, b, LLVMsyntax.Coq_typ_int sz)),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0,
        Coq_value_ext_id x_ext,
        Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c)))
      when sz = sz_0 && sz = sz_1 ->
        (x_ext, b, sz, c)
         | _ -> failwith "add_zext_bool: pattern matching failed"
    in
    let c' = INTEGER_OPERATION.add c (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
    let infrule = Coq_rule_add_zext_bool (x_ext, y_ext, add_ntag_value b, sz, c, c') in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
    make_infrules
    args.lfdef args.lnoop args.rfdef args.rnoop
    args.left_m args.right_m
    args.fdef_hint
  in
  fdef_hint
