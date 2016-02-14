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
    (options : CoreHint_t.sub_const_not)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let z = options.z in
  let y = options.y in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (y.name) insn_hint in
    let (z_ext, z_rhs) = get_rhs_from_insn_hint CoreHint_t.Source (z.name) insn_hint in
    let (sz, x, c1, c2) =
      match y_rhs, z_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, x, _),
        Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c1)), y)
        when sz = sz_0 && sz = sz_1 ->
        let c2 = INTEGER_OPERATION.add c1 (INTEGER.of_Z(Size.to_Z sz) (Zpos Coq_xH) true) in
        (sz, x, c1, c2)
      | _ -> failwith "sub_const_not: pattern matching failed"
    in
    let infrule = Coq_rule_sub_const_not (z_ext, y_ext, sz, x, c1, c2) in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint
