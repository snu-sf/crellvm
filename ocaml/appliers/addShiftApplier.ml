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
    (options : CoreHint_t.add_shift)
    (args : CommandArg.microhint_args)
    : fdef_hint_t =

  let pos = options.position in
  let y = options.y in
  let block_prev_opt:string option = None in

  let make_infrules insn_hint =
    let (y_ext, y_rhs) = get_rhs_from_insn_hint CoreHint_t.Source y.name insn_hint in
    let (sz, x_ext) =
      match y_rhs with
      | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, x_ext, x_ext_0)
      when x_ext = x_ext_0 ->
        (sz, x_ext)
         | _ -> failwith "add_shift: pattern matching failed"
    in
    let infrule = Coq_rule_add_shift (y_ext, sz, x_ext) in
    [infrule]
    in
    let fdef_hint = add_inference pos block_prev_opt
                                  make_infrules
                                  args.lfdef args.lnoop args.rfdef
                                  args.rnoop args.left_m args.right_m
                                  args.fdef_hint
  in
  fdef_hint

