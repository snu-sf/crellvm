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
    (instr_args : CoreHint_t.propagate_instr)
    (args : CommandArg.microhint_args)
    (scope : CoreHint_t.scope)
    : (PropagateHints.invariant_elt_t * LLVMsyntax.fdef * string option) =

  (*let (lhspos, lhslr, lhs, lhstyp) = getVar 0 args in*)
  let lhsvar : CoreHint_t.variable = instr_args.lhs in
  let (lhs) = (lhsvar.name) in
  (*let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in*)
  let rhspos : CoreHint_t.position = instr_args.rhs_at in

  (*let tpos = getPos 2 args in*)
  (*let block_prev_opt = getBlock 3 args in*)
  let block_prev_opt : string option = None in

  let (lhsfdef, lhsnoop) =
    match scope with
    | CoreHint_t.Source -> (args.lfdef, args.lnoop)
    | CoreHint_t.Target -> (args.rfdef, args.rnoop)
    (*(args.lfdef, args.lnoop)*)
    (*match lhslr with
    | ParseHints.Original -> (lfdef, lnoop)
           | ParseHints.Optimized -> (rfdef, rnoop)*)
  in
  let (rhsfdef, rhsnoop) =
    match scope with
    | CoreHint_t.Source -> (args.lfdef, args.lnoop)
    | CoreHint_t.Target -> (args.rfdef, args.rnoop)
    (*(args.lfdef, args.lnoop)*)
    (*match rhslr with
    | ParseHints.Original -> (lfdef, lnoop)
          | ParseHints.Optimized -> (rfdef, rnoop)*)
  in
  let rhs_bb : string = rhspos.block_name in
  let rhs_block =
    match LLVMinfra.lookupBlockViaLabelFromFdef rhsfdef rhs_bb with
    | Some block -> block
    | None ->
        (*(match LLVMinfra.lookupBlockViaIDFromFdef rhsfdef rhs with
        | Some block -> snd block
        | None -> *)
        try
          (match rhsfdef with
          Syntax_base.LLVMsyntax_base.Coq_fdef_intro (_,blks) ->
            snd (List.nth blks (int_of_string rhs_bb))
            )
          with Failure "int_of_string" ->
            failwith "propagate_micro instr_propagate rhs_block (juneyoung lee)"
      (* ) *)
  in
  let rhs_insn =
    match rhspos.instr_index with
    | CoreHint_t.Command idx ->
        let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
        let orig_idx = Utility.get_orig_idx rhsnoop idx in
        let cmds = match rhs_block with Syntax_base.LLVMsyntax_base.Coq_stmts_intro (_,cmds,_) -> cmds in
        Syntax_base.LLVMsyntax_base.Coq_insn_cmd (List.nth cmds orig_idx)
    | _ ->
        (*
        (match LLVMinfra.lookupInsnViaIDFromFdef rhsfdef rhs with
        | Some insn -> insn
        | None ->
            *)
        failwith "propagate_micro instr2_propagate rhs_insn (juneyoung lee)"
        (* ) *)
  in
  let rhs_phivars =
    let LLVMsyntax.Coq_stmts_intro (phinodes, _, _) = rhs_block in
    List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
  in
  let fdef =
    match scope with
    | CoreHint_t.Source -> args.lfdef
    | CoreHint_t.Target -> args.rfdef
  in
  (make_eq_insn lhs rhs_insn rhs_phivars block_prev_opt), fdef, block_prev_opt


