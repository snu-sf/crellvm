(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
open Interpreter
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open Vars_aux
open Validator_aux
open Extraction_defs
open Utility

type atom = AtomImpl.atom

let get_rhs_from_fdef v fdef : LLVMsyntax.insn =
  match LLVMinfra.lookupInsnViaIDFromFdef fdef v with
  | None -> failwith "get_rhs_from_fdef"
  | Some insn -> insn

let get_rhses_from_insn_hint lr var hint : (id_ext * rhs_ext) list =
  let hint = hint.hint_invariant in
  let hint =
    match lr with
    | ParseHints.Original -> hint.invariant_original
    | ParseHints.Optimized -> hint.invariant_optimized
  in
  let hints =
    EqRegSetImpl.filter
      (fun (id_ext, rhs_ext) -> var = fst id_ext)
      hint.eqs_eq_reg
  in
  EqRegSetImpl.elements hints

let get_rhs_from_insn_hint lr var hint : id_ext * rhs_ext =
  let hint = hint.hint_invariant in
  let hint =
    match lr with
    | ParseHints.Original -> hint.invariant_original
    | ParseHints.Optimized -> hint.invariant_optimized
  in
  let hints =
    EqRegSetImpl.filter
      (fun (id_ext, rhs_ext) -> var = fst id_ext)
      hint.eqs_eq_reg
  in
  match EqRegSetImpl.choose hints with
  | Some r -> r
  | None -> failwith "get_rhs_from_insn_hint: no such hint"

let get_dereference_from_insn_hint lr ptr hint : LLVMsyntax.typ * LLVMsyntax.align * value_ext =
  let hint = hint.hint_invariant in
  let hint =
    match lr with
    | ParseHints.Original -> hint.invariant_original
    | ParseHints.Optimized -> hint.invariant_optimized
  in
  let hints =
    EqHeapSetImpl.filter
      (fun (((lhs_ext, _), _), rhs_ext) -> value_ext_dec ptr lhs_ext)
      hint.eqs_eq_heap
  in
  match EqHeapSetImpl.choose hints with
  | None -> failwith "get_dereference_from_insn_hint: no such hint"
  | Some (((_, typ), align), r) -> (typ, align, r)

let get_dereference_from_insn_hint_wo_var lr (var:atom) ptr hint : LLVMsyntax.typ * LLVMsyntax.align * value_ext =
  let hint = hint.hint_invariant in
  let hint =
    match lr with
    | ParseHints.Original -> hint.invariant_original
    | ParseHints.Optimized -> hint.invariant_optimized
  in
  let hints =
    EqHeapSetImpl.filter
      (fun (((lhs_ext, _), _), rhs_ext) -> 
        (value_ext_dec ptr lhs_ext ||
            (match ptr with 
            | Coq_value_ext_id p -> 
              EqRegSetImpl.mem (p, Coq_rhs_ext_value lhs_ext) hint.eqs_eq_reg
            | _ -> false) ||
            (match lhs_ext with 
            | Coq_value_ext_id l -> 
              EqRegSetImpl.mem (l, Coq_rhs_ext_value ptr) hint.eqs_eq_reg
            | _ -> false)) &&
        not (Coq_value_ext_id (var, Coq_ntag_old) = rhs_ext) &&
        not (Coq_value_ext_id (var, Coq_ntag_new) = rhs_ext))
      hint.eqs_eq_heap
  in
  match EqHeapSetImpl.choose hints with
  | None -> failwith "get_dereference_from_insn_hint_wo_var: no such hint"
  | Some (((_, typ), align), r) -> (typ, align, r)

let get_reference_from_insn_hint lr (var:atom) hint : value_ext * LLVMsyntax.typ * LLVMsyntax.align * id_ext =
  let hint = hint.hint_invariant in
  let hint =
    match lr with
    | ParseHints.Original -> hint.invariant_original
    | ParseHints.Optimized -> hint.invariant_optimized
  in
  let hints =
    EqHeapSetImpl.filter
      (fun (lhs_ext, rhs_ext) ->
       (Coq_value_ext_id (var, Coq_ntag_old) = rhs_ext)
       || (Coq_value_ext_id (var, Coq_ntag_new) = rhs_ext))
      hint.eqs_eq_heap
  in
  match EqHeapSetImpl.choose hints with
  | Some (((l, t), a), Coq_value_ext_id r) -> (l, t, a, r)
  | Some _ -> failwith "get_reference_from_insn_hint: strange pattern match"
  | None -> failwith "get_reference_from_insn_hint: no such hint"

let update_cmd lr cmd insn_hint =
  let eqs =
    match lr with
    | ParseHints.Original -> insn_hint.hint_invariant.invariant_original
    | ParseHints.Optimized -> insn_hint.hint_invariant.invariant_optimized
  in
  let eqs = add_ntag_option_cmd_to_eqs eqs (Some cmd) in
  let invariant =
    match lr with
    | ParseHints.Original -> {insn_hint.hint_invariant with invariant_original = eqs}
    | ParseHints.Optimized -> {insn_hint.hint_invariant with invariant_optimized = eqs}
  in
  let insn_hint = {insn_hint with hint_invariant = invariant} in
  insn_hint

let rec get_nth_cmd n cmds noop =
  match pop_one_X cmds noop with
  | Coq_ret_pop_cmd (cmd_opt, cmds, noop) ->
     if n <= 0
     then cmd_opt
     else get_nth_cmd (n - 1) cmds noop
  | Coq_ret_pop_terminator ->
     failwith "get_nth_cmd"

(* add an inference rule at the "at" in the hint.
 *)
let add_inference (at_block, at_nth) (block_prev_opt:atom option)
                  (make_infrules:insn_hint_t -> infrule_t list)
                  (lfd:LLVMsyntax.fdef) (lnoop:noop_t)
                  (rfd:LLVMsyntax.fdef) (rnoop:noop_t)
                  (left_m:Syntax.LLVMsyntax.coq_module)
                  (right_m:Syntax.LLVMsyntax.coq_module)
                  (hint:fdef_hint_t) : fdef_hint_t =
  let block_hints = hint(*.block_hints*) in
  match LLVMinfra.lookupBlockViaLabelFromFdef lfd at_block,
        LLVMinfra.lookupBlockViaLabelFromFdef rfd at_block,
        Alist.lookupAL block_hints at_block with
  | None, _, _ -> failwith "add_inference: no such block in left"
  | _, None, _ -> failwith "add_inference: no such block in right"
  | _, _, None -> failwith "add_inference: no such block hint"
  | Some (LLVMsyntax.Coq_stmts_intro (lphis, lcmds, _)),
    Some (LLVMsyntax.Coq_stmts_intro (rphis, rcmds, _)),
    Some block_hint ->
     let is_applicable_phiid phiid =
       (block_prev_opt = None || block_prev_opt = Some phiid)
     in
     let lnoop = get_noop_by_bb at_block lnoop in
     let rnoop = get_noop_by_bb at_block rnoop in
     let phi_hint =
       match at_nth with
       | ParseHints.PhinodePos ->
          List.map
            (fun (phiid, phi_hint) ->
             if not (is_applicable_phiid phiid)
             then (phiid, phi_hint)
             else
               let insn_hint =
                 match invariant_proceed_phis phi_hint lphis rphis phiid with
                 | Some insn_hint -> insn_hint
                 | None -> phi_hint
               in
               let insn_hint = 
                 List.fold_left (fun h inf -> infrule_resolve left_m right_m h inf) 
                   insn_hint phi_hint.hint_infrules in
               let infrules = make_infrules insn_hint in
               let hint_infrules = List.append phi_hint.hint_infrules infrules in
               (phiid, {phi_hint with hint_infrules = hint_infrules}))
            block_hint.phi_hint
       | _ -> block_hint.phi_hint
     in
     let cmds_hint =
       match at_nth with
       | ParseHints.CommandPos at_nth ->
          List.map
            (fun (phiid, cmds_hint) ->
             if not (is_applicable_phiid phiid)
             then (phiid, cmds_hint)
             else
               let cmds_hint =
                 mapi
                   (fun n hint ->
                    if not (n = at_nth)
                    then hint
                    else
                      let lcmd_opt = get_nth_cmd n lcmds lnoop in
                      let rcmd_opt = get_nth_cmd n rcmds rnoop in
                      let insn_hint =
                        match invariant_proceed left_m right_m hint lcmd_opt rcmd_opt with
                        | Some insn_hint -> insn_hint
                        | None -> hint
                      in
                      let insn_hint =
                        List.fold_left
                          (infrule_resolve left_m right_m)
                          insn_hint
                          hint.hint_infrules
                      in
                      let infrules = make_infrules insn_hint in
                      let hint_infrules = List.append hint.hint_infrules infrules in
                      {hint with hint_infrules = hint_infrules})
                   cmds_hint
               in
               (phiid, cmds_hint))
            block_hint.cmds_hint
       | _ -> block_hint.cmds_hint
     in
     let term_hint =
       match at_nth with
       | ParseHints.TerminatorPos ->
          let term_hint = block_hint.term_hint in
          let term_hint = 
            List.fold_left (fun h inf -> infrule_resolve left_m right_m h inf) 
              term_hint term_hint.hint_infrules in 
          let infrules = make_infrules term_hint in
          let hint_infrules = List.append term_hint.hint_infrules infrules in
          let term_hint = {term_hint with hint_infrules = hint_infrules} in
          term_hint
       | _ -> block_hint.term_hint
     in
     let block_hint =
       {phi_hint = phi_hint;
        cmds_hint = cmds_hint;
        term_hint = term_hint}
     in
     let block_hints = Alist.updateAL block_hints at_block block_hint in
     (*{hint with block_hints =*) block_hints(*}*)
