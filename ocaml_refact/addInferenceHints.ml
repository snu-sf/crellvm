(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
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
open CoreHint_t
open Printexc

type atom = AtomImpl.atom

let update_cmd lr cmd insn_hint =
  let eqs = _choose_hint_invariant_by_scope lr insn_hint.hint_invariant in
  let eqs = add_ntag_option_cmd_to_eqs eqs (Some cmd) in
  let invariant =
    match lr with
    | CoreHint_t.Source -> {insn_hint.hint_invariant with invariant_original = eqs}
    | CoreHint_t.Target -> {insn_hint.hint_invariant with invariant_optimized = eqs}
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

(* add an inference rule at the "at" in the hint. *)
let add_inference (pos : CoreHint_t.position) (block_prev_opt:atom option)
                  (make_infrules:insn_hint_t -> infrule_t list)
                  (lfd:LLVMsyntax.fdef) (rfd:LLVMsyntax.fdef)
                  (left_m:Syntax.LLVMsyntax.coq_module)
                  (right_m:Syntax.LLVMsyntax.coq_module)
                  (hint:Hints.stmts) : Hints.stmts =
  let block_hints = hint in
  match LLVMinfra.lookupBlockViaLabelFromFdef lfd (pos.block_name),
        LLVMinfra.lookupBlockViaLabelFromFdef rfd (pos.block_name),
        Alist.lookupAL block_hints (pos.block_name) with
  | None, _, _ -> failwith "add_inference: no such block in source"
  | _, None, _ -> failwith "add_inference: no such block in target"
  | _, _, None -> failwith "add_inference: no such block hint"
  | Some (LLVMsyntax.Coq_stmts_intro (lphis, lcmds, _)),
    Some (LLVMsyntax.Coq_stmts_intro (rphis, rcmds, _)),
    Some block_hint ->
     let is_applicable_phiid phiid =
       (block_prev_opt = None || block_prev_opt = Some phiid)
     in
     let phi_hint =
       match (pos.instr_index) with
       | CoreHint_t.Phinode prev_block ->
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
       match (pos.instr_index) with
       | CoreHint_t.Command at_nth ->
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
       match (pos.instr_index) with
       | CoreHint_t.Terminator ->
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
     let block_hints = Alist.updateAL block_hints (pos.block_name) block_hint in
     block_hints
