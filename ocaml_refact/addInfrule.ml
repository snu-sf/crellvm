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

let make_coq_infrule (infrule:CoreHint_t.infrule) : Infrule.t

(* add an inference rule for a phinode *)
let add_infrule_phinode (infrule:CoreHint_t.infrule)
                        (pos_phinode:CoreHint_t.pos_phinode)
                        (prev_block:atom option)
                        (block_hint:Hints.stmts) : Hints.stmts =
  let is_applicable_phiid prev_block phiid = (prev_block = Some phiid) in
  let hint_phinodes =
    List.map
    (fun (phiid, infrules) ->
      if not (is_applicable_phiid prev_block phiid)
      then (phiid, infrules)
      else
        let coq_infrule = make_coq_infrule infrule
        let infrules = List.append infrules [coq_infrule] in
        (phiid, infrules))
    block_hint.phinodes in
  let block_hint = { block_hint with phinodes = hint_phinodes } in
  block_hint

(* add an inference rule for a command *)
let add_infrule_command (infrule:CoreHint_t.infrule)
                        (pos_command:CoreHint_t.pos_command)
                        (line_num:int)
                        (block_hint:Hints.stmts) : Hint.stmts =
  let hint_cmds =
    let coq_infrule = make_coq_infrule infrule in
    let update_infrules n (infrules, inv) =
      if not (line_num = n) then infrules
      else (List.append infrules [coq_infrule], inv) in
    mapi update_infrules block_hint.cmds in
  let block_hint = { block_hint with cmds = hint_cmds } in
  block_hint

(* add an inference rule at the "at" in the hint. *)
let add_infrule (infrule:CoreHint_t.infrule) (block_prev_opt:atom option)
                  (lfd:LLVMsyntax.fdef) (rfd:LLVMsyntax.fdef)
                  (hint:ValidationHint.fdef) : ValidationHint.fdef =
  let block_hints = hint in
  let pos = infrule.position in
  let block_name =
    (match pos with
    | CoreHint_t.Phinode phinode -> phinode.block_name
    | CoreHint_t.Command command ->
        let (bid, _) = get_pos_from_command command lfd rfd in
        bid) in
  match LLVMinfra.lookupBlockViaLabelFromFdef lfd (block_name),
        LLVMinfra.lookupBlockViaLabelFromFdef rfd (block_name),
        Alist.lookupAL block_hints (block_name) with
  | None, _, _ -> failwith "add_inference: no such block in source"
  | _, None, _ -> failwith "add_inference: no such block in target"
  | _, _, None -> failwith "add_inference: no such block hint"
  | Some (LLVMsyntax.Coq_stmts_intro (lphis, lcmds, _)),
    Some (LLVMsyntax.Coq_stmts_intro (rphis, rcmds, _)),
    Some block_hint ->
      let block_hint_new =
        (match pos with
        | CoreHint_t.Phinode phinode ->
            add_infrule_phinode infrule phinode block_prev_opt block_hint
        | CoreHint_t.Command command ->
            let (_, line_num) = get_pos_from_command command lfd rfd in
            add_infrule_command infrule command line_num block_hint) in
      let block_hints = Alist.updateAL block_hints (block_name) block_hint_new in
      block_hints
