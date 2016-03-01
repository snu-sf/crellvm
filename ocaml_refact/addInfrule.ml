(**********************************)
(* add inference rule to the hint *)
(**********************************)

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
open CoreHintUtil
open Printexc

type atom = AtomImpl.atom

(* add an inference rule for a phinode *)
let add_infrule_phinode (coq_infrule:Infrule.t)
                        (pos_phinode:CoreHint_t.position_phinode)
                        (block_hint:Hints.stmts) : Hints.stmts =
  let prev_block = pos_phinode.prev_block_name in
  let hint_phinodes =
    let infrules =
      match Alist.lookupAL block_hint.phinodes prev_block with
      | None -> failwith "add_infrule_phinode: no previous block exists"
      | Some infrules -> infrules
    in
    let infrules = list.append infrules [coq_infrule] in
    Alist.updateAL block_hint.phinodes prev_block infrules in
  let block_hint = { block_hint with phinodes = hint_phinodes } in
  block_hint

(* add an inference rule for a command *)
let add_infrule_command (infrule:Infrule.t)
                        (pos_command:CoreHint_t.position_command)
                        (line_num:int)
                        (block_hint:Hints.stmts) : Hint.stmts =
  let hint_cmds =
    List.mapi
      (fun n -> fun (infrules, inv) ->
        if not (line_num = n) then infrules
        else (List.append infrules [coq_infrule], inv))
      block_hint.cmds in
  let block_hint = { block_hint with cmds = hint_cmds } in
  block_hint

(* add an inference rule at the "at" in the hint. *)
let add_infrule (infrule:Infrule.t)
                (lfd:LLVMsyntax.fdef) (rfd:LLVMsyntax.fdef)
                (hint:ValidationHint.fdef) : ValidationHint.fdef =
  let block_hints = hint in
  let pos = infrule.position in
  let block_name = Position.get_block_name_from_position pos lfd rfd in
  match Alist.lookupAL block_hints block_name with
  | None -> failwith "add_infrule: no such block hint"
  | Some block_hint ->
      let block_hint_new =
        (match pos with
        | CoreHint_t.Phinode phinode ->
            add_infrule_phinode infrule phinode block_hint
        | CoreHint_t.Command command ->
            let (_, line_num) = Position.get_pos_from_command command lfd rfd in
            add_infrule_command infrule command line_num block_hint) in
      let block_hints = Alist.updateAL block_hints block_name block_hint_new in
      block_hints
