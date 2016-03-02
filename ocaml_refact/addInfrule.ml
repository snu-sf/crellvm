(**********************************)
(* add inference rule to the hint *)
(**********************************)

open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open MetatheoryAtom
open Extraction_defs
open CoreHint_t
open ConvertUtil
open Printexc

type atom = AtomImpl.atom

let add_infrule_phinode (coq_infrule:Infrule.t)
                        (prev_block:atom)
                        (block_hint:ValidationHint.stmts) : ValidationHint.stmts =
  let hint_phinodes = block_hint.ValidationHint.phinodes in
  let infrules = TODOCAML.get (Alist.lookupAL hint_phinodes prev_block) in
  let infrules = List.append infrules [coq_infrule] in
  let hint_phinodes = Alist.updateAL hint_phinodes prev_block infrules in
  let block_hint = { block_hint with ValidationHint.phinodes = hint_phinodes } in
  block_hint

let add_infrule_command (infrule:Infrule.t)
                        (line_num:int)
                        (block_hint:ValidationHint.stmts)
    : ValidationHint.stmts =
  let hint_cmds =
    List.mapi
      (fun n (infrules, inv) ->
        if line_num <> n
        then (infrules, inv)
        else (List.append infrules [infrule], inv))
      block_hint.ValidationHint.cmds
  in
  let block_hint = { block_hint with ValidationHint.cmds = hint_cmds } in
  block_hint

let add_infrule (pos:Position.t)
                (infrule:Infrule.t)
                (block_hints:ValidationHint.fdef)
    : ValidationHint.fdef =
  let (block_name, idx) = pos in
  let block_hint = TODOCAML.get (Alist.lookupAL block_hints block_name) in
  let block_hint =
    match idx with
    | Position.Phinode prev_block ->
       add_infrule_phinode infrule prev_block block_hint
    | Position.Command line_num ->
       add_infrule_command infrule line_num block_hint
  in
  let block_hints = Alist.updateAL block_hints block_name block_hint in
  block_hints
