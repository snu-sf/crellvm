open Hints
open Syntax

(** val gen_infrules_from_cmds :
    LLVMsyntax.cmd -> LLVMsyntax.cmd -> Invariant.t -> Infrule.t list **)

let gen_infrules_from_cmds
      (cmd_src cmd_tgt:LLVMsyntax.cmd)
      (inv : Invariant.t)
    : Infrule.t list
  = []

(** val gen_infrules : Invariant.t -> Invariant.t -> Infrule.t list **)

let gen_infrules
      (inv inv_nxt : Invariant.t)
    : Infrule.t list
  = []
