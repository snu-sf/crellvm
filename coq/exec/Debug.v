Require Import Exprs.
Require Import Hints.
Require Import String.
Require Import syntax.
Import LLVMsyntax.
Require Import Metatheory.

Set Implicit Arguments.

Definition failwith_false (msg:string) (ls:list l): bool := false.
Definition failwith_None {A:Type} (msg:string) (ls:list l): option A := None.

(* These will be handled explicitly during extraction, the definition is just to notify meaning. *)
Definition debug_print (A: Type) (printer: A -> unit) (content: A): A :=
  let unused := printer content in content.
Definition debug_string (A: Type) (str: string) (host: A): A := host.

Parameter atom_printer : atom -> unit.
Parameter cmd_printer : cmd -> unit.
Parameter idT_printer : IdT.t -> unit.

Definition debug_print_validation_process
           (infrules: list Infrule.t)
           (inv0 inv1 inv2 inv3 inv: Invariant.t): Invariant.t := inv.
Definition debug_print_cmd_pair (c_src c_tgt:cmd): cmd * cmd :=
  (c_src, c_tgt).
