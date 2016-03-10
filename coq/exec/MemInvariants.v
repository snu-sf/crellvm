Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.

Set Implicit Arguments.

(* For TODOs, see `coq/hint/hint_sem.v` *)
Module Unary.
  Structure t := mk {
    previous: GVMap;
    ghost: GVMap;
    global_max: positive;
    private: list mblock;
  }.

  Definition sem_Tag (st:State) (aux:t) (tag:Tag.t): GVsMap :=
    match tag with
    | Tag.physical => st.(EC).(Locals)
    | Tag.previous => aux.(previous)
    | Tag.ghost => aux.(ghost)
    end.

  Definition sem_IdT (st:State) (aux:t) (id:IdT.t): option GenericValue :=
    lookupAL _ (sem_Tag st aux id.(fst)) id.(snd).

  Definition sem_ValueT (conf:Config) (st:State) (aux:t) (v:ValueT.t): option GenericValue :=
    match v with
    | ValueT.id id => sem_IdT st aux id
    | ValueT.const c =>
      const2GV
        conf.(CurTargetData)
        conf.(Globals)
        c
    end.

  (* TODO *)
  Definition sem_Expr (conf:Config) (st:State) (aux:t) (v:Expr.t): option GenericValue :=
    None.

  Inductive sem_lessdef (conf:Config) (st:State) (aux:t) (es:ExprPair.t): Prop :=
  | sem_lessdef_intro
      v1 v2
      (V1: sem_Expr conf st aux es.(fst) = Some v1)
      (V2: sem_Expr conf st aux es.(snd) = Some v2)
      (LESSDEF: GVs.lessdef v1 v2)
  .

  (* TODO *)
  Inductive sem_noalias (conf:Config) (st:State) (aux:t) (vs:ValueTPair.t): Prop :=
  .

  (* TODO: see `eq_reg_sem_old_alloca` *)
  Inductive sem_alloca (conf:Config) (st:State) (aux:t) (a:IdT.t): Prop :=
  .

  (* TODO: see `isolated_sem` *)
  Inductive sem_private (conf:Config) (st:State) (aux:t) (a:IdT.t): Prop :=
  .

  Inductive sem (conf:Config) (st:State) (aux:t) (inv:Invariant.unary): Prop :=
  | sem_intro
      (LESSDEF: ExprPairSet.For_all (sem_lessdef conf st aux) inv.(Invariant.lessdef))
      (NOALIAS: ValueTPairSet.For_all (sem_noalias conf st aux) inv.(Invariant.noalias))
      (ALLOCAS: IdTSet.For_all (sem_alloca conf st aux) inv.(Invariant.allocas))
      (PRIVATE: IdTSet.For_all (sem_private conf st aux) inv.(Invariant.private))
  .
End Unary.

Module Relational.
  Structure t := mk {
    src: Unary.t;
    tgt: Unary.t;
    alpha: meminj;
  }.

  (* TODO *)
  Definition sem_maydiff (st_src st_tgt:State) (aux:t) (id:IdT.t): Prop :=
    match Unary.sem_IdT st_src aux.(src) id, Unary.sem_IdT st_src aux.(src) id with
    | Some v1, Some v2 => GVs.inject aux.(alpha) v1 v2
    | _, _ => False (* TODO: we have to take care of None cases *)
    end.

  Inductive sem (conf_src conf_tgt:Config) (st_src st_tgt:State) (aux:t) (inv:Invariant.t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src st_src aux.(src) inv.(Invariant.src))
      (TGT: Unary.sem conf_tgt st_tgt aux.(tgt) inv.(Invariant.tgt))
      (MAYDIFF: IdTSet.For_all (sem_maydiff st_src st_tgt aux) inv.(Invariant.maydiff))
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (INCR: inject_incr lhs.(alpha) rhs.(alpha))
      (TODO: False)
  .

  (* TODO: le_public? *)
End Relational.
