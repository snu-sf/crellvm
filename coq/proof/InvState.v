Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import sflib.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.

Set Implicit Arguments.


(* For TODOs, see `coq/hint/hint_sem.v` *)
Module Unary.
  Structure t := mk {
    previous: GVMap;
    ghost: GVMap;
  }.

  Definition sem_tag (st:State) (invst:t) (tag:Tag.t): GVsMap :=
    match tag with
    | Tag.physical => st.(EC).(Locals)
    | Tag.previous => invst.(previous)
    | Tag.ghost => invst.(ghost)
    end.

  Definition sem_idT (st:State) (aux:t) (id:IdT.t): option GenericValue :=
    lookupAL _ (sem_tag st aux id.(fst)) id.(snd).

  Definition sem_valueT (conf:Config) (st:State) (aux:t) (v:ValueT.t): option GenericValue :=
    match v with
    | ValueT.id id => sem_idT st aux id
    | ValueT.const c => const2GV conf.(CurTargetData) conf.(Globals) c
    end.

  Definition sem_expr (conf:Config) (st:State) (aux:t) (e:Expr.t): option GenericValue. Admitted.

  Definition sem_lessdef (conf:Config) (st:State) (aux:t) (es:ExprPair.t): Prop :=
    forall val2 (VAL2: sem_expr conf st aux es.(snd) = Some val2),
    exists val1,
      <<VAL1: sem_expr conf st aux es.(fst) = Some val1>> /\
      <<VAL: GVs.lessdef val1 val2>>.

  (* TODO *)
  Inductive sem_alias (conf:Config) (st:State) (aux:t) (arel:Invariant.aliasrel): Prop :=
  .

  (* TODO *)
  Inductive sem_unique (conf:Config) (st:State) (aux:t) (a:atom): Prop :=
  .

  (* TODO: see `isolated_sem` *)
  Definition sem_private (conf:Config) (st:State) (aux:t) (private:list mblock) (a:IdT.t): Prop :=
    forall val (VAL: sem_idT st aux a = Some val),
      match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val with
      | ret Vptr b _ => In b private
      | _ => False
      end.

  Inductive sem (conf:Config) (st:State) (invst:t) (invmem:InvMem.Unary.t) (inv:Invariant.unary): Prop :=
  | sem_intro
      (LESSDEF: ExprPairSet.For_all (sem_lessdef conf st invst) inv.(Invariant.lessdef))
      (NOALIAS: sem_alias conf st invst inv.(Invariant.alias))
      (UNIQUE: AtomSetImpl.For_all (sem_unique conf st invst) inv.(Invariant.unique))
      (PRIVATE: IdTSet.For_all (sem_private conf st invst invmem.(InvMem.Unary.private)) inv.(Invariant.private))
  .
End Unary.

Module Rel.
  Structure t := mk {
    src: Unary.t;
    tgt: Unary.t;
  }.

  Definition sem_inject (st_src st_tgt:State) (invst:t) (inject:meminj) (id:IdT.t): Prop :=
    forall val_src (VAL_SRC: Unary.sem_idT st_src invst.(src) id = Some val_src),
    exists val_tgt,
      <<VAL_TGT: Unary.sem_idT st_tgt invst.(tgt) id = Some val_tgt>> /\
      <<VAL: GVs.inject inject val_src val_tgt>>.

  Inductive sem (conf_src conf_tgt:Config) (st_src st_tgt:State) (invst:t) (invmem:InvMem.Rel.t) (inv:Invariant.t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src st_src invst.(src) invmem.(InvMem.Rel.src) inv.(Invariant.src))
      (TGT: Unary.sem conf_tgt st_tgt invst.(tgt) invmem.(InvMem.Rel.tgt) inv.(Invariant.tgt))
      (MAYDIFF:
         forall id (NOTIN: IdTSet.mem id inv.(Invariant.maydiff)),
           sem_inject st_src st_tgt invst invmem.(InvMem.Rel.inject) id)
  .
End Rel.
