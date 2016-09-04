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
Require Import Inject.
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

  Lemma sem_empty
        conf st invst invmem inv
        (EMPTY: Invariant.is_empty_unary inv):
    sem conf st invst invmem inv.
  Proof.
  Admitted.

  Lemma sem_valueT_physical
        conf st inv val:
    sem_valueT conf st inv (Exprs.ValueT.lift Exprs.Tag.physical val) =
    getOperandValue conf.(CurTargetData) val st.(EC).(Locals) conf.(Globals).
  Proof. destruct val; ss. Qed.
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
         forall id (NOTIN: ~ IdTSet.mem id inv.(Invariant.maydiff)),
           sem_inject st_src st_tgt invst invmem.(InvMem.Rel.inject) id)
  .

  Lemma sem_empty
        conf_src ec_src ecs_src mem_src
        conf_tgt ec_tgt ecs_tgt mem_tgt
        invmem inv
        (SRC: Hints.Invariant.is_empty_unary inv.(Invariant.src))
        (TGT: Hints.Invariant.is_empty_unary inv.(Invariant.tgt))
        (LOCALS: inject_locals invmem ec_src.(Locals) ec_tgt.(Locals)):
    exists invst,
      sem conf_src conf_tgt
          (mkState ec_src ecs_src mem_src)
          (mkState ec_tgt ecs_tgt mem_tgt)
          invst invmem inv.
  Proof.
    exists (mk (Unary.mk [] []) (Unary.mk [] [])).
    econs.
    - apply Unary.sem_empty. ss.
    - apply Unary.sem_empty. ss.
    - ii. unfold Unary.sem_idT, Unary.sem_tag in *.
      destruct id0. destruct t0; ss.
      exploit LOCALS; eauto. i. des.
      esplits; eauto. admit. (* easy *)
  Admitted.

  Lemma inject_value_spec
        conf_src st_src val_src
        conf_tgt st_tgt val_tgt
        invst invmem inv
        gval_src
        (STATE: sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
        (INJECT: Hints.Invariant.inject_value inv val_src val_tgt)
        (VAL_SRC: Unary.sem_valueT conf_src st_src invst.(src) val_src = Some gval_src):
    exists gval_tgt,
      <<VAL_TGT: Unary.sem_valueT conf_tgt st_tgt invst.(tgt) val_tgt = Some gval_tgt>> /\
      <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
  Proof.
  Admitted.
End Rel.
