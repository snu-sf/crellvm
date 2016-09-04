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

  Definition sem_idT (st:State) (invst:t) (id:IdT.t): option GenericValue :=
    lookupAL _ (sem_tag st invst id.(fst)) id.(snd).

  Definition sem_valueT (conf:Config) (st:State) (invst:t) (v:ValueT.t): option GenericValue :=
    match v with
    | ValueT.id id => sem_idT st invst id
    | ValueT.const c => const2GV conf.(CurTargetData) conf.(Globals) c
    end.

  (* TODO. cf. old's `coq/hint/hint_sem.v` *)
  Definition sem_expr (conf:Config) (st:State) (invst:t) (e:Expr.t): option GenericValue.
  Admitted.

  Definition sem_lessdef (conf:Config) (st:State) (invst:t) (es:ExprPair.t): Prop :=
    forall val2 (VAL2: sem_expr conf st invst es.(snd) = Some val2),
    exists val1,
      <<VAL1: sem_expr conf st invst es.(fst) = Some val1>> /\
      <<VAL: GVs.lessdef val1 val2>>.

  Definition sem_diffblock (conf:Config) (val1 val2:GenericValue): Prop :=
    match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val1,
          GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val2 with
    | Some (Vptr b1 _), Some (Vptr b2 _) => b1 <> b2
    | _, _ => True
    end.

  (* TODO (NOALIAS): (gptr1, ptr1.(snd)) is not aliased with (gptr2, ptr2.(snd)). *)
  Inductive sem_alias (conf:Config) (st:State) (invst:t) (arel:Invariant.aliasrel): Prop :=
  | sem_alias_intro
      (DIFFBLOCK:
         forall val1 gval1
           val2 gval2
           (MEM: ValueTPairSet.mem (val1, val2) arel.(Invariant.diffblock))
           (VAL1: sem_valueT conf st invst val1 = Some gval1)
           (VAL2: sem_valueT conf st invst val2 = Some gval2),
           sem_diffblock conf gval1 gval2)
      (NOALIAS:
         forall ptr1 gptr1
           ptr2 gptr2
           (MEM: PtrPairSet.mem (ptr1, ptr2) arel.(Invariant.noalias))
           (VAL1: sem_valueT conf st invst ptr1.(fst) = Some gptr1)
           (VAL2: sem_valueT conf st invst ptr2.(fst) = Some gptr2),
           False)
  .

  Inductive sem_unique (conf:Config) (st:State) (invst:t) (a:atom): Prop :=
  | sem_unique_intro
      val
      (VAL: lookupAL _ st.(EC).(Locals) a = Some val)
      (LOCALS: forall reg val'
                 (REG: a <> reg)
                 (VAL': lookupAL _ st.(EC).(Locals) reg = Some val'),
          sem_diffblock conf val val')
      (MEM: forall mptr typ align val'
              (LOAD: mload conf.(CurTargetData) st.(Mem) mptr typ align = Some val'),
          sem_diffblock conf val val')
  .

  Definition sem_private (conf:Config) (st:State) (invst:t) (private:list mblock) (a:IdT.t): Prop :=
    forall val (VAL: sem_idT st invst a = Some val),
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
