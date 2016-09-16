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
Require Import TODO.

Set Implicit Arguments.

(* TODO: m_src, m_tgt, conf_src, conf_tgt *)
Inductive valid_conf
          (m_src m_tgt:module)
          (conf_src conf_tgt:Config): Prop :=
| valid_conf_intro
    (INJECT: inject_conf conf_src conf_tgt)
.

(* TODO: move to somewhere *)
(* in this file and SoundImplies.v *)
Ltac solve_bool_true :=
  repeat
    (try match goal with
         | [H: andb ?a ?b = true |- _] =>
           apply andb_true_iff in H; des
         | [H: orb ?a ?b = true |- _] =>
           apply orb_true_iff in H; des
         | [H: proj_sumbool (ValueTSetFacts.eq_dec ?a ?b) = true |- _] =>
           destruct (ValueTSetFacts.eq_dec a b)
         end;
     try subst; ss; unfold is_true in *; unfold sflib.is_true in *).

Module Unary.
  Structure t := mk {
    previous: GVsMap;
    ghost: GVsMap;
  }.

  Definition update_previous f x :=
    (mk (f x.(previous)) x.(ghost)).

  Definition update_ghost f x :=
    (mk x.(previous) (f x.(ghost))).

  Definition update_both f x :=
    update_ghost f (update_previous f x).

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

  Fixpoint sem_list_valueT (conf:Config) (st:State) (invst:t) (lv:list (sz * ValueT.t)): option (list GenericValue) :=
    match lv with
    | nil => Some nil
    | (_, v) :: lv' =>
      match sem_valueT conf st invst v, sem_list_valueT conf st invst lv' with
      | Some GV, Some GVs => Some (GV::GVs)
      | _, _ => None
      end
    end.

  Definition sem_expr (conf:Config) (st:State) (invst:t) (e:Expr.t): option GenericValue :=
    match e with
    | Expr.bop op bsz v1 v2 =>
      match sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv1, Some gv2 =>
        mbop conf.(CurTargetData) op bsz gv1 gv2
      | _, _ => None
      end
    | Expr.fbop op fp v1 v2 =>
      match sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv1, Some gv2 =>
        mfbop conf.(CurTargetData) op fp gv1 gv2
      | _, _ => None
      end
    | Expr.extractvalue ty1 v1 lc ty2 =>
      match sem_valueT conf st invst v1 with
      | Some gv1 =>
        extractGenericValue conf.(CurTargetData) ty1 gv1 lc
      | None => None
      end
    | Expr.insertvalue ty1 v1 ty2 v2 lc =>
      match sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv1, Some gv2 =>
        insertGenericValue conf.(CurTargetData) ty1 gv1 lc ty2 gv2
      | _, _ => None
      end
    | Expr.gep inb ty1 v1 lsv ty2 =>
      match sem_valueT conf st invst v1, sem_list_valueT conf st invst lsv with
      | Some gv1, Some glsv =>
        gep conf.(CurTargetData) ty1 glsv inb ty2 gv1
      | _, _ => None
      end
    | Expr.trunc op ty1 v ty2 =>
      match sem_valueT conf st invst v with
      | Some gv =>
        mtrunc conf.(CurTargetData) op ty1 ty2 gv
      | _ => None
      end
    | Expr.ext eop ty1 v ty2 =>
      match sem_valueT conf st invst v with
      | Some gv =>
        mext conf.(CurTargetData) eop ty1 ty2 gv
      | None => None
      end
    | Expr.cast cop ty1 v ty2 =>
      match sem_valueT conf st invst v with
      | Some gv => mcast conf.(CurTargetData) cop ty1 ty2 gv
      | None => None
      end
    | Expr.icmp c ty v1 v2 =>
      match sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv1, Some gv2 =>
        micmp conf.(CurTargetData) c ty gv1 gv2
      | _, _ => None
      end
    | Expr.fcmp fc fp v1 v2 =>
      match sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv1, Some gv2 =>
        mfcmp conf.(CurTargetData) fc fp gv1 gv2
      | _, _ => None
      end
    | Expr.select v0 ty v1 v2 =>
      match sem_valueT conf st invst v0,
            sem_valueT conf st invst v1,
            sem_valueT conf st invst v2 with
      | Some gv0, Some gv1, Some gv2 =>
        match GV2int conf.(CurTargetData) Size.One gv0 with
        | Some z =>
          Some (if negb (zeq z 0) then gv1 else gv2)
        | _ => None
        end
      | _, _, _ => None
      end
    | Expr.value v =>
      sem_valueT conf st invst v
    | Expr.load v ty a =>
      match sem_valueT conf st invst v with
      | Some gvp =>
        mload conf.(CurTargetData) st.(Mem) gvp ty a
      | None => None
      end
    end.

  Definition sem_lessdef (conf:Config) (st:State) (invst:t) (es:ExprPair.t): Prop :=
    forall val1 (VAL1: sem_expr conf st invst es.(fst) = Some val1),
    exists val2,
      <<VAL2: sem_expr conf st invst es.(snd) = Some val2>> /\
      <<VAL: GVs.lessdef val1 val2>>.

  Definition sem_diffblock (conf:Config) (val1 val2:GenericValue): Prop :=
    match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val1,
          GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val2 with
    | Some (Vptr b1 _), Some (Vptr b2 _) => b1 <> b2
    | _, _ => True
    end.

  Definition NOALIAS_TODO: Prop. Admitted.

  Definition sem_noalias (conf:Config) (val1 val2:GenericValue) (ty1 ty2:typ): Prop :=
    match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val1,
          GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val2 with
    | Some (Vptr b1 ofs1), Some (Vptr b2 ofs2) =>
      forall
        size1 size2
        (BLOCK: b1 = b2)
        (* TODO: getTypeSizeInBits, storesize, or allocsize for size? *)
        (SIZE1: getTypeSizeInBits conf.(CurTargetData) ty1 = Some size1)
        (SIZE2: getTypeSizeInBits conf.(CurTargetData) ty2 = Some size2),
        NOALIAS_TODO
        (* [Int.signed (31%nat) ofs1, Int.signed (31%nat) ofs1 + size1) disjoint *)
        (* [Int.signed (31%nat) ofs2, Int.signed (31%nat) ofs2 + size2) *)
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
           sem_noalias conf gptr1 gptr2 ptr1.(snd) ptr2.(snd))
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
    unfold Invariant.is_empty_unary in EMPTY.
    solve_bool_true.
    econs.
    - ii. apply ExprPairSet.is_empty_2 in EMPTY.
      exfalso. eapply EMPTY; eauto.
    - admit. (* TODO: sem_alias *)
    - ii. apply AtomSetImpl.is_empty_2 in EMPTY1.
      exfalso. eapply EMPTY1; eauto.
    - ii. apply IdTSet.is_empty_2 in EMPTY0.
      exfalso. eapply EMPTY0; eauto.
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

  Definition update_src f x :=
    (mk (f x.(src)) x.(tgt)).

  Definition update_tgt f x :=
    (mk x.(src) (f x.(tgt))).

  Definition update_both f x :=
    update_src f (update_tgt f x).

  Definition sem_inject (st_src st_tgt:State) (invst:t) (inject:meminj) (id:IdT.t): Prop :=
    forall val_src (VAL_SRC: Unary.sem_idT st_src invst.(src) id = Some val_src),
    exists val_tgt,
      <<VAL_TGT: Unary.sem_idT st_tgt invst.(tgt) id = Some val_tgt>> /\
      <<VAL: genericvalues_inject.gv_inject inject val_src val_tgt>>.

  Inductive sem (conf_src conf_tgt:Config) (st_src st_tgt:State) (invst:t) (invmem:InvMem.Rel.t) (inv:Invariant.t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src st_src invst.(src) invmem.(InvMem.Rel.src) inv.(Invariant.src))
      (TGT: Unary.sem conf_tgt st_tgt invst.(tgt) invmem.(InvMem.Rel.tgt) inv.(Invariant.tgt))
      (MAYDIFF:
         forall id (NOTIN: (IdTSet.mem id inv.(Invariant.maydiff)) = false),
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
      exploit LOCALS; eauto.
  Qed.

  (* TODO: position *)
  Lemma not_in_maydiff_sem1
        inv id
        (NIMD: Invariant.not_in_maydiff inv (Exprs.ValueT.id id) = true):
    <<NOT_IN: (IdTSet.mem id (Invariant.maydiff inv)) = false>>.
  Proof.
    ii. apply negb_true_iff in NIMD.
    rewrite NIMD. ss.
  Qed.

  (* TODO: position *)
  Lemma not_in_maydiff_sem2
        inv id
        (NOT_IN: (IdTSet.mem id (Invariant.maydiff inv) = false)):
  <<NIMD: Invariant.not_in_maydiff inv (Exprs.ValueT.id id) = true>>.
  Proof.
    destruct id; ss.
    rewrite NOT_IN. ss.
  Qed.

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
    unfold Invariant.inject_value in INJECT.
    solve_bool_true.
    - inv STATE.
      destruct val_tgt.
      + apply not_in_maydiff_sem1 in INJECT0. des.
        exploit MAYDIFF; eauto.
      + esplits.
        * ss. admit. (* targetdata & globals *)
        * admit. (* will be same *)
    - inv STATE. inv TGT.
      (* apply ExprPairSet.mem_2 in INJECT. *)
      (* exploit LESSDEF; eauto. ss. *)
      (* apply LESSDEF in INJECT. *)
      (* Unary.sem_lessdef *)
      (* { ss.  *)
      (*   ExprPairSet.In *)
      (* ExprPairSet.For_all *)
      (* eapply LESSDEF in INJECT. *)
      admit. (* TODO: Unary.sem_lessdef *)
    - admit. (* ditto *)
    - admit. (* ditto *)
  Admitted.

  Lemma eqb_forallb2 {X} x_eqb (xs: list X) xs2
        (EQB_SPEC: forall x x2, x_eqb x x2 = true -> x = x2)
        (EQB_FORALLB: list_forallb2 x_eqb xs xs2 = true):
    <<EQ: xs = xs2>>.
  Proof.
    generalize dependent xs2.
    induction xs; ii; red; des; ss; destruct xs2; ss.
    des_bool; des.
    apply EQB_SPEC in EQB_FORALLB.
    apply IHxs in EQB_FORALLB0. des.
    clarify.
  Qed.

  Lemma inject_expr_spec
        m_src conf_src st_src expr_src
        m_tgt conf_tgt st_tgt expr_tgt
        invst invmem inv
        gval_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (STATE: sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
        (INJECT: Hints.Invariant.inject_expr inv expr_src expr_tgt)
        (VAL_SRC: Unary.sem_expr conf_src st_src invst.(src) expr_src = Some gval_src):
    exists gval_tgt,
      <<VAL_TGT: Unary.sem_expr conf_tgt st_tgt invst.(tgt) expr_tgt = Some gval_tgt>> /\
      <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
  Proof.
    unfold Invariant.inject_expr in INJECT. unfold Invariant.deep_check_expr in INJECT. des_bool; des.
    inv CONF. inv INJECT1.
    Ltac exploit_inject_value_spec_with x :=
      match (type of x) with
      | (Unary.sem_valueT _ _ _ _ = Some _) =>
        (exploit inject_value_spec; [| | | exact x |]; eauto; ii; des)
      (* | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) => *)
      (*   (exploit clear_unary_preserved_list_valueT; [exact x| |]; eauto; ii; des) *)
      end.
    assert(EQB_SPEC := Decs.const_eqb_spec).
    Time destruct expr_src, expr_tgt;
      inv INJECT; (* only 13 will remain from 169 *)
      repeat (des_bool; des; ss);
      des_ifs; (all_once exploit_inject_value_spec_with);
        des_sumbool; subst; ss;
          try (rewrite <- TARGETDATA);
          try (exploit (@eqb_forallb2 const); eauto; ii; des; []);
          clarify.
    - exploit genericvalues_inject.simulation__mbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__extractGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__insertGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__GEP; try apply VAL_SRC; eauto; ii; des; eauto.
      (* exploit genericvalues_inject.simulation__mgep; try apply VAL_SRC; eauto; ii; des; eauto. *)
      esplits; eauto.
      admit.
      admit.
    -
      idtac.
  (* Heq2 : Unary.sem_list_valueT conf_src st_src (src invst) lsv = ret l0 *)
  (* INJECT1 : list_forallb2 (Invariant.inject_value inv) (List.map snd lsv) (List.map snd lsv0) = true *)
  (* Heq0 : Unary.sem_list_valueT conf_tgt st_tgt (tgt invst) lsv0 = merror *)
      admit.
    - exploit genericvalues_inject.simulation__mtrunc; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mext; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mcast; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__micmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfcmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - esplits; eauto.
    - admit.
  (* Heq7 : GV2int (CurTargetData conf_src) Size.One g2 = ret z2 *)
  (* Heq2 : GV2int (CurTargetData conf_tgt) Size.One g = ret z1 *)
  (* Heq3 : negb (zeq z1 0) = true *)
  (* Heq8 : negb (zeq z2 0) = false *)
  (* INJECT5 : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g2 g *)
    - admit.
      (* same as above *)
    - esplits; eauto.
    -
  (* Heq6 : GV2int (CurTargetData conf_src) Size.One g2 = ret z1 *)
  (* Heq2 : GV2int (CurTargetData conf_tgt) Size.One g = merror *)
  (* INJECT5 : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g2 g *)
      admit.
    -
  (* Heq6 : GV2int (CurTargetData conf_src) Size.One g2 = ret z1 *)
  (* Heq2 : GV2int (CurTargetData conf_tgt) Size.One g = merror *)
  (* INJECT5 : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g2 g *)
      admit.
    - (* There exists lemma for mload_aux *)
      (* exploit genericvalues_inject.simulation__mload; try apply VAL_SRC; eauto; ii; des; eauto. *)
  Admitted.
End Rel.

(* 2 focused subgoals *)
(* (unfocused: 13, shelved: 3), subgoal 1 (ID 386956) *)

(*   m_src : module *)
(*   conf_src : Config *)
(*   st_src : State *)
(*   v : ValueT.t *)
(*   lsv : list (sz * ValueT.t) *)
(*   m_tgt : module *)
(*   conf_tgt : Config *)
(*   st_tgt : State *)
(*   ib0 : inbounds *)
(*   t1 : typ *)
(*   v0 : ValueT.t *)
(*   lsv0 : list (sz * ValueT.t) *)
(*   u0 : typ *)
(*   invst : t *)
(*   invmem : InvMem.Rel.t *)
(*   inv : Invariant.t *)
(*   gval_src : GenericValue *)
(*   STATE : sem conf_src conf_tgt st_src st_tgt invst invmem inv *)
(*   MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st_src) (Mem st_tgt) invmem *)
(*   INJECT0 : Invariant.inject_value inv v v0 = true *)
(*   INJECT1 : list_forallb2 (Invariant.inject_value inv) (List.map snd lsv) (List.map snd lsv0) = true *)
(*   g0 : GenericValue *)
(*   Heq1 : Unary.sem_valueT conf_src st_src (src invst) v = ret g0 *)
(*   l1 : list GenericValue *)
(*   Heq2 : Unary.sem_list_valueT conf_src st_src (src invst) lsv = ret l1 *)
(*   TARGETDATA : CurTargetData conf_src = CurTargetData conf_tgt *)
(*   GLOBALS : Globals conf_src = Globals conf_tgt *)
(*   EQB_SPEC : forall c1 c2 : const, Decs.const_eqb c1 c2 -> c1 = c2 *)
(*   H2 : List.map fst lsv = List.map fst lsv0 *)
(*   g : GenericValue *)
(*   l0 : list GenericValue *)
(*   Heq0 : Unary.sem_list_valueT conf_tgt st_tgt (tgt invst) lsv0 = ret l0 *)
(*   VAL_SRC : gep (CurTargetData conf_src) t1 l1 ib0 u0 g0 = ret gval_src *)
(*   VAL_TGT : Unary.sem_valueT conf_tgt st_tgt (tgt invst) v0 = ret g *)
(*   INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g0 g *)
(*   ============================ *)
(*   genericvalues_inject.wf_sb_mi ?Goal12 (InvMem.Rel.inject invmem) ?Goal13 ?Goal14 *)

(* subgoal 2 (ID 386878) is: *)
(*  genericvalues_inject.gvs_inject (InvMem.Rel.inject invmem) l1 l0 *)





(* GEPPPPPPPPPPPPPPPPPPPPPPP *)
(* 2 focused subgoals *)
(* (unfocused: 13, shelved: 3), subgoal 1 (ID 257388) *)

(*   m_src : module *)
(*   conf_src : Config *)
(*   st_src : State *)
(*   v : ValueT.t *)
(*   lsv : list (sz * ValueT.t) *)
(*   m_tgt : module *)
(*   conf_tgt : Config *)
(*   st_tgt : State *)
(*   ib0 : inbounds *)
(*   t1 : typ *)
(*   v0 : ValueT.t *)
(*   lsv0 : list (sz * ValueT.t) *)
(*   u0 : typ *)
(*   invst : t *)
(*   invmem : InvMem.Rel.t *)
(*   inv : Invariant.t *)
(*   gval_src : GenericValue *)
(*   STATE : sem conf_src conf_tgt st_src st_tgt invst invmem inv *)
(*   MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st_src) (Mem st_tgt) invmem *)
(*   INJECT0 : Invariant.inject_value inv v v0 = true *)
(*   INJECT1 : list_forallb2 (Invariant.inject_value inv) (List.map snd lsv) (List.map snd lsv0) = true *)
(*   g0 : GenericValue *)
(*   Heq1 : Unary.sem_valueT conf_src st_src (src invst) v = ret g0 *)
(*   l1 : list GenericValue *)
(*   Heq2 : Unary.sem_list_valueT conf_src st_src (src invst) lsv = ret l1 *)
(*   TARGETDATA : CurTargetData conf_src = CurTargetData conf_tgt *)
(*   GLOBALS : Globals conf_src = Globals conf_tgt *)
(*   H2 : List.map fst lsv = List.map fst lsv0 *)
(*   g : GenericValue *)
(*   l0 : list GenericValue *)
(*   Heq0 : Unary.sem_list_valueT conf_tgt st_tgt (tgt invst) lsv0 = ret l0 *)
(*   VAL_SRC : gep (CurTargetData conf_src) t1 l1 ib0 u0 g0 = ret gval_src *)
(*   VAL_TGT : Unary.sem_valueT conf_tgt st_tgt (tgt invst) v0 = ret g *)
(*   INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g0 g *)
(*   ============================ *)
(*   genericvalues_inject.wf_sb_mi ?Goal14 (InvMem.Rel.inject invmem) ?Goal15 ?Goal16 *)

(* subgoal 2 (ID 257312) is: *)
(*  genericvalues_inject.gvs_inject (InvMem.Rel.inject invmem) l1 l0 *)
