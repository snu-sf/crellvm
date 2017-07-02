Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import sflib.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Require Import memory_props.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require Import Inject.
Require InvMem.
Require Import TODO.
Require Import paco.
Require Import TODOProof.
Require Import OpsemAux.

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

Lemma get_lhs_in_spec
      ld (rhs: Expr.t) x
  (LHS: ExprPairSet.In x (Invariant.get_lhs ld rhs)):
  (snd x) = rhs /\ ExprPairSet.In x ld.
Proof.
  unfold Invariant.get_lhs, flip in *.
  rewrite ExprPairSetFacts.filter_iff in LHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma get_rhs_in_spec
      ld (lhs: Expr.t) x
  (RHS: ExprPairSet.In x (Invariant.get_rhs ld lhs)):
  (fst x) = lhs /\ ExprPairSet.In x ld.
Proof.
  unfold Invariant.get_rhs, flip in *.
  rewrite ExprPairSetFacts.filter_iff in RHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma get_rhs_in_spec2
      (ld: ExprPairSet.t) (lhs: Expr.t) (x: Expr.t * Expr.t)
      (LHS: fst x = lhs)
      (IN: ExprPairSet.In x ld)
  : ExprPairSet.In x (Invariant.get_rhs ld lhs).
Proof.
  i. des.
  unfold Invariant.get_rhs, flip.
  apply ExprPairSet.filter_3; try by solve_compat_bool.
  subst.
  unfold proj_sumbool.
  des_ifs.
Qed.

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
    list_disjoint (GV2blocks val1) (GV2blocks val2).

  Definition sem_noalias (conf:Config) (val1 val2:GenericValue) (ty1 ty2:typ): Prop :=
    list_disjoint (GV2blocks val1) (GV2blocks val2).
    (* TODO *)
    (* match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val1, *)
    (*       GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val2 with *)
    (* | Some (Vptr b1 ofs1), Some (Vptr b2 ofs2) => b1 <> b2 *)
    (*   (* forall *) *)
    (*   (*   size1 size2 *) *)
    (*   (*   (BLOCK: b1 = b2) *) *)
    (*   (*   (* TODO: getTypeSizeInBits, storesize, or allocsize for size? *) *) *)
    (*   (*   (SIZE1: getTypeSizeInBits conf.(CurTargetData) ty1 = Some size1) *) *)
    (*   (*   (SIZE2: getTypeSizeInBits conf.(CurTargetData) ty2 = Some size2), *) *)
    (*   (*   .. *) *)
    (*   (*   (* [Int.signed (31%nat) ofs1, Int.signed (31%nat) ofs1 + size1) disjoint *) *) *)
    (*   (*   (* [Int.signed (31%nat) ofs2, Int.signed (31%nat) ofs2 + size2) *) *) *)
    (* | _, _ => True *)
    (* end. *)

  Lemma diffblock_comm
        conf gv1 gv2
        (DIFFBLOCK: sem_diffblock conf gv1 gv2)
    : sem_diffblock conf gv2 gv1.
  Proof.
    eapply list_disjoint_comm; eauto.
  Qed.

  Lemma undef_diffblock
        conf (gv1: GenericValue) gv2
        (* (UNDEF: List.Forall (fun x => x.(fst) = Vundef) gv1) *)
        (UNDEF: forall v mc, In (v, mc) gv1 -> v = Vundef)
    :
      <<DIFFBLOCK: sem_diffblock conf gv1 gv2>>.
  Proof.
    induction gv2; ii; des; ss.
    cut(GV2blocks gv1 = []).
    { clarify. ii. rewrite H1 in *. ss. }
    clear - UNDEF.
    induction gv1; ii; ss.
    destruct a; ss.
    exploit UNDEF; eauto; []; ii; des.
    subst.
    exploit IHgv1; eauto.
  Qed.

  Lemma noalias_comm
        conf gv1 gv2 ty1 ty2
        (NOALIAS: sem_noalias conf gv1 gv2 ty1 ty2)
    : sem_noalias conf gv2 gv1 ty2 ty1.
  Proof.
    eapply list_disjoint_comm; eauto.
  Qed.

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

  Inductive sem_unique (conf:Config) (st:State) (gmax:positive) (a:atom) : Prop :=
  | sem_unique_intro
      val
      (VAL: lookupAL _ st.(EC).(Locals) a = Some val)
      (LOCALS: forall reg val'
                 (REG: a <> reg)
                 (VAL': lookupAL _ st.(EC).(Locals) reg = Some val'),
          sem_diffblock conf val val')
      (MEM:
         forall mptr typ align val'
           (LOAD: mload conf.(CurTargetData) st.(Mem) mptr typ align = Some val'),
           sem_diffblock conf val val')
      (GLOBALS:
         forall b
           (GV2BLOCKS: In b (GV2blocks val)),
           (gmax < b)%positive)
  .

  Definition sem_private (conf:Config) (st:State) (invst:t)
             (private_parent:list mblock) (public:mblock -> Prop) (a:IdT.t): Prop :=
    forall b val
           (VAL: sem_idT st invst a = Some val)
           (IN: In b (GV2blocks val)),
      <<PRIVATE_BLOCK: InvMem.private_block st.(Mem) public b>> /\
                       <<PARENT_DISJOINT: ~ In b private_parent>>
  .
      (* In b private. *)
      (* match GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) val with *)
      (* | ret Vptr b _ => In b private *)
      (* | _ => False *)
      (* end. *)

  Inductive sem (conf:Config) (st:State) (invst:t) (invmem:InvMem.Unary.t) (gmax:positive) (public:mblock -> Prop) (inv:Invariant.unary): Prop :=
  | sem_intro
      (LESSDEF: ExprPairSet.For_all (sem_lessdef conf st invst) inv.(Invariant.lessdef))
      (NOALIAS: sem_alias conf st invst inv.(Invariant.alias))
      (UNIQUE: AtomSetImpl.For_all (sem_unique conf st gmax) inv.(Invariant.unique))
      (PRIVATE: IdTSet.For_all (sem_private conf st invst invmem.(InvMem.Unary.private_parent) public) inv.(Invariant.private))
      (ALLOCAS_PARENT: list_disjoint st.(EC).(Allocas) invmem.(InvMem.Unary.private_parent))
      (ALLOCAS_VALID: List.Forall (Mem.valid_block st.(Mem)) st.(EC).(Allocas))
      (WF_LOCAL: MemProps.wf_lc st.(Mem) st.(EC).(Locals))
      (WF_PREVIOUS: MemProps.wf_lc st.(Mem) invst.(previous))
      (WF_GHOST: MemProps.wf_lc st.(Mem) invst.(ghost))
      (UNIQUE_PARENT_LOCAL:
         forall x ptr
           (PTR:lookupAL _ st.(EC).(Locals) x = Some ptr),
           InvMem.gv_diffblock_with_blocks conf ptr invmem.(InvMem.Unary.unique_parent))
      (WF_FDEF: wf_fdef conf.(CurSystem) conf st.(EC).(CurFunction))
      (WF_EC: wf_EC st.(EC))
  .

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
      <<VAL: genericvalues_inject.gv_inject inject val_src val_tgt>>
  .

  Inductive inject_allocas (f: meminj): list mblock -> list mblock -> Prop :=
  | inject_allocas_nil: inject_allocas f [] []
  | inject_allocas_alloca_nop
      al
      (PRIVATE: f al = None)
      als_src als_tgt
      (INJECT: inject_allocas f als_src als_tgt)
    :
      inject_allocas f (al :: als_src) als_tgt
  | inject_allocas_nop_alloca
      al
      (PRIVATE: forall b ofs, f b <> Some (al, ofs))
      als_src als_tgt
      (INJECT: inject_allocas f als_src als_tgt)
    :
      inject_allocas f als_src (al :: als_tgt)
  | inject_allocas_alloca_alloca
      al_src al_tgt
      (PUBLIC: f al_src = Some (al_tgt, 0))
      als_src als_tgt
      (INJECT: inject_allocas f als_src als_tgt)
    :
      inject_allocas f (al_src :: als_src) (al_tgt :: als_tgt)
  .

  Definition sem_inject_expr (conf_src conf_tgt: Config)
             (st_src st_tgt:State) (invst:t) (inject:meminj) (expr:Expr.t): Prop :=
    forall val_src (VAL_SRC: Unary.sem_expr conf_src st_src invst.(src) expr = Some val_src),
    exists val_tgt,
      <<VAL_TGT: Unary.sem_expr conf_tgt st_tgt invst.(tgt) expr = Some val_tgt>> /\
      <<VAL: genericvalues_inject.gv_inject inject val_src val_tgt>>.

  Inductive sem (conf_src conf_tgt:Config) (st_src st_tgt:State) (invst:t) (invmem:InvMem.Rel.t) (inv:Invariant.t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src st_src invst.(src) invmem.(InvMem.Rel.src) invmem.(InvMem.Rel.gmax) (InvMem.Rel.public_src invmem.(InvMem.Rel.inject)) inv.(Invariant.src))
      (TGT: Unary.sem conf_tgt st_tgt invst.(tgt) invmem.(InvMem.Rel.tgt) invmem.(InvMem.Rel.gmax) (InvMem.Rel.public_tgt invmem.(InvMem.Rel.inject)) inv.(Invariant.tgt))
      (MAYDIFF:
         forall id (NOTIN: (IdTSet.mem id inv.(Invariant.maydiff)) = false),
           sem_inject st_src st_tgt invst invmem.(InvMem.Rel.inject) id)
      (ALLOCAS:
         inject_allocas invmem.(InvMem.Rel.inject) st_src.(EC).(Allocas) st_tgt.(EC).(Allocas))
  .

  Lemma inject_allocas_preserved_aux
        invmem0
        als_src als_tgt
        (INJECT: inject_allocas invmem0.(InvMem.Rel.inject) als_src als_tgt)
        invmem1
        (INJECT_INCR: inject_incr invmem0.(InvMem.Rel.inject) invmem1.(InvMem.Rel.inject))
        bd_src bd_tgt
        (FROZEN: InvMem.Rel.frozen invmem0.(InvMem.Rel.inject) invmem1.(InvMem.Rel.inject)
                                             bd_src bd_tgt)
        (VALID_SRC: List.Forall (fun x => (x < bd_src)%positive) als_src)
        (VALID_TGT: List.Forall (fun x => (x < bd_tgt)%positive) als_tgt)
    :
        <<INJECT: inject_allocas invmem1.(InvMem.Rel.inject) als_src als_tgt>>
  .
  Proof.
    ginduction INJECT; ii; ss.
    - econs; eauto.
    - inv VALID_SRC.
      econs; eauto.
      + erewrite <- InvMem.Rel.frozen_preserves_src; eauto.
      + eapply IHINJECT; eauto.
    - inv VALID_TGT.
      econs; eauto.
      + ii.
        exploit InvMem.Rel.frozen_preserves_tgt; eauto; []; i; des.
        exploit PRIVATE; eauto.
      + eapply IHINJECT; eauto.
    - inv VALID_SRC. inv VALID_TGT.
      econs 4; eauto.
      + eapply IHINJECT; eauto.
  Qed.

  Lemma inject_allocas_preserved_le
        invmem0
        als_src als_tgt
        (INJECT: inject_allocas invmem0.(InvMem.Rel.inject) als_src als_tgt)
        invmem1
        (LE: InvMem.Rel.le invmem0 invmem1)
        (VALID_SRC: List.Forall
                      (Mem.valid_block invmem0.(InvMem.Rel.src).(InvMem.Unary.mem_parent)) als_src)
        (VALID_TGT: List.Forall
                      (Mem.valid_block invmem0.(InvMem.Rel.tgt).(InvMem.Unary.mem_parent)) als_tgt)
    :
        <<INJECT: inject_allocas invmem1.(InvMem.Rel.inject) als_src als_tgt>>
  .
  Proof.
    eapply inject_allocas_preserved_aux; try exact INJECT; try eassumption.
    { apply LE. }
    { apply LE. }
  Qed.

  Lemma inject_allocas_preserved_le_lift
        m_src0 m_tgt0 invmem0
        als_src als_tgt
        (INJECT: inject_allocas invmem0.(InvMem.Rel.inject) als_src als_tgt)
        invmem1
        arg0 arg1 arg2 arg3
        (LE: InvMem.Rel.le (InvMem.Rel.lift m_src0 m_tgt0 arg0 arg1 arg2 arg3 invmem0) invmem1)
        (VALID_SRC: List.Forall (Mem.valid_block m_src0) als_src)
        (VALID_TGT: List.Forall (Mem.valid_block m_tgt0) als_tgt)
        (PARENT_LE_SRC: ((Mem.nextblock (InvMem.Unary.mem_parent (InvMem.Rel.src invmem0)) <=
                          Mem.nextblock (InvMem.Unary.mem_parent (InvMem.Rel.src invmem1))))%positive)
        (PARENT_LE_TGT: ((Mem.nextblock (InvMem.Unary.mem_parent (InvMem.Rel.tgt invmem0)) <=
                          Mem.nextblock (InvMem.Unary.mem_parent (InvMem.Rel.tgt invmem1))))%positive)
    :
        <<INJECT: inject_allocas invmem1.(InvMem.Rel.inject) als_src als_tgt>>
  .
  Proof.
    eapply inject_allocas_preserved_aux; try exact INJECT; try eassumption.
    { apply LE. }
    { inv LE; ss. }
  Qed.

  Lemma const2GV_gv_inject_refl
        TD globals cnst gv meminj
        (CONST: const2GV TD globals cnst = ret gv)
        gmax mem_src mem_tgt
        (WASABI: genericvalues_inject.wf_sb_mi gmax meminj mem_src mem_tgt)
        (WF_GLOBALS: genericvalues_inject.wf_globals gmax globals)
    :
    <<REFL: genericvalues_inject.gv_inject meminj gv gv>>.
  Proof.
    eapply const2GV_inject; eauto.
  Qed.

  Lemma not_in_maydiff_value_spec
        inv invmem invst
        m_src conf_src st_src
        m_tgt conf_tgt st_tgt
        val gv_val_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (NIMD: Invariant.not_in_maydiff inv val = true)
        (MAYDIFF: forall id : Tag.t * id,
            IdTSet.mem id (Invariant.maydiff inv) = false ->
            sem_inject st_src st_tgt invst (InvMem.Rel.inject invmem) id)
        (VAL_SRC: Unary.sem_valueT conf_src st_src (src invst) val = ret gv_val_src)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
    :
    exists gv_val_tgt, Unary.sem_valueT conf_tgt st_tgt (tgt invst) val = ret gv_val_tgt /\
                       genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) gv_val_src gv_val_tgt.
  Proof.
    inv CONF. inv INJECT.
    destruct val; repeat (ss; des_bool; des).
    - exploit MAYDIFF; eauto.
    - esplits.
      + rewrite <- TARGETDATA, <- GLOBALS. eauto.
      + eapply const2GV_gv_inject_refl; eauto.
        apply MEM.
        apply MEM.
  Qed.

  Lemma not_in_maydiff_list_value_spec
        inv invmem invst
        m_src conf_src st_src
        m_tgt conf_tgt st_tgt
        vals gv_vals_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (NIMD: forallb (Invariant.not_in_maydiff inv) (List.map snd vals) = true)
        (MAYDIFF: forall id : Tag.t * id,
            IdTSet.mem id (Invariant.maydiff inv) = false ->
            sem_inject st_src st_tgt invst (InvMem.Rel.inject invmem) id)
        (VAL_SRC: Unary.sem_list_valueT conf_src st_src (src invst) vals = ret gv_vals_src)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
    :
    exists gv_vals_tgt,
      Unary.sem_list_valueT conf_tgt st_tgt (tgt invst) vals = ret gv_vals_tgt /\
      list_forall2 (genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject)) gv_vals_src gv_vals_tgt.
  Proof.
    revert gv_vals_src VAL_SRC.
    induction vals; ss; i; inv VAL_SRC.
    - esplits; eauto. econs.
    - destruct a. simtac.
      exploit not_in_maydiff_value_spec; eauto. i. des.
      exploit IHvals; eauto. i. des.
      rewrite H0, H3. esplits; eauto. econs; eauto.
  Qed.

  (* company-coq extracted *)
  (* C-c C-a C-x *)
  Lemma not_in_maydiff_load:
    forall (inv : Invariant.t) (invmem : InvMem.Rel.t) (invst : t)
           (m_src : module) (conf_src : Config) (st_src : State)
           (m_tgt : module) (conf_tgt : Config) (st_tgt : State)
           (v : ValueT.t) (t0 : typ) (a : align) (gv_expr_src : GenericValue),
      valid_conf m_src m_tgt conf_src conf_tgt ->
      Invariant.not_in_maydiff inv v = true ->
      (forall id : Tag.t * id,
          IdTSet.mem id (Invariant.maydiff inv) = false ->
          sem_inject st_src st_tgt invst (InvMem.Rel.inject invmem) id) ->
      forall g0 : GenericValue,
        Unary.sem_valueT conf_src st_src (src invst) v = ret g0 ->
        mload (CurTargetData conf_tgt) (Mem st_src) g0 t0 a = ret gv_expr_src ->
        InvMem.Rel.sem conf_src conf_tgt (Mem st_src) (Mem st_tgt) invmem ->
        CurTargetData conf_src = CurTargetData conf_tgt ->
        Globals conf_src = Globals conf_tgt ->
        forall g : GenericValue,
          Unary.sem_valueT conf_tgt st_tgt (tgt invst) v = ret g ->
          genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g0 g ->
          exists gv_expr_tgt : GenericValue,
            mload (CurTargetData conf_tgt) (Mem st_tgt) g t0 a = ret gv_expr_tgt /\
            genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) gv_expr_src
                                           gv_expr_tgt.
  Proof.
    intros inv invmem invst m_src conf_src st_src m_tgt conf_tgt st_tgt v t0 a
           gv_expr_src CONF NIMD MAYDIFF g0 Heq0 VAL_SRC MEM
           TARGETDATA GLOBALS g H H0.
    eapply mload_inv in VAL_SRC; eauto; []; ii; des.
    clarify.
    inv MEM. clear SRC TGT.
    rename b into __b__.
    inv H0. inv H6.
    destruct invmem. cbn in *.
    inv H5. cbn in *.
    exploit genericvalues_inject.simulation_mload_aux;
      try apply VAL_SRC; eauto; []; ii; des; eauto.
    esplits; eauto.
    des_ifs. rewrite <- H0.
    (* not to spill inv contents outside of assertion proof *)
    replace delta with 0 in *; cycle 1.
    {
      (* really weird *)
      inv WF.
      exploit mi_range_block; eauto.
    }
    replace (Int.signed 31 (Int.add 31 ofs (Int.repr 31 0)))
            with (Int.signed 31 ofs + 0); ss.
    clear - ofs.
    rewrite Z.add_comm. ss.
    apply int_add_0.
  Qed.

  Lemma inject_expr_load
        (m_src : module)
        (conf_src : Config)
        (st_src : State)
        (v : ValueT.t)
        (m_tgt : module)
        (conf_tgt : Config)
        (st_tgt : State)
        (v0 : ValueT.t)
        (t1 : typ)
        (a0 : align)
        (invst : t)
        (invmem : InvMem.Rel.t)
        (inv : Invariant.t)
        (gval_src : GenericValue)
        (STATE : sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st_src) (Mem st_tgt) invmem)
        (INJECT0 : Invariant.inject_value inv v v0 = true)
        (g0 : GenericValue)
        (Heq0 : Unary.sem_valueT conf_src st_src (src invst) v = ret g0)
        (CONF_DUP : valid_conf m_src m_tgt conf_src conf_tgt)
        (TARGETDATA : CurTargetData conf_src = CurTargetData conf_tgt)
        (GLOBALS : Globals conf_src = Globals conf_tgt)
        (EQB_SPEC : forall c1 c2 : const, Decs.const_eqb c1 c2 -> c1 = c2)
        (g : GenericValue)
        (VAL_SRC : mload (CurTargetData conf_src) (Mem st_src) g0 t1 a0 = ret gval_src)
        (VAL_TGT : Unary.sem_valueT conf_tgt st_tgt (tgt invst) v0 = ret g)
        (INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) g0 g)
    :
      exists gval_tgt : GenericValue,
        (<<VAL_TGT: mload (CurTargetData conf_src) (Mem st_tgt) g t1 a0 = ret gval_tgt >>) /\
        (<<INJECT: genericvalues_inject.gv_inject (InvMem.Rel.inject invmem)
                                                  gval_src gval_tgt >>)
  .
  Proof.
    eapply mload_inv in VAL_SRC; eauto; []; ii; des.
    clarify.
    inv MEM. clear SRC TGT.
    rename b into __b__.
    inv INJECT. inv H4.
    destruct invmem. cbn in *.
    inv H3. cbn in *.
    exploit genericvalues_inject.simulation_mload_aux;
      try apply VAL_SRC; eauto; []; ii; des; eauto.
    esplits; eauto.
    des_ifs. rewrite <- H.
    (* not to spill inv contents outside of assertion proof *)
    replace delta with 0 in *; cycle 1.
    {
      (* really weird *)
      inv WF.
      exploit mi_range_block; eauto.
    }
    replace (Int.signed 31 (Int.add 31 ofs (Int.repr 31 0)))
    with (Int.signed 31 ofs + 0); ss.
    clear - ofs.
    rewrite Z.add_comm. ss.
    apply int_add_0.
  Qed.

  (* TODO move lemma position to definition point *)
  Lemma forall_gv_inject_gvs_inject
        invmem l0 l1
        (INJECT: list_forall2
                   (genericvalues_inject.gv_inject
                      (InvMem.Rel.inject invmem)) l0 l1)
    :
      <<INJECTS: genericvalues_inject.gvs_inject
                   (InvMem.Rel.inject invmem) l0 l1>>
  .
  Proof.
    generalize dependent l1.
    induction l0; ii; ss; des; ss.
    - inv INJECT. ss.
    - destruct l1; ss.
      { inv INJECT. }
      inv INJECT.
      exploit IHl0; eauto.
  Qed.

  Lemma not_in_maydiff_expr_spec
        inv invmem invst
        m_src conf_src st_src
        m_tgt conf_tgt st_tgt
        expr gv_expr_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (NIMD: Invariant.not_in_maydiff_expr inv expr = true)
        (MAYDIFF: forall id : Tag.t * id,
            IdTSet.mem id (Invariant.maydiff inv) = false ->
            sem_inject st_src st_tgt invst (InvMem.Rel.inject invmem) id)
        (VAL_SRC: Unary.sem_expr conf_src st_src (src invst) expr
                  = ret gv_expr_src)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
    :
    exists gv_expr_tgt,
      (Unary.sem_expr conf_tgt st_tgt (tgt invst) expr = ret gv_expr_tgt)
      /\ (genericvalues_inject.gv_inject
            (InvMem.Rel.inject invmem) gv_expr_src gv_expr_tgt)
  .
  Proof.
    inversion CONF. inv INJECT.
    unfold Invariant.not_in_maydiff_expr in *.
    Ltac exploit_not_in_maydiff_value_spec_with x :=
      match (type of x) with
      | (Unary.sem_valueT _ _ _ _ = Some _) =>
        (exploit not_in_maydiff_value_spec; [| | | exact x | |]; eauto; ii; des; [])
      end.
    Ltac exploit_not_in_maydiff_list_value_spec_with x :=
      match (type of x) with
      | (Unary.sem_list_valueT _ _ _ _ = Some _) =>
        (exploit not_in_maydiff_list_value_spec; [| | | exact x | |]; eauto; ii; des; [])
      end.
    Ltac exploit_eq_GV2int :=
      let tmp := fresh in
      match goal with
      | [ H1: GV2int ?conf_x _ ?x = _,
          H2: GV2int ?conf_y _ ?y = _,
          TRGTDATA: ?conf_x = ?conf_y,
          INJ: genericvalues_inject.gv_inject _ ?x ?y |- _ ] =>
        exploit genericvalues_inject.simulation__eq__GV2int; try eapply INJ; eauto; intro tmp; des; [];
        rewrite H1 in tmp;
        rewrite TRGTDATA in tmp;
        rewrite H2 in tmp;
        clarify
      end.
    Time destruct expr; ss; repeat (des_bool; des);
      des_ifs; (all_once exploit_not_in_maydiff_value_spec_with); clarify;
        (all_once exploit_not_in_maydiff_list_value_spec_with); clarify;
          try rewrite TARGETDATA in VAL_SRC;
          try exploit_eq_GV2int.
    (* Finished transaction in 39.843 secs (39.67u,0.194s) (successful) *)
    - exploit genericvalues_inject.simulation__mbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__extractGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__insertGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    - inv MEM.
      exploit genericvalues_inject.simulation__GEP; try apply VAL_SRC; eauto; ii; des; eauto.
      apply forall_gv_inject_gvs_inject; ss.
      (* exploit genericvalues_inject.simulation__mgep; try apply VAL_SRC; eauto; ii; des; eauto. *)
    - exploit genericvalues_inject.simulation__mtrunc; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mext; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mcast; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__micmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfcmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - esplits; eauto.
    - esplits; eauto.
    - eapply not_in_maydiff_value_spec; eauto.
    - eapply not_in_maydiff_load; eauto.
  Qed.

  Lemma lessdef_expr_spec
        invst invmem inv
        conf st gmax public
        e1 e2 gv1
        (SEM: Unary.sem conf st invst invmem gmax public inv)
        (E: ExprPairSet.mem (e1, e2) inv.(Invariant.lessdef))
        (E1: Unary.sem_expr conf st invst e1 = ret gv1):
    exists gv2,
      <<E2: Unary.sem_expr conf st invst e2 = ret gv2>> /\
      <<GV: GVs.lessdef gv1 gv2>>.
  Proof.
    inv SEM. exploit LESSDEF.
    - apply ExprPairSetFacts.mem_iff. eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma lessdef_GV2val
        TD gv0 gv1
        (GV: GVs.lessdef gv0 gv1)
    :
      TODO.lift2_option Val.lessdef (GV2val TD gv0) (GV2val TD gv1)
  .
  Proof.
    inv GV; ss.
    des; ss. destruct a1, b1; ss. clarify.
    inv H; ss.
    - des_ifs; ss; try (by inv H0).
    - des_ifs; ss; try (by inv H0).
  Qed.

  Lemma lessdef_mc2undefs
        gv0 mcs0
        (CHUNK: gv_chunks_match_typb_aux gv0 mcs0)
    :
      <<LD: GVs.lessdef (mc2undefs mcs0) gv0>>
  .
  Proof.
    ginduction gv0; ii; ss.
    - des_ifs. ss. econs; eauto.
    - des_ifs. ss.
      apply memory_chunk_eq_prop in H0. clarify.
      econs; ss; eauto.
      eapply IHgv0; eauto.
  Qed.

  Lemma lessdef_gundef
        TD ty gv0
        (UNDEF: gundef TD ty = ret gv0)
        gv1
        (CHUNK: gv_chunks_match_typb TD gv1 ty)
    :
      <<LD: GVs.lessdef gv0 gv1>>
  .
  Proof.
    red.
    unfold gundef, gv_chunks_match_typb in *. des_ifs.
    eapply lessdef_mc2undefs; eauto.
  Qed.

  (* Vellvm: mbop_is_total *)
  (* Just drag wf condition? *)
  Lemma mbop_total
        TD b0 s0 gva0 gvb0
    :
      exists val0, <<MBOP: mbop TD b0 s0 gva0 gvb0 = ret val0>> /\
                           <<CHUNK: gv_chunks_match_typb TD val0 (typ_int (Size.to_nat s0))>>
  .
  Proof.
    assert(MBOP: exists val0, mbop TD b0 s0 gva0 gvb0 = ret val0).
    { unfold mbop.
      des_ifs; try by (unfold gundef, flatten_typ; ss; esplits; eauto; des_ifs).
    }
    des.
    expl mbop_matches_chunks.
    esplits; eauto.
    ADMIT "this should hold".
  Qed.

  Lemma lessdef_mbop
        b0 s0 val0 gva0 gva1 gvb0 gvb1
        TD
        (MBOP0: mbop TD b0 s0 gva0 gvb0 = ret val0)
        (GVA: GVs.lessdef gva0 gva1)
        (GVB: GVs.lessdef gvb0 gvb1)
    :
      exists val1, <<MBOP: mbop TD b0 s0 gva1 gvb1 = ret val1 >> /\ <<LD: GVs.lessdef val0 val1>>
  .
  Proof.
    exploit lessdef_GV2val; try apply GVA; eauto.
    instantiate (1:= TD).
    intro VA.
    exploit lessdef_GV2val; try apply GVB; eauto.
    instantiate (1:= TD).
    intro VB.
    clear GVA GVB.
    generalize (mbop_total TD b0 s0 gva1 gvb1); intro MBOP1. des.
    esplits; eauto.
    unfold mbop in *.
    abstr (GV2val TD gva0) va0.
    abstr (GV2val TD gva1) va1.
    abstr (GV2val TD gvb0) vb0.
    abstr (GV2val TD gvb1) vb1.
    destruct va0, va1; ss; [|]; cycle 1.
    { rewrite MBOP in *. clarify. eapply GVs.lessdef_refl; eauto. }
    destruct vb0, vb1; ss; [|]; cycle 1.
    { des_ifs; try rewrite MBOP in *; clarify; eapply GVs.lessdef_refl; eauto. }
    inv VA; ss; cycle 1.
    { eapply lessdef_gundef; eauto. }
    inv VB; ss; cycle 1.
    { assert(UNDEF: gundef TD (typ_int (Size.to_nat s0)) = ret val0).
      { destruct v0; ss. }
      clear MBOP0.
      eapply lessdef_gundef; eauto.
    }
    { assert(val0 = val1).
      { des_ifs. }
      clarify.
      eapply GVs.lessdef_refl.
    }
  Qed.

  (* TODO: put off 2 from here, rename colliding lemma *)
  Lemma lessdef_expr_spec2
        invst invmem inv
        conf st gmax public
        e0 e1
        (SEM: Unary.sem conf st invst invmem gmax public inv)
        (LD_EXPR: Hints.Invariant.lessdef_expr (e0, e1) inv.(Invariant.lessdef) = true)
        e0' e1'
        (EQ0: Unary.sem_expr conf st invst e0 = Unary.sem_expr conf st invst e0')
        (EQ1: Unary.sem_expr conf st invst e1 = Unary.sem_expr conf st invst e1')
    :
      <<LD: Unary.sem_lessdef conf st invst (e0', e1')>>
  .
  Proof.
    ii. ss.
    rewrite <- EQ0 in *.
    rewrite <- EQ1 in *.
    clear EQ0 EQ1. clear_tac.
    unfold Invariant.lessdef_expr in *.
    des_bool; des.
    { eapply lessdef_expr_spec; eauto. }
    unfold Invariant.deep_check_expr in *. ss.
    des_bool; des.
    destruct e0, e1; ss; repeat (des_bool; des); des_sumbool; des_ifs_safe; clarify; clear_tac.
    - expl lessdef_expr_spec (try exact LD_EXPR0; eauto).
      expl lessdef_expr_spec (try exact LD_EXPR1; eauto). ss.
      des_ifs_safe.
      clear - VAL1 GV GV0.
      eapply lessdef_mbop; eauto.
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
    - admit. (* similar *)
  Admitted.

  Lemma inject_value_spec
        m_src conf_src st_src val_src
        m_tgt conf_tgt st_tgt val_tgt
        invst invmem inv
        gval_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (STATE: sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
        (INJECT: Invariant.inject_value inv val_src val_tgt)
        (VAL_SRC: Unary.sem_valueT conf_src st_src invst.(src) val_src = Some gval_src):
    exists gval_tgt,
      <<VAL_TGT: Unary.sem_valueT conf_tgt st_tgt invst.(tgt) val_tgt = Some gval_tgt>> /\
      <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
  Proof.
    inversion CONF. inv INJECT0.
    unfold Invariant.inject_value in INJECT. solve_bool_true.
    - inv STATE.
      eapply not_in_maydiff_value_spec; eauto.
    - inv STATE.
      exploit not_in_maydiff_value_spec; eauto. i. des.
      exploit lessdef_expr_spec; eauto. i. des.
      esplits; eauto. eapply GVs.inject_lessdef_compose; eauto.
    - inv STATE.
      exploit lessdef_expr_spec; try exact INJECT; eauto. i. des.
      exploit not_in_maydiff_value_spec; eauto. i. des.
      esplits; eauto. eapply GVs.lessdef_inject_compose; eauto.
    - inv STATE.
      apply ExprPairSetFacts.exists_iff in INJECT; [|solve_compat_bool].
      inv INJECT. destruct x. repeat (des_bool; des).
      apply get_rhs_in_spec in H. ss. des. subst.
      apply ExprPairSetFacts.mem_iff in H2.
      exploit lessdef_expr_spec; try exact H2; eauto. i. des.
      exploit not_in_maydiff_expr_spec; try exact H1; eauto. i. des.
      exploit lessdef_expr_spec; try exact H0; eauto. i. des.
      esplits; eauto.
      eapply GVs.lessdef_inject_compose; eauto.
      eapply GVs.inject_lessdef_compose; eauto.
  Qed.

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

  Lemma inject_list_value_spec
        m_src conf_src st_src vals_src
        m_tgt conf_tgt st_tgt vals_tgt
        invst invmem inv
        gval_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (STATE: sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
        (* TODO unite below into single INJECT? For unity with inject_value_spec *)
        (INJECT_SZ: List.map fst vals_src = List.map fst vals_tgt)
        (INJECT_VAL: list_forallb2 (Invariant.inject_value inv) (List.map snd vals_src) (List.map snd vals_tgt))
        (VAL_SRC: Unary.sem_list_valueT conf_src st_src invst.(src) vals_src = Some gval_src):
    exists gval_tgt,
      <<VAL_TGT: Unary.sem_list_valueT conf_tgt st_tgt invst.(tgt) vals_tgt = Some gval_tgt>> /\
      <<INJECT: list_forall2 (genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject)) gval_src gval_tgt>>.
  Proof.
    Ltac exploit_inject_value_spec_with x :=
      match (type of x) with
      | (Unary.sem_valueT _ _ _ _ = Some _) =>
        (exploit inject_value_spec; [| | | | exact x |]; eauto; ii; des; [])
      end.
    generalize dependent vals_tgt.
    generalize dependent gval_src.
    induction vals_src; ii; ss.
    - destruct vals_tgt; inv INJECT_SZ; ss. inv VAL_SRC.
      esplits; eauto. econs.
    - destruct a; ss.
      destruct vals_tgt; ss.
      inv INJECT_SZ. des_bool; des.
      destruct p; ss.
      des_ifs; (all_once exploit_inject_value_spec_with);
        (all_once exploit_inject_value_spec_with);
        (exploit IHvals_src; eauto; ii; des; []); clarify.
      + esplits; eauto.
        econs; eauto.
  Qed.

  Lemma inject_expr_spec
        m_src conf_src st_src expr_src
        m_tgt conf_tgt st_tgt expr_tgt
        invst invmem inv
        gval_src
        (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
        (STATE: sem conf_src conf_tgt st_src st_tgt invst invmem inv)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
        (INJECT: Invariant.inject_expr inv expr_src expr_tgt)
        (VAL_SRC: Unary.sem_expr conf_src st_src invst.(src) expr_src = Some gval_src):
    exists gval_tgt,
      <<VAL_TGT: Unary.sem_expr conf_tgt st_tgt invst.(tgt) expr_tgt = Some gval_tgt>> /\
      <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
  Proof.
    unfold Invariant.inject_expr in INJECT. unfold Invariant.deep_check_expr in INJECT. des_bool; des.
    assert(CONF_DUP := CONF).
    inv CONF. inv INJECT1.

    Ltac exploit_inject_list_value_spec_with x :=
      match (type of x) with
      | (Unary.sem_list_valueT _ _ _ _ = Some _) =>
        (exploit inject_list_value_spec; [| | | | | exact x |]; eauto; ii; des; [])
      end.

    (* Or we may use assert? Can we use assert with some variables left as existential? *)
    (* Like in apply f with (x := 1) (y := 2) ? *)
    (* Putting CurTargetData blah or meminj inside this Ltac seems dirty. *)

    assert(EQB_SPEC := Decs.const_eqb_spec).
    Time destruct expr_src, expr_tgt;
      inv INJECT; (* only 13 will remain from 169 *)
      repeat (des_bool; des; ss);
      des_ifs; (* 41 goals *) (* Finished transaction in 25.972 secs (25.937u,0.05s) (successful) *)
      clarify; (* 41 goals, Finished transaction in 30.875 secs (30.841u,0.052s) (successful) *)
      des_sumbool; subst; ss;
        try (rewrite <- TARGETDATA);
        try (exploit (@eqb_forallb2 const); eauto; ii; des; []);
        (all_once exploit_inject_value_spec_with);
        (all_once exploit_inject_list_value_spec_with);
        clarify; (* Finished transaction in 140.027 secs (139.734u,0.373s) (successful) *)
        try exploit_eq_GV2int.
    - exploit genericvalues_inject.simulation__mbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfbop; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__extractGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__insertGenericValue; try apply VAL_SRC; eauto; ii; des; eauto.
    -
      inv MEM.
      exploit genericvalues_inject.simulation__GEP; try apply VAL_SRC; eauto; ii; des; eauto.
      apply forall_gv_inject_gvs_inject; ss.
    - exploit genericvalues_inject.simulation__mtrunc; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mext; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mcast; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__micmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - exploit genericvalues_inject.simulation__mfcmp; try apply VAL_SRC; eauto; ii; des; eauto.
    - esplits; eauto.
    - esplits; eauto.
    - exploit inject_value_spec; eauto.
    -
      eapply inject_expr_load; eauto.
  Qed.
  (* TODO move inject_expr_load out of here, + refactor with maydiff_load *)
End Rel.

Module Subset.
  Ltac conv_mem2In :=
    repeat 
      match goal with
      | [H: IdTSet.mem ?x ?inv = true |- _] =>
        apply IdTSetFacts.mem_iff in H
      | [H: ValueTSet.mem ?x ?inv = true |- _] =>
        apply ValueTSetFacts.mem_iff in H
      | [H: ValueTPairSet.mem ?x ?inv = true |- _] =>
        apply ValueTPairSetFacts.mem_iff in H
      | [H: ExprPairSet.mem ?x ?inv = true |- _] =>
        apply ExprPairSetFacts.mem_iff in H
      | [H: PtrSet.mem ?x ?inv = true |- _] =>
        apply PtrSetFacts.mem_iff in H
      | [H: PtrPairSet.mem ?x ?inv = true |- _] =>
        apply PtrPairSetFacts.mem_iff in H
      | [H: AtomSetImpl.mem ?x ?inv = true |- _] =>
        apply AtomSetFacts.mem_iff in H

      | [_:_ |- IdTSet.mem ?x ?inv = true] =>
        apply IdTSetFacts.mem_iff
      | [_:_ |- ValueTSet.mem ?x ?inv = true] =>
        apply ValueTSetFacts.mem_iff
      | [_:_ |- ValueTPairSet.mem ?x ?inv = true] =>
        apply ValueTPairSetFacts.mem_iff
      | [_:_ |- ExprPairSet.mem ?x ?inv = true] =>
        apply ExprPairSetFacts.mem_iff
      | [_:_ |- PtrSet.mem ?x ?inv = true] =>
        apply PtrSetFacts.mem_iff
      | [_:_ |- PtrPairSet.mem ?x ?inv = true] =>
        apply PtrPairSetFacts.mem_iff
      | [_:_ |- AtomSetImpl.mem ?x ?inv = true] =>
        apply AtomSetFacts.mem_iff

      | [H: IdTSet.mem ?x ?inv = false |- _] =>
        apply IdTSetFacts.not_mem_iff in H
      | [H: ValueTSet.mem ?x ?inv = false |- _] =>
        apply ValueTSetFacts.not_mem_iff in H
      | [H: ValueTPairSet.mem ?x ?inv = false |- _] =>
        apply ValueTPairSetFacts.not_mem_iff in H
      | [H: ExprPairSet.mem ?x ?inv = false |- _] =>
        apply ExprPairSetFacts.not_mem_iff in H
      | [H: PtrSet.mem ?x ?inv = false |- _] =>
        apply PtrSetFacts.not_mem_iff in H
      | [H: PtrPairSet.mem ?x ?inv = false |- _] =>
        apply PtrPairSetFacts.not_mem_iff in H
      | [H: AtomSetImpl.mem ?x ?inv = false |- _] =>
        apply AtomSetFacts.not_mem_iff in H

      | [_:_ |- IdTSet.mem ?x ?inv = false] =>
        apply IdTSetFacts.not_mem_iff
      | [_:_ |- ValueTSet.mem ?x ?inv = false] =>
        apply ValueTSetFacts.not_mem_iff
      | [_:_ |- ValueTPairSet.mem ?x ?inv = false] =>
        apply ValueTPairSetFacts.not_mem_iff
      | [_:_ |- ExprPairSet.mem ?x ?inv = false] =>
        apply ExprPairSetFacts.not_mem_iff
      | [_:_ |- PtrSet.mem ?x ?inv = false] =>
        apply PtrSetFacts.not_mem_iff
      | [_:_ |- PtrPairSet.mem ?x ?inv = false] =>
        apply PtrPairSetFacts.not_mem_iff
      | [_:_ |- AtomSetImpl.mem ?x ?inv = false] =>
        apply AtomSetFacts.not_mem_iff
      end
  .

  Program Instance PreOrder_Subset_unary : PreOrder Invariant.Subset_unary.
  Next Obligation.
    econs; try econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. inv SUBSET_NOALIAS. inv SUBSET_NOALIAS0.
    econs; try econs; etransitivity; eauto.
  Qed.
  
  Program Instance PreOrder_Subset : PreOrder Invariant.Subset.
  Next Obligation.
    econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0.
    econs; etransitivity; eauto.
  Qed.

  Lemma not_in_maydiff_Subset
        inv0 inv1
         (SUBSET: Invariant.Subset inv0 inv1)
  : Invariant.not_in_maydiff inv0 <1= Invariant.not_in_maydiff inv1.
  Proof.
    unfold Invariant.not_in_maydiff in *.
    i. des_ifs.
    des_bool.
    rewrite negb_true_iff in *.
    inv SUBSET.
    conv_mem2In.
    ii. exploit SUBSET_MAYDIFF; eauto.
  Qed.

  Lemma inject_value_Subset
        v1 v2
        inv0 inv1
        (INJECT: Invariant.inject_value inv0 v1 v2)
        (SUBSET: Invariant.Subset inv0 inv1)
  : Invariant.inject_value inv1 v1 v2.
  Proof.
    unfold Invariant.inject_value in *.
    unfold sflib.is_true in *.
    repeat rewrite orb_true_iff in INJECT.
    repeat rewrite orb_true_iff.
    des.
    - left. left. left.
      des_bool. des.
      apply andb_true_iff.
      split; eauto.
      eapply not_in_maydiff_Subset; eauto.
    - left. left. right.
      des_bool. des.
      apply andb_true_iff.
      split; eauto; try by eapply not_in_maydiff_Subset; eauto.
      inv SUBSET.
      inv SUBSET_TGT.
      conv_mem2In.
      exploit SUBSET_LESSDEF; eauto.
    - left. right.
      des_bool. des.
      apply andb_true_iff; split; eauto; try by eapply not_in_maydiff_Subset; eauto.
      inv SUBSET. inv SUBSET_SRC.
      conv_mem2In.
      exploit SUBSET_LESSDEF; eauto.
    - right.
      rewrite <- ExprPairSetFacts.exists_iff in *;try by solve_compat_bool.
      unfold ExprPairSet.Exists in *. des.
      apply get_rhs_in_spec in INJECT. des.
      esplits.
      + eapply get_rhs_in_spec2; eauto.
        inv SUBSET. inv SUBSET_SRC.
        exploit SUBSET_LESSDEF; eauto.
      + des_bool. des.
        apply andb_true_iff.
        split.
        * inv SUBSET. inv SUBSET_TGT.
          conv_mem2In.
          exploit SUBSET_LESSDEF; eauto.
        * unfold Invariant.not_in_maydiff_expr in *.
          apply forallb_forall. i.
          eapply forallb_forall in INJECT2; eauto.
          eapply not_in_maydiff_Subset; eauto.
  Qed.

End Subset.
