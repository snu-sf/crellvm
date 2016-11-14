Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import Validator.
Require Import Postcond.
Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Require Import Inject. (* TODO: for simtac *)

Set Implicit Arguments.


(* Forget *)

Definition locals_equiv_except (ids:AtomSetImpl.t) (locals0 locals1:GVsMap): Prop :=
  forall id (NOT_MEM: AtomSetImpl.mem id ids = false),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Inductive state_equiv_except (ids:AtomSetImpl.t) (st0 st1: State): Prop :=
| state_eq_except_intro
    (MEM: st0.(Mem) = st1.(Mem))
    (LOCALS: locals_equiv_except ids st0.(EC).(Locals) st1.(EC).(Locals))
.

Ltac inv_state_equiv_except :=
  repeat match goal with
         | [H: state_equiv_except ?ids ?st0 ?st1 |- _] =>
           inv H; unfold locals_equiv_except in *
         end;
  repeat match goal with
         | [_:_ |- state_equiv_except ?ids ?st0 ?st1] =>
           econs; unfold locals_equiv_except in *
         end.

Program Instance Equivalence_state_equiv_except ids
  : Equivalence (state_equiv_except ids).
Next Obligation.
  ss.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; symmetry; eauto.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; eauto using eq_trans.
Qed.

Lemma sem_idT_equiv_except
      ids st0 st1 invst id gv
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_idT st0 invst (Tag.physical, id) = Some gv)
      (NOTIN: AtomSetImpl.mem id ids = false)
  : <<STATE: InvState.Unary.sem_idT st1 invst (Tag.physical, id) = Some gv>>.
Proof.
  unfold InvState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma sem_valueT_equiv_except
      ids st0 st1 invst v gv
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_valueT conf st0 invst v = Some gv)
      (NOTIN: (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids))) v = false)
  : <<STATE: InvState.Unary.sem_valueT conf st1 invst v = Some gv>>.
Proof.
  unfold flip in NOTIN.
  destruct v; ss. destruct x. destruct t; ss.
  rewrite lift_physical_atoms_idtset_spec1 in *.
  eapply sem_idT_equiv_except; eauto.
Qed.

Lemma sem_list_valueT_equiv_except
      ids st0 st1 invst lsv gvs
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_list_valueT conf st0 invst lsv = Some gvs)
      (NOTIN: existsb (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids)) <*> snd) lsv = false)
  : <<STATE: InvState.Unary.sem_list_valueT conf st1 invst lsv = Some gvs>>.
Proof.
  unfold flip in NOTIN.
  revert gvs STATE NOTIN.
  induction lsv; ss.
  i. simtac.
  apply orb_false_iff in NOTIN. des.
  exploit sem_valueT_equiv_except; eauto. i. des.
  des_ifs; exploit IHlsv; eauto; i; des; clarify.
Qed.

Ltac solve_equiv_except_val st0 :=
  repeat match goal with
         | [H: _ || LiftPred.ValueT _ _ = false |- _] =>
           apply orb_false_iff in H;des
         | [H: LiftPred.ValueT _ _ || _ = false |- _] =>
           apply orb_false_iff in H;des
         end;
  repeat match goal with
         | [H: InvState.Unary.sem_valueT _ st0 _ _ = Some _ |- _] =>
           eapply sem_valueT_equiv_except in H; eauto; rewrite H
         end.

Lemma sem_expr_equiv_except
      conf invst
      ids st0 st1 e val
      (EQUIV: state_equiv_except ids st0 st1)
      (FILTER: (LiftPred.Expr (flip IdTSet.mem (lift_physical_atoms_idtset ids))) e = false)
      (SEM_EXPR: InvState.Unary.sem_expr conf st0 invst e = Some val)
  : <<SEM_EXPR: InvState.Unary.sem_expr conf st1 invst e = Some val>>.
Proof.
  unfold compose in FILTER.
  destruct e; ss; simtac;
    try (solve_equiv_except_val st0; eauto).
  - erewrite sem_list_valueT_equiv_except; eauto.
  - rewrite COND2. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
Qed.

Lemma forget_stack_unary_Subset
      defs leaks inv0
  : Invariant.Subset_unary (ForgetStack.unary defs leaks inv0) inv0.
Proof.
  unfold ForgetStack.unary.
  econs; ss; ii.
  - eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - econs; ii.
    + eapply ValueTPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
    + eapply PtrPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
  - eapply AtomSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - eapply IdTSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
Qed.

Lemma forget_stack_Subset
      def_src def_tgt inv0
      leaks_src leaks_tgt
  : Invariant.Subset (ForgetStack.t def_src def_tgt leaks_src leaks_tgt inv0) inv0.
Proof.
  unfold ForgetStack.t.
  econs; ss;
    try apply forget_stack_unary_Subset.
  ii.
  apply IdTSet.union_3. eauto.
Qed.

(* soundness *)

Inductive unique_preserved_except conf inv unique_parent st gmax except_for : Prop :=
| unique_preserved_except_intro
    (UNIQUE_PRESERVED_INV:
       forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true)
         (NO_LEAK: AtomSetImpl.mem u except_for = false),
         InvState.Unary.sem_unique conf st gmax u)
    (UNIQUE_PRESERVED_PARENT_LOCAL:
       forall x ptr
         (PTR:lookupAL _ st.(EC).(Locals) x = Some ptr),
         InvMem.gv_diffblock_with_blocks conf ptr unique_parent)
    (UNIQUE_PRESERVED_PARENT_MEM:
       forall mptr typ align val'
         (LOAD: mload conf.(CurTargetData) st.(Mem) mptr typ align = Some val'),
         InvMem.gv_diffblock_with_blocks conf val' unique_parent)
    (UNIQUE_PRESERVED_PARENT_GLOBALS:
       forall b (IN: In b unique_parent), (gmax < b)%positive)
.

Require Import memory_props.
Import MemProps.

Lemma mbop_multiple_result_inv
      TD bop sz gvs1 gvs2 val1 val2 vals
      (MBOP: mbop TD bop sz gvs1 gvs2 = Some (val1 :: val2 :: vals))
  :
    gundef TD (typ_int sz) = Some (val1 :: val2 :: vals)
.
Proof.
  unfold mbop in *.
  des_ifs.
Qed.

Lemma mbop_no_result_inv
      TD bop sz gvs1 gvs2
      (MBOP: mbop TD bop sz gvs1 gvs2 = Some (nil))
  :
    gundef TD (typ_int sz) = Some (nil)
.
Proof.
  unfold mbop in *.
  des_ifs.
Qed.

Lemma BOP_diffblock
      S TD Ps gl fs
      lc bop sz v1 v2 val ptr
      (H : BOP TD lc gl bop sz v1 v2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  apply opsem_props.OpsemProps.BOP_inversion in H. des.
  (* exploit mbop_preserves_no_alias; eauto; []; ii; des. *)
  exploit mbop_preserves_no_embedded_ptrs; eauto; []; ii; des.
  {
    clear H H0.
    generalize dependent gvs1.
    generalize dependent gvs2.
    induction val; ii; ss.
    -
      (* can mbop = Some [] happen? *)
      unfold InvState.Unary.sem_diffblock.
      ss.
      destruct (GV2ptr TD (getPointerSize TD) ptr); ss.
      destruct v; ss.
    -
      destruct val; ss.
      {
        (* can mbop = Some [] happen? *)
        unfold InvState.Unary.sem_diffblock.
        ss.
        destruct (GV2ptr TD (getPointerSize TD) ptr); ss.
        destruct v; ss.
        destruct a; ss.
        destruct v; ss.
      }
      {
        destruct p; ss.
        destruct a; ss.
        unfold InvState.Unary.sem_diffblock. ss.
        destruct v0; ss; destruct v; ss; des_ifs.
      }
  }
Qed. (* memory_props.MemProps.mbop_preserves_no_embedded_ptrs or *)
(* memory_props.MemProps.mbop_preserves_no_alias? *)

Lemma FBOP_diffblock
      S TD Ps gl fs
      lc bop sz v1 v2 val ptr
      (H : FBOP TD lc gl bop sz v1 v2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
Admitted.

Definition leaks_diffblock_with conf st cmd ptr: Prop :=
  forall v gv
    (IN_LEAK: In v (Cmd.get_leaked_values cmd))
    (VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gv),
    InvState.Unary.sem_diffblock conf ptr gv.

Lemma operands_diffblock
      conf st gmax cmd
      u uptr
      (UNIQUE_U: InvState.Unary.sem_unique conf st gmax u)
      (NOT_LEAKED: AtomSetImpl.mem u (AtomSetImpl_from_list
                                        (Cmd.get_leaked_ids cmd)) = false)
      (U_VALUE : lookupAL GenericValue st.(EC).(Locals) u = Some uptr)
  : leaks_diffblock_with conf st cmd uptr.
Proof.
Admitted.

Lemma extractGenericValue_diffblock
      conf st cmd
      x ty1 v lc ty2
      ptr gv l0 val
      (CMD: cmd = insn_extractvalue x ty1 v lc ty2)
      (VAL : getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gv)
      (OPERANDS_DIFFBLOCK: leaks_diffblock_with conf st cmd ptr)
      (RES: extractGenericValue conf.(CurTargetData) ty1 gv l0 = Some val)
  : InvState.Unary.sem_diffblock conf ptr val.
Proof.
Admitted.

Require Import SoundPostcondCmdAdd.

Lemma step_unique_preserved_except_current
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : << UNIQUE_CURRENT:
    forall u : atom,
      AtomSetImpl.mem u (Invariant.unique inv0) = true ->
      AtomSetImpl.mem u
                      (union (AtomSetImpl_from_list (Cmd.get_def cmd))
                             (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))) = false ->
      InvState.Unary.sem_unique conf st1 gmax u>>.
Proof.
  intros u MEM_U NOT_LEAKED_U0.
  apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U0.
  hexploit notin_union_1; eauto. intros NOT_DEF_U.
  hexploit notin_union_2; eauto. intros NOT_LEAKED_U. clear NOT_LEAKED_U0.
  apply AtomSetFacts.not_mem_iff in NOT_DEF_U.
  apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
  inv STATE. inv MEM.
  exploit UNIQUE; eauto.
  { apply AtomSetFacts.mem_iff. eauto. }
  intros UNIQUE_BEF.

  (* Ltac solve_unique_not_def := *)
  (*   try by match goal with *)
  (*          | [H: AtomSetImpl.mem ?u (AtomSetImpl_from_list [?x]) = false |- *)
  (*             lookupAL _ (updateAddAL _ ?lc ?x _) ?u = Some _ ] => *)
  (*            rewrite <- lookupAL_updateAddAL_neq; eauto; *)
  (*            apply AtomSetImpl_singleton_mem_false; eauto *)
  (*          end. *)
  Ltac clarify_not_def :=
    match goal with
    | [H: AtomSetImpl.mem ?u (AtomSetImpl_from_list [?x]) = false |- _] =>
      apply AtomSetImpl_singleton_mem_false in H
    end.

  Ltac narrow_down_unique :=
    try
      (clarify_not_def;
       econs; eauto; ss;
       [by rewrite <- lookupAL_updateAddAL_neq; eauto |
        i;
        match goal with
        | [H: lookupAL _ (updateAddAL _ ?lc ?x _) ?reg = Some _ |- _] =>
          destruct (id_dec x reg); [|by rewrite <- lookupAL_updateAddAL_neq in *; eauto]
        end; subst;
        rewrite lookupAL_updateAddAL_eq in *; clarify]).
  inv STEP; destruct cmd; ss; clarify;
    try by inv UNIQUE_BEF; econs; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply BOP_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply FBOP_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.

    

      
    admit.
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* insertvalue *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* malloc *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* alloca *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* load *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* gep *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* trunc *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* extop *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* cast *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* icmp *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* fcmp *)
  - inv UNIQUE_BEF; narrow_down_unique.
    admit. (* select *)
Admitted.

Lemma step_unique_preserved_except_parent
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : <<UNIQUE_PARENT:
    forall (x : atom) (ptr : GenericValue),
      lookupAL GenericValue (Locals (EC st1)) x = Some ptr ->
      InvMem.gv_diffblock_with_blocks conf ptr (InvMem.Unary.unique_parent invmem)>>.
Proof.
Admitted.

Lemma step_unique_preserved_except
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : unique_preserved_except conf inv0 invmem.(InvMem.Unary.unique_parent) st1 gmax
                            (AtomSetImpl.union (AtomSetImpl_from_list (Cmd.get_def cmd))
                                               (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))).
Proof.
  hexploit step_unique_preserved_except_current; eauto. i.
  hexploit step_unique_preserved_except_parent; eauto. i.
  inv STATE. inv MEM.
  econs; eauto.
Qed.


(* Ltac rename_id_res x:= *)
(*   match goal with *)
(*   | [H: lookupAL _ (updateAddAL _ _ ?id _) ?reg = Some _ |- _] => *)
(*     rename id into x *)
(*   end. *)
(* inv STEP; ss; destruct cmd; ss; inv CMDS. *)
(* - (* nop *) *)
(*   ii. apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. ss. *)
(*   econs; ss; eauto. *)
(* - (* bop *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* bop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* fbop *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* fbop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* extractvalue *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* bop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* insertvalue *) *)
(*   (* TODO: fill rest *) *)


Lemma step_state_equiv_except
      conf st0 st1 evt
      cmd cmds
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : state_equiv_except (AtomSetImpl_from_list (Cmd.get_def cmd))
                       (mkState st0.(EC) st0.(ECS) st1.(Mem)) st1.
Proof.
  inv STEP; ss;
    inv CMDS; econs; ss; ii;
      hexploit AtomSetImpl_singleton_mem_false; eauto; i;
        eauto using lookupAL_updateAddAL_neq.
Qed.

Lemma forget_stack_unary_sound
      conf defs leaks st0 st1 gmax
      inv invst invmem
      (EQUIV : state_equiv_except defs st0 st1)
      (UNIQUE_PRESERVED : unique_preserved_except conf inv invmem.(InvMem.Unary.unique_parent) st1 gmax (AtomSetImpl.union defs leaks))
      (STATE : InvState.Unary.sem conf st0 invst invmem gmax inv)
      (WF_LC: memory_props.MemProps.wf_lc st1.(Mem) st1.(EC).(Locals))
  : InvState.Unary.sem conf st1 invst invmem gmax (ForgetStack.unary defs leaks inv).
Proof.
  inv STATE.
  assert (EQUIV_REV: state_equiv_except defs st1 st0).
  { symmetry. eauto. }
  econs; eauto.
  - ii. destruct x as [e1 e2]. ss.
    apply ExprPairSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    solve_negb_liftpred.
    exploit sem_expr_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto.
    i. des.
    exploit LESSDEF; eauto.
    i. des. ss.
    exploit sem_expr_equiv_except; try exact EQUIV; try exact VAL2; eauto.
  - inv NOALIAS.
    econs.
    + i. ss.
      rewrite ValueTPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
    + i. ss.
      rewrite PtrPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
  - ii. ss.
    apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    apply negb_true_iff in H0.
    inv UNIQUE_PRESERVED.
    apply UNIQUE_PRESERVED_INV; eauto.
    apply AtomSetFacts.mem_iff; eauto.
  - ii. ss.
    apply IdTSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    unfold flip, compose in *.
    apply negb_true_iff in H0.
    destruct x as [t x].
    destruct t; try (exploit PRIVATE; eauto; fail).
    exploit sem_idT_equiv_except; eauto.
    { rewrite <- lift_physical_atoms_idtset_spec1. eauto. }
    i. des.
    exploit PRIVATE; eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv UNIQUE_PRESERVED. eauto.
Qed.

Lemma forget_stack_sound
      conf_src st0_src
      conf_tgt st0_tgt
      st1_src st1_tgt
      invst invmem inv0
      defs_src defs_tgt
      leaks_src leaks_tgt
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv0)
      (EQUIV_SRC: state_equiv_except defs_src st0_src st1_src)
      (EQUIV_TGT: state_equiv_except defs_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except
                     conf_src inv0.(Invariant.src)
                     invmem.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
                     st1_src invmem.(InvMem.Rel.gmax)
                     (AtomSetImpl.union defs_src leaks_src))
      (UNIQUE_TGT: unique_preserved_except
                     conf_tgt inv0.(Invariant.tgt)
                     invmem.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
                     st1_tgt invmem.(InvMem.Rel.gmax)
                     (AtomSetImpl.union defs_tgt leaks_tgt))
      (WF_LC_SRC: memory_props.MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_LC_TGT: memory_props.MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
  : <<STATE_FORGET: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt
                                     invst invmem (ForgetStack.t defs_src defs_tgt leaks_src leaks_tgt inv0)>>.
Proof.
  inv STATE.
  econs; ss.
  - eapply forget_stack_unary_sound; eauto.
  - eapply forget_stack_unary_sound; eauto.
  - i. ss.
    rewrite IdTSetFacts.union_b in NOTIN.
    solve_des_bool.
    destruct id0. destruct t; ss.
    + rewrite lift_physical_atoms_idtset_spec1 in *.
      rewrite AtomSetFacts.union_b in NOTIN.
      solve_des_bool.
      ii. symmetry in EQUIV_SRC.
      exploit sem_idT_equiv_except; try exact EQUIV_SRC; eauto. i. des.
      exploit MAYDIFF; eauto. i. des.
      exploit sem_idT_equiv_except; try exact EQUIV_TGT; eauto.
    + ii. exploit MAYDIFF; eauto.
    + ii. exploit MAYDIFF; eauto.
Qed.
