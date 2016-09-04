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
Require Import GenericValues.
Require Import SimulationLocal.
Require InvMem.
Require InvState.
Require Import SoundBase.
Require Import SoundImplies.
Require Import SoundPostcond.
Require Import SoundInfrules.
Require Import SoundReduceMaydiff.

Set Implicit Arguments.


(* TODO: position *)
Definition get_blocks (f:fdef): blocks :=
  let '(fdef_intro _ blocks) := f in
  blocks.

Inductive vali_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (invmem:InvMem.Rel.t)
          (idx:nat)
          (st_src st_tgt:State): Prop :=
| vali_state_sim_intro
    m_src m_tgt
    fdef_hint cmds_hint
    inv inv_term
    invst
    (CONF: CONF_TODO) (* m_src, m_tgt, conf_src, conf_tgt *)
    (ECS_SRC: st_src.(ECS) = stack0_src)
    (ECS_TGT: st_tgt.(ECS) = stack0_tgt)
    (FDEF: valid_fdef m_src m_tgt st_src.(EC).(CurFunction) st_tgt.(EC).(CurFunction) fdef_hint)
    (CMDS: valid_cmds m_src m_tgt st_src.(EC).(CurCmds) st_tgt.(EC).(CurCmds) cmds_hint inv = Some inv_term)
    (TERM: valid_terminator fdef_hint inv_term m_src m_tgt
                            st_src.(EC).(CurFunction).(get_blocks)
                            st_tgt.(EC).(CurFunction).(get_blocks)
                            st_src.(EC).(CurBB).(fst)
                            st_src.(EC).(Terminator)
                            st_tgt.(EC).(Terminator))
    (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
    (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
.

Lemma vali_init
      m_src m_tgt
      conf_src conf_tgt
      stack0_src stack0_tgt
      fdef_src fdef_tgt
      fdef_hint
      args_src args_tgt
      mem_src mem_tgt
      inv
      ec_src
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (CONF: CONF_TODO)
      (INIT: init_fdef conf_src fdef_src args_src ec_src):
  exists ec_tgt idx,
    init_fdef conf_tgt fdef_tgt args_tgt ec_tgt /\
    vali_state_sim
      conf_src conf_tgt
      stack0_src stack0_tgt
      inv idx
      (mkState ec_src stack0_src mem_src)
      (mkState ec_tgt stack0_tgt mem_tgt).
Proof.
Admitted.

(* TODO: position *)
Ltac condtac :=
  repeat
    (try match goal with
         | [H: ?a = ?a |- _] => clear H
         | [H: context[match ?c with
                       | [] => _
                       | _::_ => _
                       end] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [H: context[match ?c with
                       | Some _ => _
                       | None => _
                       end] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [H: context[if ?c then _ else _] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [H: Some _ = Some _ |- _] => inv H
         | [H: context[let (_, _) := ?p in _] |- _] => destruct p
         | [H: negb _ = false |- _] =>
           apply negb_false_iff in H
         | [H: proj_sumbool (typ_dec ?a ?b) = true |- _] =>
           destruct (typ_dec a b)
         | [H: proj_sumbool (l_dec ?a ?b) = true |- _] =>
           destruct (l_dec a b)
         end;
     unfold Debug.debug_print_validation_process in *;
     subst; ss).


(* TODO: position *)
Lemma inject_value_sound
      conf_src st_src val_src
      conf_tgt st_tgt val_tgt
      invst invmem inv
      gval_src
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
      (INJECT: Hints.Invariant.inject_value inv val_src val_tgt)
      (VAL_SRC: InvState.Unary.sem_valueT conf_src st_src invst.(InvState.Rel.src) val_src = Some gval_src):
  exists gval_tgt,
    <<VAL_TGT: InvState.Unary.sem_valueT conf_tgt st_tgt invst.(InvState.Rel.tgt) val_tgt = Some gval_tgt>> /\
    <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
Proof.
Admitted.

(* TODO: position *)
Lemma sem_valueT_physical
      conf st inv val:
  InvState.Unary.sem_valueT conf st inv (Exprs.ValueT.lift Exprs.Tag.physical val) =
  getOperandValue conf.(CurTargetData) val st.(EC).(Locals) conf.(Globals).
Proof. destruct val; ss. Qed.

Lemma vali_sim
      conf_src conf_tgt
      (CONF: CONF_TODO):
  (vali_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  intros stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM. pfold.
  generalize (classic (stuck_state conf_src st_src)). intro STUCK_SRC. des.
  { destruct (s_isFinialState conf_src st_src) eqn:FINAL_SRc; cycle 1.
    - (* error *)
      eapply _sim_local_error; eauto. econs; eauto.
    - (* final *)
      admit.
  }
  destruct st_src, st_tgt. destruct EC0, EC1.
  inv SIM. ss.
  destruct CurCmds0; condtac;
    (try by exfalso; eapply has_false_False; eauto).
  - (* term *)
    unfold valid_terminator in TERM.
    condtac;
      (try by exfalso; eapply has_false_False; eauto).
    apply NNPP in STUCK_SRC. des.
    inv STUCK_SRC; destruct Terminator1; condtac.
    (* TODO: switch case *)
    + (* return *)
      unfold returnUpdateLocals in *. condtac.
      exploit inject_value_sound; eauto.
      { rewrite sem_valueT_physical. eauto. }
      rewrite sem_valueT_physical. s. i. des.
      eapply _sim_local_return; eauto; ss.
    + (* return_void *)
      eapply _sim_local_return_void; eauto; ss.
    + (* br *)
      exploit inject_value_sound; eauto.
      { rewrite sem_valueT_physical. eauto. }
      rewrite sem_valueT_physical. s. i. des.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      esplits; eauto.
      { econs 1. econs; eauto. rewrite COND5. eauto. }
      { admit. (* InvMem.Rel.le refl *) }
      right. apply CIH.
      instantiate (1 := mkState _ _ _). econs; eauto; ss.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
      * admit. (* InvState.Rel.sem *)
    + (* br, bogus: see https://github.com/snu-sf/llvmberry/issues/310 *)
      admit.
    + (* br_uncond *)
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      esplits; eauto.
      { econs 1. econs; eauto. }
      { admit. (* InvMem.Rel.le refl *) }
      right. apply CIH.
      instantiate (1 := mkState _ _ _). econs; eauto; ss.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
      * admit. (* InvState.Rel.sem *)
  - (* cmd *)
    eapply _sim_local_step.
    { (* tgt not stuck *)
      admit.
    }
    i.
    (* TODO: call is ignored! *)
    exploit postcond_cmd_sound; eauto; ss. i. des.
    exploit apply_infrules_sound; eauto; ss. i. des.
    exploit reduce_maydiff_sound; eauto; ss. i. des.
    exploit implies_sound; eauto; ss. i. des.
    esplits; eauto.
    + econs 1. eauto.
    + right. apply CIH. econs; eauto.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
Admitted.

Lemma vali_sim_func
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: CONF_TODO)
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint):
  sim_func conf_src conf_tgt fdef_src fdef_tgt.
Proof.
  ii.
  exploit vali_init; eauto. i. des.
  esplits; eauto.
  apply vali_sim; eauto.
Qed.
