Require Import Program.
Require Import sflib.

Require Import vellvm.
Require Import paco.
Require Import opsem_props.
Import Opsem.
Import OpsemProps.

Require Import GenericValues.
Require Import Behavior.
Require Import Simulation.

Lemma strong_induction
      (P : nat -> Prop)
      (IH: forall (n:nat) (IH: forall (k:nat) (LT: (k < n)%nat), P k), P n):
  forall n : nat, P n.
Proof.
  i. cut (forall (m k:nat), (k < m -> P k)%nat); [by eauto|].
  induction m.
  - i. omega.
  - i. apply lt_le_S in H. inv H; eauto.
Qed.

Lemma adequacy
      conf_src conf_tgt idx st_src st_tgt
      (SIM: sim conf_src conf_tgt idx st_src st_tgt):
  behave conf_tgt st_tgt <1= behave conf_src st_src.
Proof.
  s. revert idx st_src st_tgt SIM. pcofix CIH. i.
  punfold PR. inv PR. revert idx st_src SIM x0 MAT.
  dependent induction TAU; cycle 1.
  { i. destruct tr1, tr2; ss.
    punfold SIM. inv SIM.
    - pfold. econs; eauto.
    - exfalso. eapply final_stuck; eauto.
    - exploit STEP; eauto. i. des. inv H2; [|done].
      exploit IHTAU; eauto. i.
      punfold H2. inv H2. pfold. econs; [|eauto].
      rewrite <- E0_right. eapply sop_star_trans; eauto.
      inv H1; eauto.
      rewrite <- E0_right. econs 2; eauto.
  }
  intros idx. revert state.
  induction idx using strong_induction. i.
  punfold SIM. inv SIM.
  - pfold. econs; eauto.
  - inv MAT.
    + inv ERROR. congruence.
    + pfold. econs; eauto. econs 2. congruence.
    + exfalso. eapply final_stuck; eauto.
    + exfalso. eapply final_stuck; eauto.
  - inv MAT.
    + contradict PROGRESS. inv ERROR; ss.
    + contradict PROGRESS. ii. des.
      destruct (s_isFinialState conf_tgt state) eqn:X; ss.
      exfalso. eapply final_stuck; eauto.
    + exploit STEP; eauto. i. des.
      inv INF; [|done]. inv H1; [|done]. inv H0.
      * pfold. econs; eauto.
      * exploit IH; eauto.
        { punfold H2. inv H2. dependent induction TAU; eauto.
          destruct tr1, tr2; ss. econs 3; eauto.
        }
        i. punfold H0. inv H0. pfold. econs; [|eauto].
        rewrite <- E0_right. eapply sop_star_trans; eauto.
    + exploit STEP; eauto. i. des.
      inv INF; [|done]. inv H1; [|done]. inv H0; [|done].
      pfold. econs; eauto.
Qed.

Lemma sim_module_init
      module_src module_tgt main args
      conf_src st_src
      (SIM: sim_module module_src module_tgt)
      (SRC: s_genInitState [module_src] main args Mem.empty = ret (conf_src, st_src)):
  exists conf_tgt st_tgt idx,
    <<TGT: s_genInitState [module_tgt] main args Mem.empty = ret (conf_tgt, st_tgt)>> /\
    <<SIM: sim conf_src conf_tgt idx st_src st_tgt>>.
Proof. exploit SIM; eauto. Qed.

Lemma adequacy_module
      module_src module_tgt
      (SIM: sim_module module_src module_tgt):
  behave_module module_tgt <3= behave_module module_src.
Proof.
  s. intros main args obs TGT conf_src st_src INIT_SRC.
  exploit sim_module_init; eauto. i. des.
  exploit TGT; eauto.
  eapply adequacy. eauto.
Qed.
