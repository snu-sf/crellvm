Require Import sflib.

Require Import vellvm.
Require Import paco.

Import Opsem.
Require Import Behavior.
Require Import Simulation.

Lemma adequacy
      conf_src conf_tgt idx st_src st_tgt
      (SIM: sim conf_src conf_tgt idx st_src st_tgt):
  behave conf_tgt st_tgt <1= behave conf_src st_src.
Proof.
  s. revert idx st_src st_tgt SIM. pcofix CIH. i.
Admitted.

(* TODO: <<a: True>> notation *)
Lemma sim_system_init
      system_src system_tgt main args
      conf_src st_src
      (SRC: s_genInitState system_src main args Mem.empty = ret (conf_src, st_src)):
  exists conf_tgt st_tgt idx,
    s_genInitState system_tgt main args Mem.empty = ret (conf_tgt, st_tgt) /\
    sim conf_src conf_tgt idx st_src st_tgt.
Proof.
Admitted.

Lemma adequacy_system
      system_src system_tgt
      (SIM: sim_system system_src system_tgt):
  behave_system system_tgt <3= behave_system system_src.
Proof.
  s. intros main args obs TGT conf_src st_src INIT_SRC.
  exploit sim_system_init; eauto. i. des.
  exploit TGT; eauto.
  eapply adequacy. eauto.
Qed.
