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

Lemma sim_module_init
      module_src module_tgt main args
      conf_src st_src
      (SIM: sim_module module_src module_tgt)
      (SRC: s_genInitState [module_src] main args Mem.empty = ret (conf_src, st_src)):
  exists conf_tgt st_tgt idx,
    <<TGT: s_genInitState [module_tgt] main args Mem.empty = ret (conf_tgt, st_tgt)>> /\
    <<SIM: sim conf_src conf_tgt idx st_src st_tgt>>.
Proof.
Admitted.

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
