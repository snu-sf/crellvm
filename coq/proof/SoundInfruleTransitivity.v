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
Require Import TODOProof.
Require Import Decs.
Require Import Exprs.
Require Import Validator.
Require Import GenericValues.
Require Import Inject.
Require AssnMem.
Require AssnState.
Require Import Hints.
Require Import memory_props.
Import Memory.
Require Import opsem_wf.
Require Import genericvalues_inject.
Require Import memory_sim.
Require Import MemAux.
Require Import SoundBase.

Set Implicit Arguments.

Lemma load_realign_sem_expr
      conf st invst e0
  :
    <<EQ: AssnState.Unary.sem_expr conf st invst e0 =
          AssnState.Unary.sem_expr conf st invst (Infrules.load_realign e0)>>
.
Proof.
  red.
  unfold Infrules.load_realign. des_ifs; ss.
Qed.

