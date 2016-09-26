Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.

Import Opsem.
Require Import sflib.

Module GVs.
  Definition lessdef (v1 v2:GenericValue): Prop :=
    list_forall2
      (fun vc1 vc2 =>
         Val.lessdef vc1.(fst) vc2.(fst) /\
         vc1.(snd) = vc2.(snd))
      v1 v2.

  Definition inject (alpha:meminj) (v1 v2:GenericValue): Prop :=
    list_forall2
      (fun vc1 vc2 =>
         val_inject alpha vc1.(fst) vc2.(fst) /\
         vc1.(snd) = vc2.(snd))
      v1 v2.

  Lemma lessdef_refl x:
        <<REFL: lessdef x x>>.
  Proof.
    induction x; ii; ss; des; econs.
    esplits; eauto. apply IHx.
  Qed.

  Lemma lessdef_inject_compose mij a b c
        (LD: lessdef a b)
        (INJECT: genericvalues_inject.gv_inject mij b c):
    << INJECT: genericvalues_inject.gv_inject mij a c >>.
  Proof. Admitted.

  Lemma inject_lessdef_compose mij a b c
        (INJECT: genericvalues_inject.gv_inject mij a b)
        (LD: lessdef b c):
    << INJECT: genericvalues_inject.gv_inject mij a c >>.
  Proof. Admitted.
End GVs.


(* TODO: position *)
Inductive error_state conf st: Prop :=
| error_state_intro
    (STUCK: stuck_state conf st)
    (NFINAL: s_isFinialState conf st = None)
.

Lemma nerror_stuck_final
      conf st
      (NERROR: ~ error_state conf st)
      (STUCK: stuck_state conf st):
  exists retval, s_isFinialState conf st = Some retval.
Proof.
  destruct (s_isFinialState conf st) eqn:X; eauto.
  exfalso. apply NERROR. econs; ss.
Qed.

Lemma nerror_nfinal_nstuck
      conf st1
      (NERROR: ~ error_state conf st1)
      (NFINAL: s_isFinialState conf st1 = None):
  exists st2 e, sInsn conf st1 st2 e.
Proof.
  destruct (classic (stuck_state conf st1)).
  - contradict NERROR. econs; ss.
  - apply NNPP in H. ss.
Qed.
