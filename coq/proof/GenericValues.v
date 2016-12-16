Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Require Import TODO.

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

Lemma final_stuck
      conf st retval
      (FINAL: s_isFinialState conf st = Some retval):
  stuck_state conf st.
Proof.
  ii. des. destruct st, EC0. ss.
  destruct CurCmds0, Terminator0, ECS0; ss.
  - inv H.
  - inv H.
Qed.

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

Definition val2block val :=
  match val with
  | Vptr blck _ => Some blck
  | _ => None
  end.

(* Defining definition with fixpoint makes proof a lot hard *)
(* inductive def ? *)
Definition GV2blocks (gval: GenericValue) := filter_map (val2block <*> fst) gval.

Lemma GV2ptr_In_GV2blocks
      td sz gv b i
        (GV2PTR: GV2ptr td sz gv = Some (Values.Vptr b i))
  :
    <<GV2BLOCKS: In b (GV2blocks gv)>>
.
Proof.
  induction gv; ii; des; ss.
  destruct a; ss. des_ifs. ss.
  left. ss.
Qed.

Lemma GV2blocks_cons
      v m gv
  :
      <<CONS_INV: GV2blocks ((v, m) :: gv) = GV2blocks [(v, m)] ++ GV2blocks gv>>
.
Proof.
  red.
  unfold GV2blocks in *.
  unfold compose in *.
  ss.
  des_ifs.
Qed.

Lemma GV2blocks_In_cons
      b v1 m gv1
      (IN: In b (GV2blocks ((v1, m) :: gv1)))
  :
    <<IN: In b (GV2blocks [(v1, m)]) \/ In b (GV2blocks gv1)>>
.
Proof.
  erewrite GV2blocks_cons in IN.
  apply in_app in IN.
  ss.
Qed.
