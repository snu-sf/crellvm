Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Require Import TODO.
Require Import TODOProof.

Import Opsem.
Require Import sflib.

Module GVs.
  Definition lessdef (v1 v2:GenericValue): Prop :=
    list_forall2
      (fun vc1 vc2 =>
         Val.lessdef vc1.(fst) vc2.(fst) /\
         vc1.(snd) = vc2.(snd) /\
         (vc1.(fst) = Vundef -> vc2.(fst) <> Vundef -> Val.has_chunkb vc2.(fst) vc2.(snd)))
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
    induction x; ii; ss; des.
    { econs. }
    econs.
    - esplits; eauto. i. ss.
    - apply IHx.
  Qed.

  Lemma lessdef_trans
        x y z
        (LD01: lessdef x y)
        (LD12: lessdef y z)
    :
      <<LD02: lessdef x z>>
  .
  Proof.
    ginduction LD01; ii; ss.
    inv LD12. des. destruct b0, b1, a1; ss. clarify.
    econs; eauto.
    - ss. splits; ss.
      + eapply Val.lessdef_trans; eauto.
      + i; clarify.
        inv H2.
        * eapply H5; eauto.
        * eapply H1; eauto.
    - eapply IHLD01; eauto.
  Qed.

  Lemma lessdef_inject_compose_single mij a b c
        (LD: Val.lessdef a b)
        (INJECT: memory_sim.MoreMem.val_inject mij b c):
    << INJECT: memory_sim.MoreMem.val_inject mij a c >>.
  Proof.
    inv LD; inv INJECT; ss; try (econs; eauto; fail).
  Qed.

  Lemma inject_lessdef_compose_single mij a b c
        (INJECT: memory_sim.MoreMem.val_inject mij a b)
        (LD: Val.lessdef b c):
    << INJECT: memory_sim.MoreMem.val_inject mij a c >>.
  Proof.
    inv LD; inv INJECT; ss; try (econs; eauto; fail).
  Qed.

  Lemma lessdef_inject_compose mij a b c
        (LD: lessdef a b)
        (INJECT: genericvalues_inject.gv_inject mij b c):
    << INJECT: genericvalues_inject.gv_inject mij a c >>.
  Proof.
    red.
    generalize dependent a.
    generalize dependent c.
    induction b; ii; ss.
    { inv LD. destruct c; ss. }
    inv INJECT.
    inv LD; ss. des. destruct a1; ss. clarify.
    econs; eauto.
    { i. clarify. inv H4; ss.
      - eapply CHUNK; eauto.
      - destruct (classic (v1 = Vundef)).
        + clarify.
          inv H1. eapply CHUNK; eauto.
        + inv H1; try eapply H2; ss.
    }
    eapply lessdef_inject_compose_single; eauto.
  Qed.

  Lemma inject_lessdef_compose mij a b c
        (INJECT: genericvalues_inject.gv_inject mij a b)
        (LD: lessdef b c):
    << INJECT: genericvalues_inject.gv_inject mij a c >>.
  Proof.
    red.
    generalize dependent a.
    generalize dependent c.
    induction b; ii; ss.
    { inv LD. destruct a; ss. }
    inv INJECT.
    inv LD; ss. des. destruct b1; ss. clarify.
    econs; eauto.
    - i. clarify.
      destruct (classic (v2 = Vundef)).
      + clarify. apply H4; ss.
      + inv H1; ss.
        apply CHUNK; ss.
    - eapply inject_lessdef_compose_single; eauto.
  Qed.
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

Lemma GV2blocks_in_inv
      a gvs
      (IN: In a (GV2blocks gvs))
  :
    <<INV: exists ofs mc, In ((Values.Vptr a ofs), mc) gvs>>
.
Proof.
  induction gvs; ii; ss; des; ss.
  destruct a0; ss.
  eapply GV2blocks_In_cons in IN.
  des.
  - destruct v; ss. des; ss.
    clarify.
    esplits; eauto.
  - exploit IHgvs; eauto; []; ii; des.
    esplits; eauto.
Qed.

Lemma GV2blocks_incl
      gvs1 gvs2
      (INCL: incl gvs1 gvs2)
  :
        <<INCL: incl (GV2blocks gvs1) (GV2blocks gvs2)>>
.
Proof.
  ii.
  apply GV2blocks_in_inv in H.
  des.
  eapply TODOProof.filter_map_spec; eauto.
Qed.

Lemma GV2blocks_lift
      z ofs mc gvs'
      (IN : In (Values.Vptr z ofs, mc) gvs')
  :
    <<IN: In z (GV2blocks gvs')>>
.
Proof.
  induction gvs'; ii; ss; des; ss; clarify.
  - cbn. left; ss.
  - exploit IHgvs'; eauto; []; ii; des.
    cbn.
    unfold compose in *.
    des_ifs.
    cbn.
    right; ss.
Qed.

Lemma GV2blocks_app_inv z xs ys
      (IN: In z (GV2blocks (xs ++ ys)))
  :
    <<IN: In z (GV2blocks xs) \/ In z (GV2blocks ys)>>
.
Proof.
  generalize dependent ys.
  induction xs; ii; ss; des; ss.
  { right; ss. }
  cbn in IN.
  unfold compose in *; ss.
  destruct a; ss.
  (* destruct v; ss. *)
  des_ifs; ss; cbn.
  - unfold compose; ss.
    des; ss; subst.
    + left. des_ifs.
      ss. left; ss.
    + des_ifs.
      eapply TODOProof.filter_map_inv in IN.
      des.
      eapply in_app in IN.
      des.
      * left.
        ss. right; ss.
        eapply TODOProof.filter_map_spec; eauto.
      * right.
        eapply TODOProof.filter_map_spec; eauto.
  -
    unfold compose; ss.
    eapply TODOProof.filter_map_inv in IN.
    des.
    eapply in_app in IN.
    des.
    + left. des_ifs.
      eapply TODOProof.filter_map_spec; eauto.
    + right.
      eapply TODOProof.filter_map_spec; eauto.
Qed.

(* TODO: Why error_state is defined in GenericValues? *)
(* -> It is used in SoundPostcondCmdAdd. Is it essential? *)
Lemma error_state_neg conf st
      (NERROR_SRC: ~error_state conf st)
  :
    <<NERROR_SRC: ~(stuck_state conf st) \/ exists gv, s_isFinialState conf st = Some gv>>
.
Proof.
  red. unfold not in NERROR_SRC.
  apply imply_to_or.
  i.
  destruct (s_isFinialState conf st) eqn:T.
  { esplits; eauto. }
  exploit NERROR_SRC; eauto.
  { econs; eauto. }
  i; ss.
Qed.
