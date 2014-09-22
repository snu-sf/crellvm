Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import syntax_ext.
Require Import validator_aux.
Require Import validator.
Require Import validator_props.
Require Import logical_step.
Require Import state_props.
Require Import hints.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import syntax_ext.
Require Import basic_const_inject.

Require Import hint_sem_props_implies.
Require Import hint_sem_props_resolve_defs.
Require Import hint_sem_props_resolve.
Require Import hint_sem_props_proceed.
Require Import hint_sem_props_proceed_call.
Require Import hint_sem_props_proceed_branch.

Require Import paco.
Require Import Coq.Program.Equality.

Import Opsem.


(* lemmas *)

Lemma is_return_or_not st : (is_return st) \/ (~ is_return st).
Proof.
  unfold is_return. destruct st. destruct ECS0; auto.
  destruct (CurCmds e); [|right; by intros [? ?]].
  destruct (Terminator e); auto;
    try by (right; intros [? ?]).
Qed.

Lemma ocons_inv A (hd:A) tl :
  ocons (ret hd) tl = hd :: tl.
Proof. done. Qed.

Lemma ocons_inv_merror A (tl:list A) :
  ocons merror tl = tl.
Proof. done. Qed.

Lemma destruct_cfg cfg:
  cfg = {|
    CurSystem := (CurSystem cfg);
    CurTargetData := (CurTargetData cfg);
    CurProducts := (CurProducts cfg);
    Globals := (Globals cfg);
    FunTable := (FunTable cfg)
  |}.
Proof. by destruct cfg. Qed.

Lemma call_uniq cfg v lc fid1 fid2
  (H1: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdef,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd /\ getFdefID fd = fid1)
  (H2: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdef,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd /\ getFdefID fd = fid2) :
  fid1 = fid2.
Proof.
  destruct H1 as [fptrs1 [fptr1 [fdef1 [Hfptrs1 [Hfptr1 [Hfdef1 Hfid1]]]]]].
  destruct H2 as [fptrs2 [fptr2 [fdef2 [Hfptrs2 [Hfptr2 [Hfdef2 Hfid2]]]]]].
  rewrite Hfptrs1 in Hfptrs2. inv Hfptrs2.
  inv Hfptr1. inv Hfptr2.
  rewrite Hfdef1 in Hfdef2. inv Hfdef2.
  done.
Qed.

Lemma call_uniq' cfg v lc fid
  fptrs (Hfptrs: getOperandValue (CurTargetData cfg) v lc (Globals cfg) = ret fptrs)
  fptr (Hfptr: fptr @ fptrs)
  fd (Hfd: lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr = ret fd)
  (H2: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdef,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd /\ getFdefID fd = fid) :
  getFdefID fd = fid.
Proof.
  eapply call_uniq; eauto.
  eexists. eexists. eexists. eauto.
Qed.

Lemma excall_uniq' cfg v lc fd1 fd2
  fptrs1 (Hfptrs1: getOperandValue (CurTargetData cfg) v lc (Globals cfg) = ret fptrs1)
  fptr1 (Hfptr1: fptr1 @ fptrs1)
  (Hfd1: lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr1 = ret fd1)
  fptrs2 (Hfptrs2: getOperandValue (CurTargetData cfg) v lc (Globals cfg) = ret fptrs2)
  fptr2 (Hfptr2: fptr2 @ fptrs2)
  (Hfd2: lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr2 = ret fd2) :
  fptrs1 = fptrs2 /\ fptr1 = fptr2 /\ fd1 = fd2.
Proof.
  rewrite Hfptrs1 in Hfptrs2. inv Hfptrs2.
  inv Hfptr1. inv Hfptr2.
  rewrite Hfd1 in Hfd2. inv Hfd2.
  done.
Qed.

Lemma call_excall cfg v lc fid1
  (H1: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdef,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd /\ getFdefID fd = fid1)
  (H2: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdec,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd) :
  False.
Proof.
  destruct H1 as [fptrs1 [fptr1 [fdef1 [Hfptrs1 [Hfptr1 [Hfdef1 Hfid1]]]]]].
  destruct H2 as [fptrs2 [fptr2 [fdef2 [Hfptrs2 [Hfptr2 Hfdef2]]]]].
  rewrite Hfptrs1 in Hfptrs2. inv Hfptrs2.
  inv Hfptr1. inv Hfptr2.
  unfold lookupFdefViaPtr in Hfdef1.
  unfold lookupExFdecViaPtr in Hfdef2.
  destruct (lookupFdefViaGVFromFunTable (FunTable cfg) fptr2); [simpl in *|done].
  by rewrite Hfdef1 in Hfdef2.
Qed.

Lemma call_excall' cfg v lc fid1
  (H1: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdef,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd /\ getFdefID fd = fid1)
  fptrs (Hfptrs: getOperandValue (CurTargetData cfg) v lc (Globals cfg) = ret fptrs)
  fptr (Hfptr: fptr @ fptrs)
  fd (Hfd: lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr = ret fd) :
  False.
Proof.
  eapply call_excall; eauto.
  (repeat eexists); splits; eauto.
  by inv Hfptr; eauto.
Qed.

Lemma call'_excall cfg v lc
  fptrs (Hfptrs: getOperandValue (CurTargetData cfg) v lc (Globals cfg) = ret fptrs)
  fptr (Hfptr: fptr @ fptrs)
  fd (Hfd: lookupFdefViaPtr (CurProducts cfg) (FunTable cfg) fptr = ret fd)
  (H2: exists fptrs : GVs,
    exists fptr : GenericValue,
      exists fd : fdec,
        getOperandValue (CurTargetData cfg) v lc
        (Globals cfg) = ret fptrs /\
        fptr @ fptrs /\
        lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr =
        ret fd) :
  False.
Proof.
  eapply call_excall; eauto.
  (repeat eexists); splits; eauto.
  by inv Hfptr; eauto.
Qed.


(* logical states *)

Inductive match_state_ns : (@State DGVs) -> noop_stack_t -> Prop :=
| _match_state_ns : forall state ns, length (ECS state) = length ns -> match_state_ns state ns.
Structure lState := mkLState {
  state : @State DGVs;
  ns : noop_stack_t;
  Hmatch: match_state_ns state ns
}.

Lemma lState_eq lst1 lst2
  (Hstate: lst1.(state) = lst2.(state))
  (Hns: lst1.(ns) = lst2.(ns)) :
  lst1 = lst2.
Proof.
  destruct lst1, lst2. simpl in *. subst.
  f_equal. apply proof_irrelevance.
Qed.

Lemma destruct_lState lst :
  lst = {| state := lst.(state); ns := lst.(ns); Hmatch := lst.(Hmatch) |}.
Proof. by destruct lst. Qed.


(* logical step *)

Inductive lsInsn (cfg:Config) (pnoops:products_noop_t) : lState -> lState -> trace -> Prop :=
| _lsInsn :
  forall lst1 lst2 na tr
    (H:logical_semantic_step cfg pnoops lst1.(state) lst2.(state) lst1.(ns) lst2.(ns) na tr),
    lsInsn cfg pnoops lst1 lst2 tr.

Fixpoint stutter_num (n:noop_t) : nat :=
  match n with
    | nil => O
    | hd::tl =>
      if my_beq_nat my_O (idx_noop hd)
      then S (stutter_num tl)
      else stutter_num tl
  end.

Lemma stutter_num_noop_idx_zero_remove n x
  (H: S x = stutter_num n) :
  x = stutter_num (noop_idx_zero_remove n).
Proof.
  generalize dependent x.
  induction n; intros x H; [by inv H|].
  simpl in *. remember (idx_noop a) as ia.
  destruct ia; [by inv H|].
  exploit IHn; eauto.
  unfold stutter_num. fold stutter_num.
  by rewrite <- Heqia.
Qed.

Lemma stutter_num_noop_idx_zero_exists n x
  (H: S x = stutter_num n) :
  noop_idx_zero_exists n.
Proof.
  generalize dependent x.
  induction n; intros x H; [by inv H|].
  simpl in *. destruct (idx_noop a); [done|].
  exploit IHn; eauto.
Qed.

Lemma stutter_num_noop_idx_zero_exists' n
  (H: O = stutter_num n) :
  noop_idx_zero_exists n = false.
Proof.
  generalize dependent H.
  induction n; intro H; [by inv H|].
  simpl in *. destruct (idx_noop a); [done|].
  exploit IHn; eauto.
Qed.

Lemma noop_idx_zero_exists_stutter_num' n
  (H: noop_idx_zero_exists n = false) :
  O = stutter_num n.
Proof.
  generalize dependent H.
  induction n; intro H; [by inv H|].
  simpl in *. destruct (idx_noop a); [done|].
  exploit IHn; eauto.
Qed.

Lemma logical_semantic_step_lsInsn'
  cfg pnoops lst1 st2 ns2 na tr
  (H: logical_semantic_step cfg pnoops lst1.(state) st2 lst1.(ns) ns2 na tr) :
  match_state_ns st2 ns2.
Proof.
  econs. destruct lst1. simpl in *.
  destruct state0, st2. inv Hmatch0. simpl in *.
  inv H. inv Hpop.
  - inv Hnoop; [|by destruct rcmd].
    unfold pop_one_X in Hpop0.
    remember (noop_idx_zero_exists hpn) as z. destruct z.
    + inv Hpop0. destruct Hstep. subst.
      inv H. by inv Hnnn.
    + remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [done|].
      inv Hpop0. simpl in *.
      destruct ec. simpl in *.
      inv Hnnn; simpl in *; try done.
      * by inv Hstep.
      * rewrite (destruct_cfg cfg) in Hstep. inv Hstep; simpl in *; try done; try omega.
        by exploit call_excall'; eauto.
      * rewrite (destruct_cfg cfg) in Hstep. inv Hstep; simpl in *; try done; try omega.
        by exploit call'_excall; eauto.
  - simpl in *. subst. simpl in *.
    unfold pop_one_X in Hpop0. 
    remember (noop_idx_zero_exists hpn) as z. destruct z; [done|].
    remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [|done].
    inv Hnoop; [by inv Hnnn|].
    destruct ec. inv Hnnn; simpl in *.
    + destruct Hret as [? Hret]. subst.
      destruct Terminator0; try done.
      * inv Hstep. simpl in *. omega.
      * inv Hstep. simpl in *. omega.
    + destruct Hbrc as [? Hbrc]. subst.
      destruct Terminator0; try done.
      * inv Hstep. simpl. omega.
      * inv Hstep. simpl. omega.
Qed.

Lemma logical_semantic_step_lsInsn
  cfg pnoops lst1 st2 ns2 na tr
  (H: logical_semantic_step cfg pnoops lst1.(state) st2 lst1.(ns) ns2 na tr) :
  exists Hmatch2, lsInsn cfg pnoops lst1 (mkLState st2 ns2 Hmatch2) tr.
Proof.
  exploit logical_semantic_step_lsInsn'; eauto.
  intro Hmatch2. exists Hmatch2. econs. eauto.
Qed.

Inductive no_stuttering lst : Prop :=
| no_stuttering_nil :
  forall (H : nil = (ns lst)),
    no_stuttering lst
| no_stuttering_cons :
  forall n nstk (H : n::nstk = (ns lst))
    (Hn: O = stutter_num n),
    no_stuttering lst.

Lemma no_stuttering_dec lst : {no_stuttering lst} + {~ no_stuttering lst}.
Proof.
  destruct lst. destruct ns0; [by left; econs|].
  remember (stutter_num n) as x. destruct x.
  - left. eapply no_stuttering_cons; simpl; eauto.
  - right. intro H. inv H; simpl in *; try done. inv H0. omega.
Defined.

Lemma no_stuttering_lsInsn cfg pnoops lst1 lst2 tr
  (Hstut: no_stuttering lst1)
  (H: lsInsn cfg pnoops lst1 lst2 tr) :
  (sInsn cfg lst1.(state) lst2.(state) tr).
Proof.
  inv H. inv H0.
  inv Hstut; rewrite Hpn in H; inv H.
  exploit stutter_num_noop_idx_zero_exists'; eauto. intro Hzn.
  inv Hpop.
  - unfold pop_one_X in Hpop0. rewrite Hzn in Hpop0.
    remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [done|].
    inv Hpop0. inv Hnoop; [|by inv Hpop]. inv Hnnn; try done.
  - unfold pop_one_X in Hpop0. rewrite Hzn in Hpop0.
    remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [done|].
    inv Hpop0.
Qed.
    
Lemma stuttering_lsInsn cfg pnoops lst1 lst2 tr
  (Hstut: ~ no_stuttering lst1)
  (H: lsInsn cfg pnoops lst1 lst2 tr) :
  (lst1.(state) = lst2.(state) /\ length lst1.(ns) = length lst2.(ns) /\ tr = E0).
Proof.
  inv H. inv H0. inv Hpop.
  - unfold pop_one_X in Hpop0.
    remember (noop_idx_zero_exists hpn) as z. destruct z.
    + inv Hpop0. destruct Hstep. subst.
      splits; auto.
      inv Hnoop; [|by inv Hpop].
      inv Hnnn; try done. simpl in *. by rewrite Hpn.
    + remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [done|].
      inv Hpop0.
      exfalso. apply Hstut. eapply no_stuttering_cons; eauto.
      by apply noop_idx_zero_exists_stutter_num'.
  - unfold pop_one_X in Hpop0.
    remember (noop_idx_zero_exists hpn) as z. destruct z.
    + inv Hpop0.
    + remember (CurCmds ec) as cmds. destruct cmds as [|c cmds]; [|done].
      exfalso. apply Hstut. eapply no_stuttering_cons; eauto.
      by apply noop_idx_zero_exists_stutter_num'.
Qed.

Lemma lsInsn_sInsn cfg pnoops lst1 lst2 tr
  (H: lsInsn cfg pnoops lst1 lst2 tr) :
  (sInsn cfg lst1.(state) lst2.(state) tr) \/
  (lst1.(state) = lst2.(state) /\ length lst1.(ns) = length lst2.(ns) /\ tr = E0).
Proof.
  destruct (no_stuttering_dec lst1).
  - left. eapply no_stuttering_lsInsn; eauto.
  - right. eapply stuttering_lsInsn; eauto.
Qed.    


(* logical steps *)

Inductive lsop_star (cfg:Config) (pnoops:products_noop_t) : lState -> lState -> trace -> Prop :=
| lsop_star_nil : forall lstate, lsop_star cfg pnoops lstate lstate E0
| lsop_star_cons : forall lst1 lst2 lst3 tr1 tr2,
  lsInsn cfg pnoops lst1 lst2 tr1 ->
  lsop_star cfg pnoops lst2 lst3 tr2 ->
  lsop_star cfg pnoops lst1 lst3 (Eapp tr1 tr2)
.

Inductive lsop_star_rev (cfg:Config) (pnoops:products_noop_t) : lState -> lState -> trace -> Prop :=
| lsop_star_rev_nil : forall lstate, lsop_star_rev cfg pnoops lstate lstate E0
| lsop_star_rev_snoc : forall lst1 lst2 lst3 tr1 tr2,
  lsop_star_rev cfg pnoops lst1 lst2 tr1 ->
  lsInsn cfg pnoops lst2 lst3 tr2 ->
  lsop_star_rev cfg pnoops lst1 lst3 (Eapp tr1 tr2)
.

Inductive lsop_plus (cfg:Config) (pnoops:products_noop_t) : lState -> lState -> trace -> Prop :=
| lsop_plus_cons : forall lst1 lst2 lst3 tr1 tr2,
  lsInsn cfg pnoops lst1 lst2 tr1 ->
  lsop_star cfg pnoops lst2 lst3 tr2 ->
  lsop_plus cfg pnoops lst1 lst3 (Eapp tr1 tr2)
.

Lemma lsop_star_app cfg pnoops lst1 lst2 lst3 tr12 tr23
  (H12: lsop_star cfg pnoops lst1 lst2 tr12)
  (H23: lsop_star cfg pnoops lst2 lst3 tr23) :
  lsop_star cfg pnoops lst1 lst3 (tr12 ** tr23).
Proof.
  generalize dependent tr23.
  generalize dependent lst3.
  induction H12; intros lst3' tr23 H23.
  - by rewrite E0_left.
  - rewrite Eapp_assoc. econs; eauto.
Qed.

Lemma lsop_star_lsop_star_rev cfg pnoops lst1 lst2 tr
  (H: lsop_star cfg pnoops lst1 lst2 tr) :
  lsop_star_rev cfg pnoops lst1 lst2 tr.
Proof.
  induction H; [by econs|].
  clear H0.
  induction IHlsop_star.
  - rewrite <- E0_left, E0_right. econs; eauto. econs.
  - rewrite <- Eapp_assoc. econs; eauto.
Qed.

Lemma lsop_star_rev_lsop_star cfg pnoops lst1 lst2 tr
  (H: lsop_star_rev cfg pnoops lst1 lst2 tr) :
  lsop_star cfg pnoops lst1 lst2 tr.
Proof.
  induction H; [by econs|].
  clear H.
  induction IHlsop_star_rev.
  - rewrite E0_left, <- E0_right. econs; eauto. econs.
  - rewrite Eapp_assoc. econs; eauto.
Qed.

Lemma lsop_star_sop_star cfg pnoops lst1 lst2 tr
  (H: lsop_star cfg pnoops lst1 lst2 tr) :
  sop_star cfg lst1.(state) lst2.(state) tr.
Proof.
  induction H; auto.
  exploit lsInsn_sInsn; eauto.
  intros [H'|[H'0 [H'1 H'2]]].
  - econs; eauto.
  - subst. by rewrite <- H'0 in IHlsop_star.
Qed.

Lemma lsop_plus_lsop_star cfg pnoops lst1 lst2 tr
  (Hsem: lsop_plus cfg pnoops lst1 lst2 tr) :
  lsop_star cfg pnoops lst1 lst2 tr.
Proof. inv Hsem. econs; eauto. Qed.

Lemma lsop_plus_snoc cfg pnoops lst1 lst2 lst3 tr1 tr2
  (H12: lsop_star cfg pnoops lst1 lst2 tr1)
  (H23: lsInsn cfg pnoops lst2 lst3 tr2) :
  lsop_plus cfg pnoops lst1 lst3 (Eapp tr1 tr2).
Proof.
  generalize dependent tr2.
  generalize dependent lst3.
  induction H12; intros lst3' tr2' H23.
  - rewrite E0_left, <- E0_right. econs; eauto. econs.
  - rewrite Eapp_assoc. econs; eauto.
    apply lsop_plus_lsop_star.
    by apply IHlsop_star.
Qed.


(* stuttering *)

Definition lsInsn_uniq cfg pnoops lst1 :=
  forall
    lst2 tr (Hlst2: lsInsn cfg pnoops lst1 lst2 tr)
    lst2' tr' (Hlst2': lsInsn cfg pnoops lst1 lst2' tr'),
    lst2 = lst2' /\ tr = tr'.

Inductive lstutter_star (cfg:Config) (pnoops:products_noop_t) : lState -> lState -> Prop :=
| lstutter_star_nil : forall lstate, lstutter_star cfg pnoops lstate lstate
| lstutter_star_cons : forall lst1 lst2 lst3,
  lsInsn cfg pnoops lst1 lst2 E0 ->
  lsInsn_uniq cfg pnoops lst1 ->
  lst1.(state) = lst2.(state) ->
  lstutter_star cfg pnoops lst2 lst3 ->
  lstutter_star cfg pnoops lst1 lst3
.

Lemma lstutter_star_snoc cfg pnoops lst1 lst2 lst3
  (H: lstutter_star cfg pnoops lst1 lst2)
  (Hinsn: lsInsn cfg pnoops lst2 lst3 E0)
  (Huniq: lsInsn_uniq cfg pnoops lst2)
  (Hsts: lst2.(state) = lst3.(state)) :
  lstutter_star cfg pnoops lst1 lst3.
Proof.
  induction H.
  - econs; eauto. econs.
  - econs; eauto.
Qed.

Lemma lstutter_star_state cfg pnoops lst1 lst2
  (H: lstutter_star cfg pnoops lst1 lst2) :
  lst1.(state) = lst2.(state).
Proof.
  induction H; auto.
  by rewrite H1.
Qed.

Lemma lstutter_star_lsop_star cfg pnoops lst1 lst2
  (H: lstutter_star cfg pnoops lst1 lst2) :
  lsop_star cfg pnoops lst1 lst2 E0.
Proof.
  induction H; [by econs|].
  rewrite <- E0_right. econs; eauto.
Qed.

Lemma stuttering_lsInsn_uniq cfg pnoops lst
  (Hstut: ~ no_stuttering lst) :
  lsInsn_uniq cfg pnoops lst.
Proof.
  destruct lst. destruct state0. destruct ns0.
  { exfalso. apply Hstut. by econs. }
  remember (stutter_num n) as x. destruct x.
  { exfalso. apply Hstut. eapply no_stuttering_cons; simpl; eauto. }
  exploit stutter_num_noop_idx_zero_exists; eauto. clear. intro Hz.
  repeat intro. inv Hlst2. inv Hlst2'. simpl in *.
  inv H. inv Hec. inv Hpn.
  inv H0. inv Hec. inv Hpn.
  inv Hpop; unfold pop_one_X in *; rewrite Hz in *; try done. inv Hpop1.
  inv Hpop0; unfold pop_one_X in *; rewrite Hz in *; try done. inv Hpop.
  destruct Hstep. destruct Hstep0. subst.
  inv Hnoop; [|done]. inv Hnoop0; [|done].
  inv Hnnn; try done. inv Hnnn0; try done.
  simpl in *. split; [|done].
  apply lState_eq.
  by rewrite H3.
  by rewrite <- H4.
Qed.

Lemma stutter_lState
  cfg pnoops lst1 :
  exists lst2,
    lstutter_star cfg pnoops lst1 lst2 /\
    no_stuttering lst2.
Proof.
  destruct lst1. simpl in *.
  destruct ns0; simpl in *; [by eexists; splits; econs|].
  inversion Hmatch0. subst.
  remember (ECS state0) as ecs1. destruct ecs1; [by inv H|inv H].
  remember (stutter_num n) as x. generalize dependent Heqx.
  generalize dependent ns0.
  generalize dependent n.
  induction x; intros n1 ns1 Hmatch Hl Hx.
  { eexists. splits; try by econs. by eapply no_stuttering_cons. }
  exploit (logical_semantic_step_lsInsn cfg pnoops (mkLState state0 (n1::ns1) Hmatch) state0 (noop_idx_zero_remove n1 :: ns1) merror E0).
  { econs; simpl; eauto.
    + econs; eauto.
      * unfold pop_one_X.
        erewrite stutter_num_noop_idx_zero_exists; eauto.
      * eauto.
    + simpl. rewrite <- ocons_inv_merror. econs.
      by econs.
    + done.
  }
  intros [Hmatch2 HlsInsn].
  exploit (IHx (noop_idx_zero_remove n1) ns1 Hmatch2); eauto.
  { by apply stutter_num_noop_idx_zero_remove. }
  intros [lst2 [Hlst2 Hstut]].
  exists lst2. split; auto.
  econs; eauto.
  exploit stutter_num_noop_idx_zero_exists; eauto. clear. intro Hz.
  repeat intro. inv Hlst2. inv Hlst2'. simpl in *.
  inv H. inv Hec. inv Hpn.
  inv H0. inv Hec. inv Hpn.
  inv Hpop; unfold pop_one_X in *; rewrite Hz in *; try done. inv Hpop1.
  inv Hpop0; unfold pop_one_X in *; rewrite Hz in *; try done. inv Hpop.
  destruct Hstep. destruct Hstep0. subst.
  inv Hnoop; [|done]. inv Hnoop0; [|done].
  inv Hnnn; try done. inv Hnnn0; try done.
  simpl in *. split; [|done].
  apply lState_eq; [done|].
  by rewrite <- H2.
Qed.

Lemma sInsn_no_stuttering'
  cfg pnoops lst1 st2 tr
  (Hstut: no_stuttering lst1)
  (Hsem: sInsn cfg lst1.(state) st2 tr) :
  exists na, exists ns2,
    logical_semantic_step cfg pnoops lst1.(state) st2 lst1.(ns) ns2 na tr.
Proof.
  destruct lst1 as [st1 ns1]. inversion_clear Hmatch0. simpl in *.
  destruct ns1; [by inv Hsem|].
  inv Hstut; [done|]. inv H0.
  exploit stutter_num_noop_idx_zero_exists'; eauto. intro Hzn.
  exploit is_call_or_not; [by eexists; eexists; eauto|].
  intros [[fid Hfid]|Hfid]; simpl in *.
  { destruct st1. destruct ECS0; [by inv Hsem|]. destruct e.
    destruct CurCmds0; [done|]. destruct c; try done.
    generalize Hsem. intro Hsem'.
    rewrite (destruct_cfg cfg) in Hsem'.
    inv Hsem'; [|by exploit call_excall'; eauto].
    eexists. eexists. econs; simpl; eauto; simpl.
    + econs; eauto. unfold pop_one_X. by rewrite Hzn.
    + econs; eauto. eapply logical_semantic_step_noop_cmd_call; eauto.
      exploit call_uniq'; eauto. intro. subst. simpl in *.
      unfold lookupFdefViaPtr in H24.
      destruct (lookupFdefViaGVFromFunTable (FunTable cfg) fptr); [simpl in H24|done].
      exploit lookupFdefViaIDFromProducts_ideq; eauto. intro. subst.
      done.
    + done.
  }
  destruct (is_return_or_not st1) as [Hret|Hret].
  { destruct st1. destruct ECS0; [by inv Hsem|]. destruct e.
    simpl in Hret. destruct Hret as [? Hret]. subst.
    destruct Terminator0; try done.
    + generalize Hsem. intro Hsem'.
      rewrite (destruct_cfg cfg) in Hsem'. inv Hsem'.
      eexists. eexists. econs; simpl; eauto; simpl.
      * instantiate (2 := nil). eapply pop_one_terminator; eauto. unfold pop_one_X. erewrite stutter_num_noop_idx_zero_exists'; eauto.
      * simpl. rewrite <- (ocons_inv_merror noop_t).
        eapply logical_semantic_step_noop_stk_term; eauto. econs; simpl; eauto.
      * done.
    + generalize Hsem. intro Hsem'.
      rewrite (destruct_cfg cfg) in Hsem'. inv Hsem'.
      eexists. eexists. econs; simpl; eauto; simpl.
      * instantiate (2 := nil). eapply pop_one_terminator; eauto. unfold pop_one_X. erewrite stutter_num_noop_idx_zero_exists'; eauto.
      * simpl. rewrite <- (ocons_inv_merror noop_t).
        eapply logical_semantic_step_noop_stk_term; eauto. econs; simpl; eauto.
      * done.
  }
  (* cmd *)
  destruct st1. destruct ECS0; [by inv Hsem|]. destruct e.
  simpl in Hfid, Hret. generalize Hsem. intro Hsem'.
  rewrite (destruct_cfg cfg) in Hsem'. inv Hsem';
    (try by exploit Hret);
    (try by eexists; eexists; econs; simpl; eauto; simpl;
      [econs; eauto; unfold pop_one_X; erewrite stutter_num_noop_idx_zero_exists'; eauto
      |econs; eapply logical_semantic_step_noop_cmd_cmd; eauto
      |done]).
  - eexists. eexists. econs; simpl in *; eauto; simpl.
    + instantiate (2 := nil). eapply pop_one_terminator; eauto. unfold pop_one_X. erewrite stutter_num_noop_idx_zero_exists'; eauto.
    + eapply logical_semantic_step_noop_stk_term; eauto. eapply logical_semantic_step_noop_terminator_brc; eauto. econs; eauto.
      simpl. eexists. eexists. splits; eauto.
      instantiate (1 := if isGVZero (CurTargetData cfg) c then l2 else l1).
      by destruct (isGVZero (CurTargetData cfg) c).
    + done.
  - eexists. eexists. econs; simpl in *; eauto; simpl.
    + instantiate (2 := nil). eapply pop_one_terminator; eauto. unfold pop_one_X. erewrite stutter_num_noop_idx_zero_exists'; eauto.
    + eapply logical_semantic_step_noop_stk_term; eauto. eapply logical_semantic_step_noop_terminator_brc; eauto. econs; eauto.
      simpl. eauto.
    + done.
  - exfalso. eapply Hfid. simpl.
    eexists. eexists. eexists. eauto.
  - eexists. eexists. econs; simpl; eauto; simpl.
    + simpl. econs; eauto. unfold pop_one_X. erewrite stutter_num_noop_idx_zero_exists'; eauto.
    + simpl. rewrite <- (ocons_inv_merror noop_t). econs. eapply logical_semantic_step_noop_cmd_excall; eauto. simpl.
      eexists. eexists. eexists. eauto.
    + done.
Qed.

Lemma sInsn_no_stuttering
  cfg pnoops lst1 st2 tr
  (Hstut: no_stuttering lst1)
  (Hsem: sInsn cfg lst1.(state) st2 tr) :
  exists lst2,
    lsInsn cfg pnoops lst1 lst2 tr /\
    st2 = lst2.(state).
Proof.
  exploit sInsn_no_stuttering'; eauto. instantiate (1 := pnoops).
  intros [na [ns2 Hinsn]].
  exploit logical_semantic_step_lsInsn; eauto. intros [Hmatch Hlinsn].
  eexists ({| state := st2; ns := ns2; Hmatch := _ |}).
  split; [by eauto|done].
Qed.


(* on physical/logical steps *)

Lemma sInsn_lsop_plus
  cfg pnoops lst1 st2 tr
  (Hsem: sInsn cfg lst1.(state) st2 tr) :
  exists lst2,
    lsop_plus cfg pnoops lst1 lst2 tr /\
    st2 = lst2.(state).
Proof.
  generalize (stutter_lState cfg pnoops lst1). intros [mst [Hmst Hstut]].
  exploit sInsn_no_stuttering; eauto.
  { erewrite <- lstutter_star_state; eauto. }
  instantiate (1 := pnoops).
  intros [lst2 [Hlinsn ?]]. subst.
  exists lst2. split; [|done].
  rewrite <- E0_left. eapply lsop_plus_snoc; eauto.
  by apply lstutter_star_lsop_star.
Qed.

Lemma sop_star_lsop_star
  cfg pnoops lst1 st2 tr
  (Hsem: sop_star cfg lst1.(state) st2 tr) :
  exists lst2,
    lsop_star cfg pnoops lst1 lst2 tr /\
    st2 = lst2.(state) /\
    no_stuttering lst2.
Proof.
  dependent induction Hsem.
  { generalize (stutter_lState cfg pnoops lst1). intros [est [Hest Hstut]].
    exists est. splits; [idtac|idtac|done].
    { by apply lstutter_star_lsop_star. }
    { by erewrite lstutter_star_state; eauto. }
  }
  exploit sInsn_lsop_plus; eauto. instantiate (1 := pnoops). intros [mst [Hmst ?]]. subst.
  exploit IHHsem; eauto. intros [est [Hest [? Hstut]]]. subst.
  eexists. split; [|done].
  eapply lsop_star_app; eauto.
  by apply lsop_plus_lsop_star.
Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
