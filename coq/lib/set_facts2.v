Require Import sflib.
Require Import vellvm.

Require Import syntax_ext.

(* Some facts about equations. *)
Module WFacts2_fun (Import E : DecidableType)(Import M : WSfun E).

  Module F := (WFacts_fun E M).

  Lemma elements_singleton_prop1
    x y s (Hs: singleton y [=] s)
    (H: InA E.eq x (elements s)) :
    E.eq x y.
  Proof.
    apply elements_2 in H.
    apply Hs in H.
    apply F.singleton_iff in H.
    by symmetry.
  Qed.

  Lemma elements_singleton_prop2 y s (Hs: singleton y [=] s) :
    InA E.eq y (elements s).
  Proof.
    apply elements_1.
    apply Hs.
    apply F.singleton_iff.
    reflexivity.
  Qed.

  Lemma elements_singleton_prop3 y s (Hs: singleton y [=] s) :
    exists z,
      E.eq z y /\
      (elements s) = [z].
  Proof.
    remember (elements s) as l.
    generalize dependent (elements_singleton_prop2 y s Hs); intro Hy.
    rewrite <- Heql in Hy.
    destruct l; [inv Hy|].
    exploit (elements_singleton_prop1 e y s Hs); [by rewrite <- Heql; left|].
    intro Heq; exists e; split; [done|].
    destruct l0; [done|].
    generalize (elements_3w s); intro Hss.
    rewrite <- Heql in Hss.
    inv Hss.
    contradict H1.
    exploit (elements_singleton_prop1 e0 y s Hs); [by rewrite <- Heql; right; left|].
    by intro He0; left; eauto.
  Qed.
  
  Lemma fold_singleton_simpl:
    forall {A} f s (i:A) e (Hs: singleton e [=] s),
      exists e',
        E.eq e' e /\
        fold f s i = f e' i.
  Proof.
    intros.
    rewrite fold_1.
    destruct (elements_singleton_prop3 e s Hs) as [x [H1 H2]].
    rewrite H2; simpl.
    by exists x.
  Qed.

  Lemma eq_dec_singleton_eq:
    forall a b
      (Hseq: true = eq_dec (singleton a) (singleton b)),
      E.eq a b.
  Proof.
    intros.
    destruct (eq_dec (singleton a) (singleton b)); inv Hseq.
    generalize dependent (e b); clear e; intro e.
    apply F.singleton_iff.
    apply e.
    by apply F.singleton_iff.
  Qed.

  Lemma eq_dec_singleton_false_1:
    forall a, false = eq_dec (singleton a) empty.
  Proof.
    intros.
    destruct (eq_dec (singleton a) empty); [|done].
    exfalso.
    generalize dependent (e a); clear e; intro e; destruct e.
    apply (F.empty_iff a).
    apply H.
    by apply F.singleton_iff.
  Qed.

  Lemma eq_dec_singleton_false_2:
    forall a, false = eq_dec empty (singleton a).
  Proof.
    intros.
    destruct (eq_dec empty (singleton a)); [|done].
    exfalso.
    generalize dependent (e a); clear e; intro e; destruct e.
    apply (F.empty_iff a).
    apply H0.
    by apply F.singleton_iff.
  Qed.

  Lemma inter_singleton_1:
    forall a, inter (singleton a) (singleton a) [=] singleton a.
  Proof.
    intros a b; constructor; intro H.
    - by apply inter_1 in H.
    - by apply F.inter_iff; split.
  Qed.

  Lemma inter_singleton_2:
    forall a b
      (Hneq: false = eq_dec (singleton a) (singleton b)),
      (inter (singleton a) (singleton b))[=]empty.
  Proof.
    intros a b H.
    destruct (eq_dec (singleton a) (singleton b)); [done|]; clear H.
    intros c; constructor; [|by intro H; apply F.empty_iff in H].
    intro H.
    apply F.inter_iff in H; destruct H.
    apply singleton_1 in H.
    apply singleton_1 in H0.
    generalize (E.eq_trans H (E.eq_sym H0)); clear H H0; intro H.
    contradict n.
    intro d; constructor; intro Hd.
    - apply F.singleton_iff in Hd; apply F.singleton_iff.
      by apply (E.eq_trans (E.eq_sym H) Hd).
    - apply F.singleton_iff in Hd; apply F.singleton_iff.
      by apply (E.eq_trans H Hd).
  Qed.

  Lemma existsb_rev A f (s:list A) :
    existsb f s = existsb f (rev s).
  Proof.
    induction s; simpl; [done|].
    rewrite existsb_app.
    rewrite orb_comm, IHs.
    destruct (existsb f (rev s)); [done|simpl].
    by rewrite orb_false_r.
  Qed.
  
  Lemma in_fold_exists:
    forall x' f s
      (Hmem: mem x' (fold (fun e acc => add (f e) acc) s empty) = true),
      exists x, mem x s /\ E.eq x' (f x).
  Proof.
    intros.
    rewrite fold_1 in Hmem.
    rewrite <- fold_left_rev_right in Hmem.
    apply F.mem_iff in Hmem.
    assert (H: exists x, existsb (F.eqb x) (rev (elements s)) /\ E.eq x' (f x)).
    - generalize dependent Hmem.
      generalize (rev (elements s)) as sl; clear s.
      intro sl; induction sl; intro H; simpl in H.
      + by apply F.empty_iff in H.
      + apply F.add_iff in H; destruct H.
        * exists a; split; [|by apply E.eq_sym].
          unfold existsb; apply orb_true_iff; left.
          unfold F.eqb.
          destruct (E.eq_dec a a); [done|].
          by contradict n.
        * exploit IHsl; eauto.
          clear H; intro H; destruct H as [x [H1 H2]].
          exists x; split; [|done].
          by apply orb_true_iff; right.
    - destruct H as [x [H1 H2]]; exists x.
      split; [|done].
      rewrite F.elements_b.
      by rewrite existsb_rev.
  Qed.      

  Lemma eqb_prop1 a b :
    forall (H:F.eqb a b = true), E.eq a b.
  Proof.
    intros.
    unfold F.eqb in H.
    by destruct (E.eq_dec a b) in H.
  Qed.
End WFacts2_fun.

Module AtomSetFacts2 := WFacts2_fun AtomDT AtomSetImpl.
Module IdExtSetFacts2 := WFacts2_fun IdExtDT IdExtSetImpl.
Module ValueExtSetFacts2 := WFacts2_fun ValueExtDT ValueExtSetImpl.
Module EqRegSetFacts2 := WFacts2_fun EqRegDT EqRegSetImpl.
Module EqHeapSetFacts2 := WFacts2_fun EqHeapDT EqHeapSetImpl.
Module NeqRegSetFacts2 := WFacts2_fun NeqRegDT NeqRegSetImpl.
