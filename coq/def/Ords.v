Require Import syntax.
Require Import alist.

Require Import infrastructure.
Require vellvm. (* In order to avoid name clash on "comparison", I didn't Import it *)

Require Import sflib.
Require Export Coqlib.
Export LLVMsyntax.
Export LLVMinfra.

Require Import Decs.
Require Import TODO.
(* For "all_once" tactic. TODO: move this to TODOProof *)
Require Import TODOProof.
(* for des_ifs_safe tac *)
(* I checked dependency, but conceptually this may not good.. *)
(* file in def/ imports file in proof/ *)


Print Orders.OrderedType.
Print OrderedType.OrderedType.
(* Which one to use? *)
Print MSetAVL.Make.
(* MSet uses Orders.OrderedType. We go for that. *)
(* FYI: OrderedType.OrderedType is only for backward compatibility: *)
(* https://coq.inria.fr/library/ *)





Require Import Orders.
(* Because "Orders" name is already used, I choose "Ords" as this file's name *)
Require Import OrdersAlt.
Print OrdersAlt.
Print OrdersAlt.OrderedTypeAlt.
(* It seems convenient, but I will stick to standard. *)
(* I expect libraries are well engineered with standard, but I am unsure for Alt. *)
Print OrdersFacts.
Print OrdersTac.
(* Print OrdersEx. *) (* TODO: It exists in stlib web reference. Why not here? *)
Print OrdersLists.


Set Implicit Arguments.


Require Import Recdef.
(* https://coq.inria.fr/refman/Reference-Manual004.html#sec78 *)
(* Defines a recursive function by well founded recursion. The module Recdef of the standard library must be loaded for this feature. The {} annotation is mandatory and must be one of the following:  *)



Local Open Scope nat.

Module OrdIdx.

  Definition t := nat.

  Definition zero: t := 0.
  Definition one: t := 1.
  Definition two: t := 2.
  Definition three: t := 3.
  Definition four: t := 4.
  Definition five: t := 5.
  Definition six: t := 6.
  Definition seven: t := 7.
  Definition eight: t := 8.
  Definition nine: t := 9.
  Definition onezero: t := 10.
  Definition oneone: t := 11.
  Definition onetwo: t := 12.
  Definition onethree: t := 13.
  Definition onefour: t := 14.
  Definition onefive: t := 15.
  Definition onesix: t := 16.
  Definition oneseven: t := 17.
  Definition oneeight: t := 18.
  Definition onenine: t := 19.

  Definition compare: t -> t -> comparison := Nat.compare.

End OrdIdx.

Notation "0" := OrdIdx.zero : OrdIdx_scope.
Notation "1" := OrdIdx.one : OrdIdx_scope.
Notation "2" := OrdIdx.two : OrdIdx_scope.
Notation "3" := OrdIdx.three : OrdIdx_scope.
Notation "4" := OrdIdx.four : OrdIdx_scope.
Notation "5" := OrdIdx.five : OrdIdx_scope.
Notation "6" := OrdIdx.six : OrdIdx_scope.
Notation "7" := OrdIdx.seven : OrdIdx_scope.
Notation "8" := OrdIdx.eight : OrdIdx_scope.
Notation "9" := OrdIdx.nine : OrdIdx_scope.
Notation "10" := OrdIdx.onezero : OrdIdx_scope.
Notation "11" := OrdIdx.oneone : OrdIdx_scope.
Notation "12" := OrdIdx.onetwo : OrdIdx_scope.
Notation "13" := OrdIdx.onethree : OrdIdx_scope.
Notation "14" := OrdIdx.onefour : OrdIdx_scope.
Notation "15" := OrdIdx.onefive : OrdIdx_scope.
Notation "16" := OrdIdx.onesix : OrdIdx_scope.
Notation "17" := OrdIdx.oneseven : OrdIdx_scope.
Notation "18" := OrdIdx.oneeight : OrdIdx_scope.
Notation "19" := OrdIdx.onenine : OrdIdx_scope.

Local Open Scope OrdIdx_scope.
Local Close Scope Z_scope.
Local Close Scope nat_scope.

(* Axiom addr_compare: forall A, A -> A -> bool. *)
(* Axiom addr_compare_spec: forall A (a0 a1: A), addr_compare a0 a1 = true -> a0 = a1. *)
(* Axiom wrap_compare: forall A (f: A -> A -> comparison), A -> A -> comparison. *)
Definition wrap_compare A (f: A -> A -> comparison): A -> A -> comparison := f.
Hint Unfold wrap_compare.

Definition lazy_comparison := unit -> comparison.

(* tactics *)

Ltac solve_leibniz_ cmp CL :=
  repeat match goal with
         | [H:cmp ?a ?b = Eq |- _] => apply CL in H
         end; subst.

Ltac finish_refl_ cmp REFL:=
  try match goal with
      | [H: cmp ?a ?a = Lt |- _] =>
        rewrite REFL in H; congruence

      | [H: cmp ?a ?a = Gt |- _] =>
        rewrite REFL in H; congruence
      end;
  try by apply REFL.

Ltac apply_trans_ cmp TRANS :=
  try match goal with
      | [H1: cmp ?x ?y = ?c, H2: cmp ?y ?x = ?c |- _] =>
        exploit (TRANS c x y x); eauto; (idtac; []; i);
        exploit (TRANS c y x y); eauto; (idtac; []; i)
      end;
  try match goal with
      | [H1: cmp ?x ?y = ?c, H2: cmp ?y ?z = ?c |- _] =>
        exploit (TRANS c x y z); eauto; (idtac; []; i)
      end.

Ltac comp_sym comp sym :=
  match goal with
  | [ |- context[match comp ?a ?b with _ => _ end]] =>
    rewrite (sym a b); destruct (comp a b)
  end; ss.

Section LISTS.

  Fixpoint lexico_order (x0: list lazy_comparison): comparison :=
    match x0 with
    | [] => Eq
    | hd :: tl =>
      match (hd tt) with
      | Eq => lexico_order tl
      | Lt => Lt
      | Gt => Gt
      end
    end
  .
  Definition comparison_trans (a b: comparison): option comparison :=
    match a, b with
    | Lt, Lt => Some Lt
    | Eq, Eq => Some Eq
    | Gt, Gt => Some Gt
    | _, Eq => Some a
    | Eq, _ => Some b
    | _, _ => None
    end.

  (* Lemma comparison_trans_spec *)
  (*       x y c *)
  (*       (TRANS: comparison_trans x y = Some c) *)
  (*   : *)
  (*     <<INV: (x = Eq /\ y = c) *)
  (*            \/ (x = c /\ y = Eq) *)
  (*            \/ (x = c /\ y = c)>> *)
  (* . *)
  (* Proof. *)
  (*   destruct x, y; ss; clarify; *)
  (*     try (by left; ss); right; try (by left; ss); right; ss. *)
  (* Qed. *)

  Lemma comparison_trans_spec
        x y c
    :
      comparison_trans x y = Some c <->
      ((x = Eq /\ y = c)
       \/ (x = c /\ y = Eq)
       \/ (x = c /\ y = c))
  .
  Proof.
    red.
    split; ii.
    - destruct x, y; ss; clarify;
        try (by left; ss); right; try (by left; ss); right; ss.
    - des; clarify; ss; destruct c; ss.
  Qed.

  Lemma comparison_trans_same
        c
    :
      <<SAME: comparison_trans c c = Some c>>
  .
  Proof. destruct c; ss. Qed.

  Lemma comparison_trans_any_lt_result
        c0 c1
        (LT: comparison_trans c0 Lt = Some c1)
    :
      c1 = Lt
  .
  Proof. destruct c0; ss; clarify. Qed.

  Lemma comparison_trans_lt_any_result
        c0 c1
        (LT: comparison_trans Lt c0 = Some c1)
    :
      c1 = Lt
  .
  Proof. destruct c0; ss; clarify. Qed.

  Lemma comparison_trans_any_gt_result
        c0 c1
        (GT: comparison_trans c0 Gt = Some c1)
    :
      c1 = Gt
  .
  Proof. destruct c0; ss; clarify. Qed.

  Lemma comparison_trans_gt_any_result
        c0 c1
        (GT: comparison_trans Gt c0 = Some c1)
    :
      c1 = Gt
  .
  Proof. destruct c0; ss; clarify. Qed.

  Definition compare_list X (compare: X -> X -> comparison) :=
    fix compare_list_ (a0 b0: list X): comparison :=
      match a0, b0 with
      | a :: a1, b :: b1 => lexico_order [fun _ => (compare a b) ; fun _ => (compare_list_ a1 b1)]
      | [], [] => Eq
      | [], _ => Lt
      | _, [] => Gt
      end
  .

  Lemma compare_list_sym
        X l0
        (compare: X -> X -> comparison)
        (IHLIST: Forall (fun x => forall y, compare y x = CompOpp (compare x y)) l0)
        l1
    :
      <<SYM: compare_list compare l1 l0 = CompOpp (compare_list compare l0 l1)>>
  .
  Proof.
    red.
    generalize dependent l1.
    revert IHLIST.
    induction l0; ii; ss; des_ifs_safe.
    - des_ifs.
    - ss. inv IHLIST.
      erewrite H1. clear H1.
      abstr (compare a x) QQ0.  clear_tac.
      erewrite IHl0; ss. clear IHl0.
      abstr (compare_list compare l0 l2) QQ1. clear_tac.
      des_ifs.
  Qed.

  Lemma compare_list_sym'
        X l0 l1
        (compare: X -> X -> comparison)
        (IHLIST: forall x y, compare y x = CompOpp (compare x y))
    :
      <<SYM: compare_list compare l1 l0 = CompOpp (compare_list compare l0 l1)>>
  .
  Proof.
    apply compare_list_sym.
    induction l0; econs; eauto.
  Qed.

  Lemma compare_list_trans
        X l0
        (compare: X -> X -> comparison)
        (IHLIST:
           Forall
             (fun x => forall z y c,
                  comparison_trans (compare x y) (compare y z) = Some c -> compare x z = c) l0)
    :
  <<TRANS: forall l2 l1 c,
        comparison_trans (compare_list compare l0 l1) (compare_list compare l1 l2) = Some c ->
        compare_list compare l0 l2 = c>>
  .
  Proof.
    {
      ginduction l0; ii; ss.
      { des_ifs; ss; clarify; [].
        des_ifs. }
      { inv IHLIST.
        destruct l1, l2; ss; clarify.
        { des_ifs; ss; clarify. }
        rename H2 into IHONE.
        rename H3 into IHLIST.
        rename x into y.
        rename a into x.
        rename x0 into z.
        specialize (IHONE z y).
        apply comparison_trans_spec in H; des; ss.
        - destruct (compare x y) eqn:CMP0;
            destruct (compare y z) eqn:CMP1;
            try (expl IHONE (ss; eauto)); try rewrite IHONE0; ss; [].
          destruct (compare_list compare l0 l1) eqn:CMPL0;
            destruct (compare_list compare l1 l2) eqn:CMPL1;
            try (by (erewrite IHl0; ss; eauto));
            try (erewrite IHl0; ss; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto).
        - destruct (compare x y) eqn:CMP0;
            destruct (compare y z) eqn:CMP1;
            try (expl IHONE (ss; eauto)); try rewrite IHONE0; ss; [].
          destruct (compare_list compare l0 l1) eqn:CMPL0;
            destruct (compare_list compare l1 l2) eqn:CMPL1;
            try (by (erewrite IHl0; ss; eauto));
            try (erewrite IHl0; ss; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto).
        - destruct (compare x y) eqn:CMP0;
            destruct (compare y z) eqn:CMP1; clarify;
              try (expl IHONE (ss; eauto)); try rewrite IHONE0; ss; [].
          destruct (compare_list compare l0 l1) eqn:CMPL0;
            destruct (compare_list compare l1 l2) eqn:CMPL1;
            try (by (erewrite IHl0; ss; eauto));
            try (erewrite IHl0; ss; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto).
      }
    }
    Unshelve.
    all: ss.
  Qed.

  Lemma compare_list_leibniz
        X
        (compare: X -> X -> comparison)
        (CMP_LEIBNIZ: forall a b, compare a b = Eq -> a = b)
        l1 l2
        (CMPL_EQ: compare_list compare l1 l2 = Eq)
    : l1 = l2.
  Proof.
    generalize dependent l2.
    induction l1.
    - intros. simpl in *. des_ifs.
    - intros. simpl in *. des_ifs.
      exploit CMP_LEIBNIZ; eauto. i. subst.
      exploit IHl1; eauto. i. subst.
      eauto.
  Qed.
  
  Lemma compare_list_leibniz'
        X l1 l2
        (compare: X -> X -> comparison)
        (CMP_LEIBNIZ: Forall (fun a => forall b,  compare a b = Eq -> a = b) l1)
        (CMPL_EQ: compare_list compare l1 l2 = Eq)
    : l1 = l2.
  Proof.
    generalize dependent l2.
    induction l1.
    - intros. simpl in *. des_ifs.
    - intros. simpl in *. des_ifs.
      inversion CMP_LEIBNIZ. subst.
      match goal with
      | [H: forall b, compare a b = Eq -> a = b |- _] =>
        exploit H; eauto; i; subst
      end.
      exploit IHl1; eauto. i. subst.
      eauto.
  Qed.

  Lemma compare_list_trans'
        X compare
        (COMP_LEIBNIZ: forall x y, compare x y = Eq -> x = y)
        (COMP_REFL: forall x, compare x x = Eq)
        (COMP_TRANS: forall c (x y z:X), compare x y = c -> compare y z = c -> compare x z = c)
    : forall c l1 l2 l3, compare_list compare l1 l2 = c ->
                    compare_list compare l2 l3 = c ->
                    compare_list compare l1 l3 = c.
  Proof.
    intros c' l1. revert c'.
    induction l1.
    { simpl. intros. des_ifs. }
    simpl. intros.
    des_ifs; simpl in *; des_ifs;
      try by (solve_leibniz_ compare COMP_LEIBNIZ;
              apply_trans_ (compare_list compare) (fun c (x y z:list X) => @IHl1 c y z);
              apply_trans_ compare COMP_TRANS;
              finish_refl_ compare COMP_REFL; congruence).
  Qed.



  Lemma compare_list_trans''
        X
        (compare: X -> X -> comparison)
        (COMP_LEIBNIZ: forall x y, compare x y = Eq -> x = y)
        (COMP_REFL: forall x, compare x x = Eq)
        c l0 l1 l2
        (IHLIST:
           Forall
             (fun x => forall c y z,
                  compare x y = c -> compare y z = c -> compare x z = c) l0)
    :
      <<TRANS:
        compare_list compare l0 l1 = c -> compare_list compare l1 l2 = c ->
        compare_list compare l0 l2 = c>>
  .
  Proof.
    revert c l1 l2.
    induction l0; ii.
    { simpl in *. des_ifs. }
    destruct l1, l2; simpl in *; try congruence.
    inv IHLIST.
    des_ifs;
      try by (solve_leibniz_ compare COMP_LEIBNIZ;
              apply_trans_ (compare_list compare) (fun c (x y z:list X) => @IHl0 H4 c y z);
              apply_trans_ compare (fun c (x y z:X) => H3 c y z);
              finish_refl_ compare COMP_REFL; try congruence).
  Qed.

  Lemma compare_list_refl
        X compare
        (COMP_REFL: forall (x:X), compare x x = Eq)
    : forall l, compare_list compare l l = Eq.
  Proof.
    intros l. induction l.
    - eauto.
    - simpl. rewrite COMP_REFL.
      rewrite IHl. eauto.
  Qed.
End LISTS.


(* TODO: move to TODO.v? *)
(* Fixpoint map2 A B C (f: A -> B -> C) (a0: list A) (b0: list B) := *)
(*   match a0, b0 with *)
(*   | a :: a1, b :: b1 => (f a b) :: (map2 f a1 b1) *)
(*   | _, _ => [] *)
(*   end *)
(* . *)

(* Anyhow, besides mutual-fixpoint problem, we cannot use map2 for lexico_order *)
(* lexico_order (map2 [] [1]) will give Eq *)
(* This should hold: map2 [] [1] <> map2 [1] [] <> map2 [] []. *)
(* So simple option type will not rescue here *)










Module Type AltUsual.

  Parameter t: Type.
  Parameter compare: t -> t -> comparison.
  Parameter compare_sym: forall
            x y
    ,
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  
  Parameter compare_trans: forall
        (* x y z c (* c should come at the end, to make "specialize" easy *) *)
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .

  Parameter compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .

  (* Parameter eq_dec : forall *)
  (*     (x y:t) *)
  (*   , *)
  (*     {x = y} + {x <> y}. *)

End AltUsual.





Module AltFacts (E: OrdersAlt.OrderedTypeAlt).

  (* Include E. *)
  (* TODO: This prohibits including "EOrigFacts" later. Is there smarter way to do this? *)

  Module EOrig := OrdersAlt.OT_from_Alt E.
  (* Module EOrigFull <: OrderedTypeFull := (OT_to_Full EOrig). *)
  Module EOrigFacts := OrdersFacts.OrderedTypeFacts EOrig.
  (* Import EOrigFacts.OrderTac. *)

  Include EOrigFacts.

  Lemma compare_eq_any_trans
        c x y z
        (XY: E.compare x y = Eq)
        (YZ: E.compare y z = c)
    :
      <<XZ: E.compare x z = c>>
  .
  Proof.
    red.
    destruct c; try EOrigFacts.order.
    - erewrite EOrigFacts.eq_trans; eauto.
    - erewrite EOrigFacts.OrderTac.eq_lt; eauto.
    - repeat rewrite EOrigFacts.compare_gt_iff in *.
      erewrite EOrigFacts.OrderTac.lt_eq; eauto.
      apply EOrigFacts.eq_sym; ss.
  Qed.

  Lemma compare_any_eq_trans
        c x y z
        (XY: E.compare x y = c)
        (YZ: E.compare y z = Eq)
    :
      <<XZ: E.compare x z = c>>
  .
  Proof.
    red.
    destruct c; try EOrigFacts.order.
    - erewrite EOrigFacts.eq_trans; eauto.
    - erewrite EOrigFacts.OrderTac.lt_eq; eauto.
    - repeat rewrite EOrigFacts.compare_gt_iff in *.
      erewrite EOrigFacts.OrderTac.eq_lt; eauto.
      apply EOrigFacts.eq_sym; ss.
  Qed.

End AltFacts.

Module Alt_from_AltUsual (E: AltUsual) <: OrdersAlt.OrderedTypeAlt := E.

Module OT_from_AltUsual (E:AltUsual) <: Orders.OrderedType.
  Module EAlt := Alt_from_AltUsual E.
  Include OrdersAlt.OT_from_Alt EAlt.

  Lemma eq_leibniz : forall x y, eq x y <-> x = y.
  Proof.
    i. split.
    - apply E.compare_leibniz.
    - i. hexploit (E.compare_sym x y). red. i.
      subst. destruct (E.compare y y); ss.
  Qed.

  Lemma eq_dec_l : forall x y:t, {x = y} + {x <> y}.
  Proof.
    i. destruct (eq_dec x y).
    - left. apply eq_leibniz. ss.
    - right. ii. apply n. apply eq_leibniz. ss.
  Qed.
End OT_from_AltUsual.


(* Module Alt_from_AltUsual (E: AltUsual) <: OrdersAlt.OrderedTypeAlt := E. *)


Module AltUsualFacts (E: AltUsual). (* <: (AltFacts E). *)
(* TODO: How to check subtype of these? forall E, AltUsualFacts E >= AltFacts E*)

  (* Module EAlt <: OrdersAlt.OrderedTypeAlt := Alt_from_AltUsual E. *)
  (* Module EAltFacts := (AltFacts E). *)
  (* Include EAlt. *)
  (* Include EAltFacts. *)
  Include E.
  Include AltFacts E.

  Lemma eq_repl_l
        x y
        (EQ: compare x y = Eq)
        z
    :
      compare x z = compare y z
  .
  Proof. destruct (compare y z) eqn:T; eapply compare_eq_any_trans; eauto. Qed.

  Lemma eq_repl_r
        x y
        (EQ: compare y x = Eq)
        z
    :
      compare z x = compare z y
  .
  Proof.
    (* apply EAltFacts.eq_sym in EQ. *)
    destruct (compare z y) eqn:T; eapply compare_any_eq_trans; eauto.
  Qed.

  Lemma weird_lemma
        x y z
        (EQ: compare y x = compare z y)
    :
      compare z x = compare z y
  .
  Proof.
    destruct (compare z y) eqn:T; eapply compare_trans; eauto.
  Qed.

  Lemma eq_dec_l
        (x y : t)
    : {x = y} + {x <> y}.
  Proof.
    destruct (eq_dec x y).
    - eauto using compare_leibniz.
    - right. ii. subst.
      eauto using (compare_refl y).
  Qed.

End AltUsualFacts.










(* I write "Orders.OrderedType" in order to not confuse with "OrderedType.OrderedType" *)
(* This is weird... I think it is impossible to define OrderedType X => OrderedType (option X) *)
(* because OrderedType's lt's irrefl is defined with leibniz eq, not eq of that module *)
Module option_orig (E: Orders.OrderedType) <: Orders.OrderedType.

  Module EAlt <: OrdersAlt.OrderedTypeAlt := OrdersAlt.OT_to_Alt E.
  Import EAlt. (* To get compare_trans *)

  Module EFull <: OrderedTypeFull := (OT_to_Full E).
  (* Module EFullTotal <: TotalOrder := OTF_to_TotalOrder EFull. *)
  (* Module ETac := OrdersTac.MakeOrderTac EFull EFullTotal. *)
  Module EFacts := OrdersFacts.OrderedTypeFacts EFull.
  (* OrdersFacts.OrderedTypeFullFacts <--------- What is this for? *)
  Import EFacts.
  (* ETac is included in EFacts *)

  Definition t := option E.t.

  Definition eq (x y: t) :=
    match x, y with
    | Some x_, Some y_ => E.eq x_ y_
    | None, None => True
    | _, _ => False
    end.

  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
    destruct x, y; ss.
    - apply E.eq_dec.
    - right; ii; ss.
    - right; ii; ss.
    - left; ss.
  Defined.

  Global Program Instance eq_equiv : Equivalence eq.
  Next Obligation.
    ii. destruct x; ss. apply eq_refl; ss.
  Qed.
  Next Obligation.
    ii. destruct x; ss.
    des_ifs. ss. apply eq_sym; ss.
  Qed.
  Next Obligation.
    ii. destruct x; ss; des_ifs; ss.
    eapply eq_trans; eauto.
  Qed.



  Definition compare (x y: t): comparison :=
    match x, y with
    | Some x_, Some y_ => E.compare x_ y_
    | None, Some _ => Lt
    | Some _, None => Gt
    | None, None => Eq
    end.

  Definition lt (x y: t): Prop := compare x y = Lt.

  Lemma compare_spec (x y: t):
    CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii. destruct x, y; ss; try (by econs).

    hexploit E.compare_spec; eauto; []; intro SPEC; des.
    destruct (E.compare t0 t1) eqn:T0;
      rewrite T0 in *; inv SPEC; econs; ss.
    - 
    compute. eapply compare_lt_iff; ss.
  Qed.
  

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *. destruct x; ss.
    apply compare_lt_iff in H. order.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii.
    unfold eq in *. des_ifs.
    unfold lt in *. ss. repeat rewrite compare_lt_iff in *.
    split; ii; clarify; order.
  Qed.
  Next Obligation.
    intros x y z LTXY LTYZ. unfold lt in *.
    destruct x, y, z; ss.
    SearchAbout (EAlt.compare).
    SearchAbout (E.compare). (* Can't we search at once?? *)
    eapply EAlt.compare_trans; eauto.
  Qed.


End option_orig.



Module option (E: AltUsual) <: AltUsual.

  Definition t := option E.t.

  Definition compare (x y: t): comparison :=
    match x, y with
    | Some x_, Some y_ => E.compare x_ y_
    | None, Some _ => Lt
    | Some _, None => Gt
    | None, None => Eq
    end.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof. destruct x, y; ss. apply E.compare_sym. Qed.

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    destruct x, y, z, c; ss; apply E.compare_trans; ss.
  Qed.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof.
    destruct x, y; ss. intro. f_equal. apply E.compare_leibniz; ss.
  Qed.

End option.

Module optionFacts (E: AltUsual) := AltUsualFacts E.



(* Module prod_ord (E1 E2: Orders.OrderedType). *)
(*   Definition t : Type := E1.t * E2.t. *)
(*   Definition eq v1 v2 := *)
(*     E1.eq (fst v1) (fst v2) /\ E2.eq (snd v1) (snd v2). *)

(*   Lemma eq_equiv : Equivalence eq. *)
(*   Proof. *)
(*     unfold eq. *)
(*     split; ii. *)
(*     - split; try apply Equivalence_Reflexive. *)
(*     - des. split; apply Equivalence_Symmetric; eauto. *)
(*     - des. split; eapply Equivalence_Transitive; eauto. *)
(*   Qed. *)

(*   Definition lt (x y:t) : Prop := *)
(*     E1.lt (fst x) (fst y) \/ *)
(*     (E1.eq (fst x) (fst y) /\ E2.lt (snd x) (snd y)). *)

(*   Lemma lt_strorder : StrictOrder lt. *)
(*   Proof. *)
(*     unfold lt. constructor. *)
(*     - ii. des. *)
(*       + eapply (@StrictOrder_Irreflexive _ _ E1.lt_strorder); eauto. *)
(*       + eapply (@StrictOrder_Irreflexive _ _ E2.lt_strorder); eauto. *)
(*     - ii. des. *)
(*       + left. eapply (@StrictOrder_Transitive _ _ E1.lt_strorder); eauto. *)
(*       + left.  *)
(*         apply StrictOrder_Irreflexive. *)

(*     Orders.OrderedType *)

Module floating_point <: AltUsual.

  Definition t := floating_point.

  Definition case_ord(x: t): OrdIdx.t :=
    match x with
    | fp_float => 0
    | fp_double => 1
    | fp_fp128 => 2
    | fp_x86_fp80 => 3
    | fp_ppc_fp128 => 4
    end
  .

  Definition compare (x y: t): comparison := OrdIdx.compare (case_ord x) (case_ord y).

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof. destruct x, y; ss. Qed.
  
  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    destruct x, y, z, c; ss.
  Qed.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof.
    destruct x, y; ss.
  Qed.

End floating_point.

Module floating_pointFacts := AltUsualFacts floating_point.



(* Module floating_pointFacts := OrdersFacts.OrderedTypeFacts floating_point. *)
(* TODO: Can I define it inside original module? *)
(* just make a wrapper for UsualOrderedType? *)

Module UOT_to_AltU (E: Orders.UsualOrderedType) <: AltUsual.
  Import E.
  Module EAlt := OrdersAlt.OT_to_Alt E.
  Include EAlt.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof.
    ii.
    apply EAlt.compare_Eq. ss.
  Qed.

End UOT_to_AltU.


Module NatAltUsual := UOT_to_AltU Nat.
Module NatAltUsualFacts := AltUsualFacts NatAltUsual.

Ltac to_nat_alt_compare :=
  repeat match goal with
         | [ H: context[OrdIdx.compare ?a ?b] |- _ ] =>
           replace (OrdIdx.compare a b) with (NatAltUsual.compare a b) in H by ss
         | [ |- context[OrdIdx.compare ?a ?b] ] =>
           replace (OrdIdx.compare a b) with (NatAltUsual.compare a b) by ss
         end.
(* I Really want to remove this tactic ... *)

Module sz <: AltUsual.
  Definition t := sz.

  Definition compare (x y:t) : comparison := OrdIdx.compare x y.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof. apply Nat.compare_antisym. Qed.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof. apply Nat.compare_eq. Qed.

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    intros.
    destruct c.
    - apply nat_compare_eq in XY.
      apply nat_compare_eq in YZ.
      subst. apply Nat.compare_refl.
    - rewrite <- nat_compare_lt in *.
      red. rewrite <- nat_compare_lt. omega.
    - rewrite <- nat_compare_gt in *.
      red. rewrite <- nat_compare_gt. omega.
  Qed.      
End sz.

Module szFacts := AltUsualFacts sz.


Module varg <: AltUsual := option sz.

Module vargFacts := optionFacts varg. (* or AltUsualFacts varg directly? *)

(* TODO: remove this *)
Module AtomCompare.
  Definition t := MetatheoryAtom.AtomImpl.atom.
  Definition compare := MetatheoryAtom.AtomImpl.atom_compare.

  (* Lemma atom_lt_irrefl x: *)
  (*   ~ MetatheoryAtom.AtomImpl.atom_lt x x. *)
  (* Proof. *)
  (*   apply StrictOrder_Irreflexive. *)
  (* Qed. *)

  (* Lemma atom_lt_trans x y z: *)
  (*   MetatheoryAtom.AtomImpl.atom_lt x y -> *)
  (*   MetatheoryAtom.AtomImpl.atom_lt y z -> *)
  (*   MetatheoryAtom.AtomImpl.atom_lt x z. *)
  (* Proof. apply StrictOrder_Transitive. Qed. *)

  Lemma compare_eq x y
    : compare x y = Eq <-> x = y.
  Proof.
    unfold compare.
    generalize (MetatheoryAtom.AtomImpl.atom_compare_spec x y).
    intros SPEC.
    split; intro EQ.
    - rewrite EQ in SPEC. inversion SPEC. auto.
    - destruct (MetatheoryAtom.AtomImpl.atom_compare x y) eqn:ACMP; auto;
        inversion SPEC; subst;
          apply StrictOrder_Irreflexive in H; contradiction.
  Qed.

  Lemma compare_refl x
    : compare x x = Eq.
  Proof. apply (compare_eq x x). eauto. Qed.

  Lemma atom_lt_LT x y
    : MetatheoryAtom.AtomImpl.atom_lt x y <-> compare x y = Lt.
  Proof.
  Admitted.

  Lemma atom_lt_GT x y
    : MetatheoryAtom.AtomImpl.atom_lt x y <-> compare y x = Gt.
  Proof.
  Admitted.

  Lemma compare_lt x y
    : compare x y = Lt <-> compare y x = Gt.
  Proof.
    rewrite <- atom_lt_LT. rewrite <- atom_lt_GT. eauto.
  Qed.

  Lemma compare_lt_trans x y z
    : compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
  Proof.
    intros CXY CYZ.
    rewrite <- atom_lt_LT in *.
    eapply StrictOrder_Transitive; eauto.
    (* eapply atom_lt_trans; eauto. *)
  Qed.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof.
    red.
    destruct (compare y x) eqn:CYX.
    - rewrite compare_eq in CYX. subst.
      rewrite compare_refl. reflexivity.
    - apply compare_lt in CYX. rewrite CYX. reflexivity.
    - apply compare_lt in CYX. rewrite CYX. reflexivity.
  Qed.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof. apply compare_eq. Qed.

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    red. intros. destruct c.
    - rewrite compare_eq in *. congruence.
    - eapply compare_lt_trans; eauto.
    - rewrite <- compare_lt in *.
      eapply compare_lt_trans; eauto.
  Qed.
End AtomCompare.


Module Float <: AltUsual.

  (* Floats.float *)
  Definition t := Float.
  (* Integers.Int.int *)
  (* Floats.Float.to_bits *)
  (* Floats.Float *)
  (* Floats.Float.cmp *)

  Definition compare (x y: t): comparison := wrap_compare (FLOAT.compare) x y.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof. apply FLOAT.compare_leibniz; eauto. Qed.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof. apply FLOAT.compare_sym; eauto. Qed.

  Lemma compare_trans: forall
      c x y z
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof. apply FLOAT.compare_trans; eauto. Qed.
 
End Float.
Module FloatFacts := AltUsualFacts Float.

Module Int <: AltUsual.

  (* Floats.float *)
  Definition t := Int.
  (* Integers.Int.int *)
  (* Floats.Float.to_bits *)
  (* Floats.Float *)
  (* Floats.Float.cmp *)

  Definition compare (x y: t): comparison := Z.compare x y.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof. exact Z.compare_eq. Qed.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof. rewrite Zcompare_antisym. reflexivity. Qed.

  Lemma compare_trans: forall
      c x y z
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    destruct c; intros.
    - apply Z.compare_eq in XY.
      apply Z.compare_eq in YZ.
      subst. apply Z.compare_refl.
    - eapply Zcompare_Lt_trans; eauto.
    - eapply Zcompare_Gt_trans; eauto.
  Qed.
 
End Int.
Module IntFacts := AltUsualFacts Int.


Module id <: AltUsual.
  Definition t := id.

  Definition compare : t -> t -> comparison :=
    MetatheoryAtom.AtomImpl.atom_compare.

  Lemma strictorder_not_reflexive
        A R (SO:StrictOrder R)
    : <<NOT_REFL: forall x:A, ~ R x x>>.
  Proof.
    ii. destruct SO.
    unfold Irreflexive, Reflexive, complement in *; eauto.
  Qed.

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof.
    hexploit strictorder_not_reflexive.
    { apply MetatheoryAtom.AtomImpl.atom_lt_strorder. }
    intro NREFL.

    hexploit (@StrictOrder_Asymmetric).
    { apply MetatheoryAtom.AtomImpl.atom_lt_strorder. }
    intro ASYM.

    unfold compare.
    destruct (MetatheoryAtom.AtomImpl.atom_compare_spec x y);
      destruct (MetatheoryAtom.AtomImpl.atom_compare_spec y x); eauto;
        subst;
        try (by exploit NREFL; eauto; i; contradiction);
        try (by exploit ASYM; eauto; i; contradiction).
  Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. eapply AtomCompare.compare_trans; eauto. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. apply AtomCompare.compare_leibniz; auto. Qed.
End id.

Module idFacts := AltUsualFacts id.


Module truncop <: AltUsual.
  Definition t := truncop.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | truncop_int => 0
    | truncop_fp => 1
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End truncop.
Module truncopFacts := AltUsualFacts truncop.


Module castop <: AltUsual.
  Definition t := castop.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | castop_fptoui => 0
    | castop_fptosi => 1
    | castop_uitofp => 2
    | castop_sitofp => 3
    | castop_ptrtoint => 4
    | castop_inttoptr => 5
    | castop_bitcast => 6
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End castop.
Module castopFacts := AltUsualFacts castop.


Module extop <: AltUsual.
  Definition t := extop.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | extop_z => 0
    | extop_s => 1
    | extop_fp => 2
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End extop.
Module extopFacts := AltUsualFacts extop.


Module bool <: AltUsual.
  Definition t := bool.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | true => 0
    | false => 1
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End bool.
Module boolFacts := AltUsualFacts bool.


Module cond <: AltUsual.
  Definition t := cond.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | cond_eq => 0
    | cond_ne => 1
    | cond_ugt => 2
    | cond_uge => 3
    | cond_ult => 4
    | cond_ule => 5
    | cond_sgt => 6
    | cond_sge => 7
    | cond_slt => 8
    | cond_sle => 9
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End cond.
Module condFacts := AltUsualFacts cond.


Module fcond <: AltUsual.
  Definition t := fcond.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | fcond_false => 0
    | fcond_oeq => 1
    | fcond_ogt => 2
    | fcond_oge => 3
    | fcond_olt => 4
    | fcond_ole => 5
    | fcond_one => 6
    | fcond_ord => 7
    | fcond_ueq => 8
    | fcond_ugt => 9
    | fcond_uge => 10
    | fcond_ult => 11
    | fcond_ule => 12
    | fcond_une => 13
    | fcond_uno => 14
    | fcond_true => 15
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y; ss; destruct z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End fcond.
Module fcondFacts := AltUsualFacts fcond.


Module bop <: AltUsual.
  Definition t := bop.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | bop_add => 0
    | bop_sub => 1
    | bop_mul => 2
    | bop_udiv => 3
    | bop_sdiv => 4
    | bop_urem => 5
    | bop_srem => 6
    | bop_shl => 7
    | bop_lshr => 8
    | bop_ashr => 9
    | bop_and => 10
    | bop_or => 11
    | bop_xor => 12
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y; ss; destruct z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End bop.
Module bopFacts := AltUsualFacts bop.


Module fbop <: AltUsual.
  Definition t := fbop.

  Definition case_order (x:t): OrdIdx.t :=
    match x with
    | fbop_fadd => 0
    | fbop_fsub => 1
    | fbop_fmul => 2
    | fbop_fdiv => 3
    | fbop_frem => 4
    end.

  Definition compare (x y:t) :=
    OrdIdx.compare (case_order x) (case_order y).

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof. destruct c, x, y, z; ss. Qed.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof. destruct x, y; ss. Qed.
End fbop.
Module fbopFacts := AltUsualFacts fbop.

(* tactics *)
Ltac solve_leibniz_base :=
  solve_leibniz_ sz.compare sz.compare_leibniz;
  solve_leibniz_ Int.compare Int.compare_leibniz;
  solve_leibniz_ varg.compare varg.compare_leibniz;
  (* solve_leibniz_ typ.compare typ.compare_leibniz; *)
  solve_leibniz_ Float.compare Float.compare_leibniz;
  solve_leibniz_ sz.compare sz.compare_leibniz;
  solve_leibniz_ floating_point.compare floating_point.compare_leibniz;

  solve_leibniz_ id.compare id.compare_leibniz;
  solve_leibniz_ truncop.compare truncop.compare_leibniz;
  solve_leibniz_ extop.compare extop.compare_leibniz;
  solve_leibniz_ castop.compare castop.compare_leibniz;
  solve_leibniz_ cond.compare cond.compare_leibniz;
  solve_leibniz_ fcond.compare fcond.compare_leibniz;
  solve_leibniz_ bool.compare bool.compare_leibniz;
  solve_leibniz_ bop.compare bop.compare_leibniz;
  solve_leibniz_ fbop.compare fbop.compare_leibniz
.

Ltac finish_refl_base :=
  finish_refl_ floating_point.compare floating_pointFacts.EOrigFacts.compare_refl;
  finish_refl_ sz.compare szFacts.EOrigFacts.compare_refl;
  finish_refl_ varg.compare vargFacts.EOrigFacts.compare_refl;
  (* finish_refl_ typ.compare typ.compare_refl; *)
  finish_refl_ Float.compare FloatFacts.EOrigFacts.compare_refl;
  finish_refl_ Int.compare IntFacts.EOrigFacts.compare_refl;
  finish_refl_ id.compare idFacts.EOrigFacts.compare_refl;

  finish_refl_ truncop.compare truncopFacts.EOrigFacts.compare_refl;
  finish_refl_ castop.compare castopFacts.EOrigFacts.compare_refl;
  finish_refl_ extop.compare extopFacts.EOrigFacts.compare_refl;
  finish_refl_ bool.compare boolFacts.EOrigFacts.compare_refl;
  finish_refl_ cond.compare condFacts.EOrigFacts.compare_refl;
  finish_refl_ fcond.compare fcondFacts.EOrigFacts.compare_refl;
  finish_refl_ bop.compare bopFacts.EOrigFacts.compare_refl;
  finish_refl_ fbop.compare fbopFacts.EOrigFacts.compare_refl
  (* finish_refl_ compare compare_refl; *)
.

Ltac apply_trans_base :=
  apply_trans_ floating_point.compare @floating_point.compare_trans;
  apply_trans_ sz.compare @sz.compare_trans;
  apply_trans_ varg.compare @varg.compare_trans;
  (* apply_trans_ typ.compare @typ.compare_trans; *)
  apply_trans_ Float.compare @Float.compare_trans;
  apply_trans_ Int.compare @Int.compare_trans;
  apply_trans_ id.compare @id.compare_trans;

  apply_trans_ truncop.compare @truncop.compare_trans;
  apply_trans_ castop.compare @castop.compare_trans;
  apply_trans_ extop.compare @extop.compare_trans;
  apply_trans_ bool.compare @bool.compare_trans;
  apply_trans_ cond.compare @cond.compare_trans;
  apply_trans_ fcond.compare @fcond.compare_trans;
  apply_trans_ bop.compare @bop.compare_trans;
  apply_trans_ fbop.compare @fbop.compare_trans
.

(* helpers *)
Ltac solve_leibniz_IH cmp :=
  repeat match goal with
         | [IH: forall y, cmp ?a y = Eq -> ?a = y,
              H: cmp ?a ?b = Eq |- _ ] => apply IH in H
         end; subst.

Ltac solve_leibniz_list cmp :=
  repeat match goal with
         | [H: compare_list cmp ?l1 ?l2 = Eq |- _] =>
           apply compare_list_leibniz' in H; eauto
         end; subst.

Ltac finish_refl_list t typ compare compare_refl :=
  try
    (unfold t in *;
     match goal with
     | [H: compare_list compare ?a ?a = Lt |- _] =>
       rewrite (@compare_list_refl typ compare compare_refl) in H; congruence

     | [H: compare_list compare ?a ?a = Gt |- _] =>
       rewrite (@compare_list_refl typ compare compare_refl) in H; congruence
     end);
  try by apply (@compare_list_refl typ compare compare_refl).

Ltac comp_sym_list :=
  match goal with
  | [ |- context[match @compare_list ?t ?comp ?a ?b with _ => _ end]] =>
    rewrite (@compare_list_sym t b); destruct (compare_list comp b a)
  end; ss.

(**)
Module typ <: AltUsual.

  Definition t := typ.

  Definition case_order (x: t): OrdIdx.t :=
    match x with
    | typ_int _ => 0
    | typ_floatpoint _ => 1
    | typ_void => 2
    | typ_label => 3
    | typ_metadata => 4
    | typ_array _ _ => 5
    | typ_function _ _ _ => 6
    | typ_struct _ => 7
    | typ_pointer _ => 8
    | typ_namedt _ => 9
    end
  .

  Fixpoint compare' (x y: t): comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => sz.compare sz0 sz1
    | typ_floatpoint fp0, typ_floatpoint fp1 => (floating_point.compare fp0 fp1)
    | typ_void, typ_void => Eq
    | typ_label, typ_label => Eq
    | typ_metadata, typ_metadata => Eq
    | typ_array sz0 ty0, typ_array sz1 ty1 =>
      lexico_order [fun _ => sz.compare sz0 sz1; fun _ => compare' ty0 ty1]
    | typ_function ty0 tys0 arg0, typ_function ty1 tys1 arg1 =>
      lexico_order
        [fun _ => (compare' ty0 ty1) ; fun _ => (compare_list compare' tys0 tys1) ; fun _ => (varg.compare arg0 arg1)]
    | typ_struct tys0, typ_struct tys1 =>
      compare_list compare' tys0 tys1
    | typ_pointer ty0, typ_pointer ty1 =>
      compare' ty0 ty1
    (* | typ_namedt id0, typ_namedt id1 => MetatheoryAtom.AtomImpl.atom_compare id0 id1 *)
    | typ_namedt id0, typ_namedt id1 => id.compare id0 id1

    | _, _ => OrdIdx.compare (case_order x) (case_order y)
    end
  .

  Definition compare := wrap_compare compare'.

  Hint Unfold NatAltUsual.compare.


  Lemma compare_sym x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof.
    red. unfold compare, wrap_compare in *. revert y.
    induction x using typ_ind_gen;
      intros; destruct y; eauto; simpl.
    - by apply sz.compare_sym.
    - by apply floating_point.compare_sym.
    - rewrite (IHx y); eauto.
      comp_sym sz.compare sz.compare_sym; eauto; des_ifs.
    - rewrite (IHx y); eauto.
      rewrite (compare_list_sym compare' IH).
      comp_sym varg.compare varg.compare_sym; eauto; des_ifs.
    - exploit compare_list_sym; eauto.
    - by apply AtomCompare.compare_sym.
  Qed.

  Corollary compare_refl z:
    compare z z = Eq.
  Proof.
    assert (compare z z = CompOpp (compare z z)).
    { apply compare_sym. }
    destruct (compare z z); simpl in *; congruence.
  Qed.

  Ltac solve_leibniz' :=
    solve_leibniz_base;
    solve_leibniz_IH compare';
    solve_leibniz_list compare'
  .

  Ltac finish_refl :=
    unfold t, NW in *;
    finish_refl_base;
    finish_refl_ compare' compare_refl;
    finish_refl_list t typ compare' compare_refl;
    try congruence
  .

  Lemma compare_leibniz:
    forall x y
      (EQ: compare x y = Eq),
      x = y.
  Proof.
    unfold compare, wrap_compare.
    induction x using typ_ind_gen; intros;
      destruct y; try discriminate; subst; eauto;
        simpl in *; des_ifs; solve_leibniz'; finish_refl.
  Qed.

  Ltac solve_leibniz :=
    solve_leibniz_base;
    solve_leibniz_ compare' compare_leibniz;
    solve_leibniz_ (compare_list compare')
                   (compare_list_leibniz compare compare_leibniz)
  .

  Ltac apply_trans_IH compare :=
    try match goal with
        | [IH: forall c y z, compare ?x y = c -> compare y z = c -> compare ?x z = c,
             H1: compare ?x ?y = ?c, H2: compare ?y ?z = ?c |- _] =>
          unfold t in IH;
          exploit (@IH c y z); eauto; (idtac; []; i)
        end.

  Ltac apply_trans :=
    unfold NW in *;
    apply_trans_base;
    apply_trans_IH compare';
    apply_trans_ (compare_list compare')
                 (@compare_list_trans'' typ compare' compare_leibniz compare_refl)
  .

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    unfold compare, wrap_compare in *.
    intros c x. revert c.
    induction x using typ_ind_gen; intros;
      destruct c;
      destruct y; try discriminate; eauto;
        destruct z; try discriminate; eauto;
          simpl in *; des_ifs; solve_leibniz; apply_trans; finish_refl.
  Qed.
End typ.

Module typFacts := AltUsualFacts typ.


Module const <: AltUsual.

  Definition t := const.

  Definition case_order (x: t): OrdIdx.t :=
    match x with
    | const_zeroinitializer _ => 0
    | const_int _ _ => 1
    | const_floatpoint _ _ => 2
    | const_undef _ => 3
    | const_null _ => 4
    | const_arr _ _ => 5
    | const_struct _ _ => 6
    | const_gid _ _ => 7
    | const_truncop _ _ _ => 8
    | const_extop _ _ _ => 9
    | const_castop _ _ _ => 10
    | const_gep _ _ _ => 11
    | const_select _ _ _ => 12
    | const_icmp _ _ _ => 13
    | const_fcmp _ _ _ => 14
    | const_extractvalue _ _ => 15
    | const_insertvalue _ _ _ => 16
    | const_bop _ _ _ => 17
    | const_fbop _ _ _ => 18
    end.

  Fixpoint compare' (x y: t): comparison :=
    match x, y with
    | const_zeroinitializer ty0, const_zeroinitializer ty1 => typ.compare ty0 ty1
    | const_int sz0 i0, const_int sz1 i1 =>
      lexico_order [fun _ => sz.compare sz0 sz1 ; fun _ => Int.compare i0 i1]
    | const_floatpoint fp0 f0, const_floatpoint fp1 f1 =>
      lexico_order [fun _ => floating_point.compare fp0 fp1 ; fun _ => Float.compare f0 f1]
    | const_undef ty0, const_undef ty1 => typ.compare ty0 ty1
    | const_null ty0, const_null ty1 => typ.compare ty0 ty1
    | const_arr ty0 cs0, const_arr ty1 cs1 =>
      lexico_order [fun _ => typ.compare ty0 ty1 ; fun _ => compare_list compare' cs0 cs1]
    | const_struct ty0 cs0, const_struct ty1 cs1 =>
      lexico_order [fun _ => typ.compare ty0 ty1 ; fun _ => compare_list compare' cs0 cs1]
    | const_gid ty0 i0, const_gid ty1 i1 =>
      lexico_order [fun _ => typ.compare ty0 ty1 ; fun _ => id.compare i0 i1]
    | const_truncop trop0 c0 ty0, const_truncop trop1 c1 ty1 =>
      lexico_order [fun _ => truncop.compare trop0 trop1 ; fun _ => compare' c0 c1 ; fun _ => typ.compare ty0 ty1]
    | const_extop extop0 c0 ty0, const_extop extop1 c1 ty1 =>
      lexico_order [fun _ => extop.compare extop0 extop1 ; fun _ => compare' c0 c1 ; fun _ => typ.compare ty0 ty1]
    | const_castop csop0 c0 ty0, const_castop csop1 c1 ty1 =>
      lexico_order [fun _ => castop.compare csop0 csop1 ; fun _ => compare' c0 c1 ; fun _ => typ.compare ty0 ty1]
    | const_gep inb0 c0 cs0, const_gep inb1 c1 cs1 =>
      lexico_order [fun _ => bool.compare  inb0 inb1 ; fun _ => compare' c0 c1 ; fun _ => compare_list compare' cs0 cs1]
    | const_select cx0 cy0 cz0, const_select cx1 cy1 cz1 =>
      lexico_order [fun _ => compare' cx0 cx1 ; fun _ => compare' cy0 cy1 ; fun _ => compare' cz0 cz1]
    | const_icmp cx0 cy0 cz0, const_icmp cx1 cy1 cz1 =>
      lexico_order [fun _ => cond.compare cx0 cx1 ; fun _ => compare' cy0 cy1 ; fun _ => compare' cz0 cz1]
    | const_fcmp fc0 cx0 cy0, const_fcmp fc1 cx1 cy1 =>
      lexico_order [fun _ => fcond.compare fc0 fc1; fun _ => compare' cx0 cx1 ; fun _ => compare' cy0 cy1]
    | const_extractvalue c0 cs0, const_extractvalue c1 cs1 =>
      lexico_order [fun _ => compare' c0 c1 ; fun _ => compare_list compare' cs0 cs1]
    | const_insertvalue cx0 cy0 cs0, const_insertvalue cx1 cy1 cs1 =>
      lexico_order [fun _ => compare' cx0 cx1 ; fun _ => compare' cy0 cy1 ; fun _ => compare_list compare' cs0 cs1]
    | const_bop bop0 cx0 cy0, const_bop bop1 cx1 cy1 =>
      lexico_order [fun _ => bop.compare bop0 bop1; fun _ => compare' cx0 cx1 ; fun _ => compare' cy0 cy1]
    | const_fbop fbop0 cx0 cy0, const_fbop fbop1 cx1 cy1 =>
      lexico_order [fun _ => fbop.compare fbop0 fbop1; fun _ => compare' cx0 cx1 ; fun _ => compare' cy0 cy1]
    | _, _ => OrdIdx.compare (case_order x) (case_order y)
    end
  .

  Definition compare := wrap_compare compare'.

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof.
    red. unfold compare, wrap_compare in *. revert y.
    induction x using const_ind_gen;
      intros; destruct y; ss;
        try (by apply typ.compare_sym);
        repeat (try comp_sym Int.compare Int.compare_sym;
                try comp_sym Float.compare Float.compare_sym;
                try comp_sym sz.compare sz.compare_sym;
                try comp_sym floating_point.compare floating_point.compare_sym;
                try comp_sym typ.compare typ.compare_sym;
                try comp_sym compare' (fun (x:t) => IHx);
                try comp_sym compare' (fun (x:t) => IHx1);
                try comp_sym compare' (fun (x:t) => IHx2);
                try comp_sym compare' (fun (x:t) => IHx3);
                try comp_sym id.compare id.compare_sym;
                try comp_sym truncop.compare truncop.compare_sym;
                try comp_sym extop.compare extop.compare_sym;
                try comp_sym castop.compare castop.compare_sym;
                try comp_sym cond.compare cond.compare_sym;
                try comp_sym fcond.compare fcond.compare_sym;
                try comp_sym bool.compare bool.compare_sym;
                try comp_sym bop.compare bop.compare_sym;
                try comp_sym fbop.compare fbop.compare_sym;
                try comp_sym_list).
  Qed.

  Corollary compare_refl z:
    compare z z = Eq.
  Proof.
    assert (compare z z = CompOpp (compare z z)).
    { apply compare_sym. }
    destruct (compare z z); ss.
  Qed.

  Ltac solve_leibniz' :=
    solve_leibniz_base;
    solve_leibniz_ typ.compare typ.compare_leibniz;
    solve_leibniz_IH compare';
    solve_leibniz_list compare'
  .

  Ltac finish_refl :=
    unfold t, NW in *;
    finish_refl_base;
    finish_refl_ typ.compare typFacts.EOrigFacts.compare_refl;
    finish_refl_ compare' compare_refl;
    finish_refl_list t const compare' compare_refl;
    try congruence
  .

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof.
    unfold compare, wrap_compare in *. revert y EQ.
    induction x using const_ind_gen;
      intros; destruct y; ss;
        try by des_ifs; solve_leibniz'.
  Qed.

  Ltac solve_leibniz :=
    solve_leibniz_base;
    solve_leibniz_ typ.compare typ.compare_leibniz;
    solve_leibniz_ compare' compare_leibniz;
    solve_leibniz_ (compare_list compare')
                   (compare_list_leibniz compare compare_leibniz)
  .

  Ltac apply_trans_IH t compare :=
    try match goal with
        | [IH: forall c y z, compare ?x y = c -> compare y z = c -> compare ?x z = c,
             H1: compare ?x ?y = ?c, H2: compare ?y ?z = ?c |- _] =>
          unfold t in IH;
          exploit (@IH c y z); eauto; (idtac; []; i)
        end.

  Ltac apply_trans :=
    unfold NW in *;
    apply_trans_base;
    apply_trans_ typ.compare typ.compare_trans;
    apply_trans_IH t compare';
    apply_trans_ (compare_list compare')
                 (@compare_list_trans'' const compare' compare_leibniz compare_refl)
  .

  Lemma compare_trans: forall
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    , <<XZ: compare x z = c>>.
  Proof.
    unfold compare, wrap_compare in *.
    intros c x. revert c.
    Time
      induction x using const_ind_gen;
      intros; destruct c;
        destruct y; try discriminate; (* 399 *)
          destruct z; try discriminate; eauto; (* 57, 60 ~ 80 sec *)
            by (simpl in *; des_ifs; solve_leibniz; apply_trans; finish_refl). (* 440 sec *)
  Qed.

End const.

Module constFacts := AltUsualFacts const.
