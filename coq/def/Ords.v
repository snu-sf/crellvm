Require Import syntax.
Require Import alist.

Require Import infrastructure.
Require vellvm. (* In order to avoid name clash on "comparison", I didn't Import it *)

Require Import sflib.
Require Export Coqlib.
Export LLVMsyntax.
Export LLVMinfra.

Require Import Decs.
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


Fixpoint lexico_order (x0: list comparison): comparison :=
  match x0 with
  | [] => Eq
  | Eq :: x1 => lexico_order x1
  | Lt :: _ => Lt
  | Gt :: _ => Gt
  end
.

Definition compare_list X (compare: X -> X -> comparison) :=
  fix compare_list_ (a0 b0: list X): comparison :=
    match a0, b0 with
    | a :: a1, b :: b1 => lexico_order [(compare a b) ; (compare_list_ a1 b1)]
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    end
.



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





(* I write "Orders.OrderedType" in order to not confuse with "OrderedType.OrderedType" *)
(* This is weird... I think it is impossible to define OrderedType X => OrderedType (option X) *)
(* because OrderedType's lt's irrefl is defined with leibniz eq, not eq of that module *)
Module option (E: Orders.OrderedType) <: Orders.OrderedType.

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


End option.

                          












Module floating_point <: Orders.OrderedType.

  Definition t := floating_point.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.

  Definition eq_dec (x y:t): {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition nat_ord(x: t): nat :=
    match x with
    | fp_float => 0
    | fp_double => 1
    | fp_fp128 => 2
    | fp_x86_fp80 => 3
    | fp_ppc_fp128 => 4
    end
  .

  Definition ltb (x y: t): bool := Nat.ltb (nat_ord x) (nat_ord y).
  
  Definition lt: t -> t -> Prop := ltb.

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *. unfold ltb in *. destruct x; ss.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. clarify.
  Qed.
  Next Obligation.
    intros x y z LTXY LTYZ. unfold lt in *. unfold ltb in *.
    apply Nat.ltb_lt in LTXY.
    apply Nat.ltb_lt in LTYZ.
    apply Nat.ltb_lt.
    etransitivity; eauto.
  Qed.

  Definition compare (x y: t): comparison :=
    if(eq_dec x y) then Eq else
      (if (ltb x y) then Lt else Gt)
  .
  
  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii. destruct x, y; ss; try (by econs).
  Qed.

End floating_point.

Module floating_pointFacts := OrdersFacts.OrderedTypeFacts floating_point.
(* TODO: Can I define it inside original module? *)
(* just make a wrapper for UsualOrderedType? *)




Module varg <: Orders.OrderedType.

  Module option_nat := option Nat.
  Include option_nat.

End varg.

Module vargFacts := OrdersFacts.OrderedTypeFacts varg.







Module CompareTac (E: Orders.UsualOrderedType).
  (* Module EAlt <: OrdersAlt.OrderedTypeAlt := OrdersAlt.OT_to_Alt E. *)
  (* Import EAlt. (* To get compare_trans *) *)
  Module EFull <: OrderedTypeFull := (OT_to_Full E).
  Module EFacts := OrdersFacts.OrderedTypeFacts EFull.
  (* Import EFacts. *)

  Ltac compare_tac :=
    match goal with
    | [H: E.compare ?a ?b = Eq |- _ ] => rewrite EFacts.compare_eq_iff in H
    | [H: E.compare ?a ?b = Lt |- _ ] => rewrite EFacts.compare_lt_iff in H
    | [H: E.compare ?a ?b = Gt |- _ ] => rewrite EFacts.compare_gt_iff in H
    end.
  
End CompareTac.

Module NatCompare := CompareTac Nat.
(* NatCompare.compare_tac. *)
Module NatTacs := OrdersTac.MakeOrderTac Nat Nat.
Module NatFacts := OrdersFacts.OrderedTypeFacts Nat.








Module typ <: OrderedType.

  Definition t := typ.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.

  Fail Fixpoint compare_list (a0 b0: list t): comparison :=
    match a0, b0 with
    | a :: a1, b :: b1 => lexico_order [(compare a b) ; (compare_list a1 b1)]
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    end
    (* lexico_order (map2 compare x y) *)

  with compare (x y: t): comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => Nat.compare sz0 sz1
    | typ_floatpoint fp0, typ_floatpoint fp1 => (floating_point.compare fp0 fp1)
    | typ_void, typ_void => Eq
    | typ_label, typ_label => Eq
    | typ_metadata, typ_metadata => Eq
    | typ_array sz0 ty0, typ_array sz1 ty1 =>
      Eq
      (* lexico_order [Nat.compare sz0 sz1; compare ty0 ty1] *)
    | typ_function ty0 tys0 arg0, typ_function ty1 tys1 arg1 =>
      (* Not in definition's order, but "singleton first, list later" *)
      (* This is because I don't want to use "++" *)
      (* lexico_order ((varg.compare arg0 arg1) *)
      (*                 :: (compare ty0 ty1) :: (map2 compare tys0 tys1)) *)
      Eq
    | typ_struct tys0, typ_struct tys1 =>
      compare_list tys0 tys1
    | typ_pointer ty0, typ_pointer ty1 =>
      compare ty0 ty1
    | typ_namedt id0, typ_namedt id1 => Eq

    | _, _ => Eq
    end
  .

  Fixpoint compare_list (compare: t -> t -> comparison ) (a0 b0: list t): comparison :=
    match a0, b0 with
    | a :: a1, b :: b1 => lexico_order [(compare a b) ; (compare_list compare a1 b1)]
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    end
  .

  Fail Fixpoint compare (x y: t): comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => Nat.compare sz0 sz1
    | typ_floatpoint fp0, typ_floatpoint fp1 => (floating_point.compare fp0 fp1)
    | typ_void, typ_void => Eq
    | typ_label, typ_label => Eq
    | typ_metadata, typ_metadata => Eq
    | typ_array sz0 ty0, typ_array sz1 ty1 =>
      Eq
      (* lexico_order [Nat.compare sz0 sz1; compare ty0 ty1] *)
    | typ_function ty0 tys0 arg0, typ_function ty1 tys1 arg1 =>
      (* Not in definition's order, but "singleton first, list later" *)
      (* This is because I don't want to use "++" *)
      (* lexico_order ((varg.compare arg0 arg1) *)
      (*                 :: (compare ty0 ty1) :: (map2 compare tys0 tys1)) *)
      Eq
    | typ_struct tys0, typ_struct tys1 =>
      compare_list compare tys0 tys1
    | typ_pointer ty0, typ_pointer ty1 =>
      compare ty0 ty1
    | typ_namedt id0, typ_namedt id1 => Eq

    | _, _ => Eq
    end
  .
  Reset compare_list.

  (******* WHY????????? I tried exactly like Vellvm. What is the difference? *)

  Fixpoint wf_order (x: t): nat :=
    match x with
    | typ_int _ => 0%nat
    | typ_floatpoint _ => 0%nat
    | typ_void => 0%nat
    | typ_label => 0%nat
    | typ_metadata => 0%nat
    | typ_array _ ty0 => 1 + (wf_order ty0) + 1
    | typ_function ty0 tys0 _ => (1 + (wf_order ty0) + 1 + length tys0)%nat
    | typ_struct tys0 => length tys0
    | typ_pointer ty0 => 1 + (wf_order ty0) + 1
    | typ_namedt _ => 0%nat
    end
  .

  Program Fixpoint compare (x y: t) {measure (wf_order x)}: comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => Nat.compare sz0 sz1
    | typ_floatpoint fp0, typ_floatpoint fp1 => (floating_point.compare fp0 fp1)
    | typ_void, typ_void => Eq
    | typ_label, typ_label => Eq
    | typ_metadata, typ_metadata => Eq
    | typ_array sz0 ty0, typ_array sz1 ty1 =>
      Eq
    (* lexico_order [Nat.compare sz0 sz1; compare ty0 ty1] *)
    | typ_function ty0 tys0 arg0, typ_function ty1 tys1 arg1 =>
      (* Not in definition's order, but "singleton first, list later" *)
      (* This is because I don't want to use "++" *)
      (* lexico_order ((varg.compare arg0 arg1) *)
      (*                 :: (compare ty0 ty1) :: (map2 compare tys0 tys1)) *)
      Eq
    | typ_struct tys0, typ_struct tys1 =>
      Eq
    | typ_pointer ty0, typ_pointer ty1 =>
      compare ty0 ty1
    | typ_namedt id0, typ_namedt id1 => Eq

    | _, _ => Eq
    end
  .
  Reset compare. (* 92 oblications.... *) (* I want to use "all:" here... *)


  Program Fixpoint compare (x y: t) {measure (wf_order x)}: comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => Nat.compare sz0 sz1
    | _, _ => Eq
    end
  .
  Print compare_func.
  Reset compare. (* Anyway, we cannot do reasoning on this *)


  Fail Function compare (x y: t) {measure (wf_order x)}: comparison :=
    match x, y with
    | _, _ => Eq
    end
  .
  (* Why error???????? *)
  Reset wf_order.






  Fixpoint compare_list_failing (compare: t -> t -> comparison) (a0 b0: list t): comparison :=
    match a0, b0 with
    | _, _ => Eq
    end
  .

  Fail Fixpoint compare (x y: t): comparison :=
    match x, y with
    | typ_struct tys0, typ_struct tys1 =>
      compare_list_failing compare tys0 tys1
    | _, _ => Eq
    end
  .

  Definition compare_list (compare: t -> t -> comparison) :=
    fix compare_list_ (a0 b0: list t): comparison :=
    match a0, b0 with
    | _, _ => Eq
    end
  .

  Fixpoint compare (x y: t): comparison :=
    match x, y with
    | typ_struct tys0, typ_struct tys1 =>
      compare_list compare tys0 tys1
    | _, _ => Eq
    end
  .

  Reset compare_list_failing.

  Definition case_order (x: t): nat :=
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

  Fixpoint compare (x y: t): comparison :=
    match x, y with
    | typ_int sz0, typ_int sz1 => Nat.compare sz0 sz1
    | typ_floatpoint fp0, typ_floatpoint fp1 => (floating_point.compare fp0 fp1)
    | typ_void, typ_void => Eq
    | typ_label, typ_label => Eq
    | typ_metadata, typ_metadata => Eq
    | typ_array sz0 ty0, typ_array sz1 ty1 =>
      lexico_order [Nat.compare sz0 sz1; compare ty0 ty1]
    | typ_function ty0 tys0 arg0, typ_function ty1 tys1 arg1 =>
      lexico_order
        [(compare ty0 ty1) ; (compare_list compare tys0 tys1) ; (varg.compare arg0 arg1)]
    | typ_struct tys0, typ_struct tys1 =>
      compare_list compare tys0 tys1
    | typ_pointer ty0, typ_pointer ty1 =>
      compare ty0 ty1
    | typ_namedt id0, typ_namedt id1 => Eq

    | _, _ => Nat.compare (case_order x) (case_order y)
    end
  .

  Definition lt (x y: t): Prop := compare x y = Lt.

  Ltac nat_compare_tac :=
    repeat
      match goal with
      | [H: Nat.compare ?a ?b = Eq |- _ ] => rewrite Nat.compare_eq_iff in H
      | [H: Nat.compare ?a ?b = Lt |- _ ] => rewrite Nat.compare_lt_iff in H
      | [H: Nat.compare ?a ?b = Gt |- _ ] => rewrite Nat.compare_gt_iff in H
      | [ |- Nat.compare ?a ?b = Eq ] => rewrite Nat.compare_eq_iff
      | [ |- Nat.compare ?a ?b = Lt ] => rewrite Nat.compare_lt_iff
      | [ |- Nat.compare ?a ?b = Gt ] => rewrite Nat.compare_gt_iff
      end
  .

  Ltac elim_compare :=
    match goal with
    | [ |- CompareSpec _ _ _ ?x ] => destruct x eqn:T; try econs; ss
    end
  .

  Lemma typ_ind_gen2: forall P : typ -> typ -> Prop,
      (forall X sz5, P (typ_int sz5) X /\ P X (typ_int sz5)) ->
      (forall X floating_point5,
          P (typ_floatpoint floating_point5) X /\ P X (typ_floatpoint floating_point5)) ->
      (forall X, P typ_void X /\ P X typ_void) ->
      (forall X, P typ_label X /\ P X typ_label) ->
      (forall X, P typ_metadata X /\ P X typ_metadata) ->
      (forall X (sz5 : sz) (typ5 : typ),
          P typ5 X /\ P X typ5 -> P (typ_array sz5 typ5) X /\ P X (typ_array sz5 typ5)) ->
      (forall X typ_5,
          P typ_5 X /\ P X typ_5->
          forall l varg5,
            P (typ_function typ_5 l varg5) X /\ P X (typ_function typ_5 l varg5)) ->
      (* (forall typ_5 : typ, *)
      (*     P typ_5 -> *)
      (*     forall (l : list typ) (varg5 : varg) (IH: Forall P l), P (typ_function typ_5 l varg5)) -> *)
      (* (forall (l : list typ) (IH: Forall P l), P (typ_struct l)) -> *)
      (* (forall typ5 : typ, P typ5 -> P (typ_pointer typ5)) -> *)
      (* (forall id5 : id, P (typ_namedt id5)) -> *)
      forall t0 t1 : typ, P t0 t1.
  Proof.
    intros; revert t0; revert t1; fix IH 1.
    intros; destruct t0; try (by clear IH; eauto).
    Guarded.
    - clear IH. expl H. eauto.
    - clear IH. expl H0. eauto.
    - clear IH. expl H1. eauto.
    - clear IH. expl H2. eauto.
    - clear IH. expl H3. eauto.
    - hexploit H4.
      { instantiate (1:= t0). instantiate (1:= t1). split; ss. }
      clear IH. Guarded.
      i; des. eauto.
  Abort.

  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii.
    revert y.
    induction x using typ_ind_gen; ii; ss; destruct y; ss; try by econs.
    - Fail NatTacs.elim_compare sz5 sz0. (* TODO: WHY??? Because it is tactic notation?? *)
      destruct (Nat.compare sz5 sz0) eqn:T; ss; try (by econs; ss).
      + Fail NatCompare.compare_tac. (* TODO: WHY??????? *)
        nat_compare_tac. Undo 1.
        unfold Nat.compare in *.
        Fail NatCompare.compare_tac. (* TODO: WHY??????? *)
        Fail progress nat_compare_tac.
        Undo 4.
        nat_compare_tac. clarify. econs; eauto. ss.
      + econs; ss. unfold lt. ss. nat_compare_tac. ss.
    -  elim_compare.
       + compute in T. des_ifs.
       + apply floating_pointFacts.compare_gt_iff in T.
         compute in T. des_ifs.
    - assert(SPEC:= (IHx y)).
      des_ifs; try nat_compare_tac; subst; econs.
      + inv SPEC.
        unfold eq in *. clarify.
      + inv SPEC.
        unfold lt. ss. des_ifs. nat_compare_tac. omega.
      + inv SPEC.
        unfold lt. ss. des_ifs.
        * Abort.

  Ltac fp_compare_tac :=
    repeat
      match goal with
      | [H: floating_point.compare ?a ?b = Eq |- _ ] =>
        rewrite floating_pointFacts.compare_eq_iff in H
      | [H: floating_point.compare ?a ?b = Lt |- _ ] =>
        rewrite floating_pointFacts.compare_lt_iff in H
      | [H: floating_point.compare ?a ?b = Gt |- _ ] =>
        rewrite floating_pointFacts.compare_gt_iff in H
      | [ |- floating_point.compare ?a ?b = Eq ] =>
        rewrite floating_pointFacts.compare_eq_iff
      | [ |- floating_point.compare ?a ?b = Lt ] =>
        rewrite floating_pointFacts.compare_lt_iff
      | [ |- floating_point.compare ?a ?b = Gt ] =>
        rewrite floating_pointFacts.compare_gt_iff
      end
  .

  Ltac varg_compare_tac :=
    repeat
      match goal with
      | [H: varg.compare ?a ?b = Eq |- _ ] =>
        rewrite vargFacts.compare_eq_iff in H
      | [H: varg.compare ?a ?b = Lt |- _ ] =>
        rewrite vargFacts.compare_lt_iff in H
      | [H: varg.compare ?a ?b = Gt |- _ ] =>
        rewrite vargFacts.compare_gt_iff in H
      | [ |- varg.compare ?a ?b = Eq ] =>
        rewrite vargFacts.compare_eq_iff
      | [ |- varg.compare ?a ?b = Lt ] =>
        rewrite vargFacts.compare_lt_iff
      | [ |- varg.compare ?a ?b = Gt ] =>
        rewrite vargFacts.compare_gt_iff
      end
  .


  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *.
    revert H.
    induction x using typ_ind_gen; ii; ss;
      fp_compare_tac;
      unfold floating_point.ltb in *;
      nat_compare_tac;
      try omega.
    - destruct floating_point5; ss.
    - des_ifs; nat_compare_tac; subst; ss. omega.
    - des_ifs; varg_compare_tac; subst; ss.
      + clear - Heq1. unfold varg.compare in *.
        rewrite vargFacts.compare_lt_iff in Heq1.
        Undo 2.
        unfold varg.compare in *. des_ifs.
        Fail progress nat_compare_tac.
        rewrite Nat.compare_lt_iff in *. omega.
      + clear - Heq0 IH.
        ginduction l0; ii; ss.
        inv IH.
        des_ifs.
        apply IHl0; ss.
    - ginduction l0; ii; ss.
      inv IH.
      des_ifs.
      apply IHl0; eauto.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. clarify.
  Qed.
  Next Obligation.
    ii. unfold lt in *.
    revert_until x.
    induction x using typ_ind_gen; ii; ss; destruct y, z; ss; nat_compare_tac.
    - omega.
    - fp_compare_tac.
      destruct floating_point0, floating_point1, floating_point5; ss.
    - des_ifs; nat_compare_tac; subst; ss; try omega; clear_tac.
      + expl IHx. eq_closure_tac. ss.
      + expl IHx. eq_closure_tac. ss.
    - des_ifs; nat_compare_tac; varg_compare_tac; subst; ss; try omega; clear_tac.
  Abort.


  Lemma compare_spec_aux x y:
    (CompareSpec (eq x y) (lt x y) (lt y x) (compare x y)) /\
    (CompareSpec (eq y x) (lt y x) (lt x y) (compare y x))
  .
  Proof.
    ii.
    revert y.
    induction x using typ_ind_gen; ii; ss; destruct y; ss; try by (split; ss; econs).
    - split; ss.
      + elim_compare; nat_compare_tac; subst; ss.
        unfold lt. unfold compare. nat_compare_tac. ss.
      + elim_compare; nat_compare_tac; subst; ss.
        unfold lt. unfold compare. nat_compare_tac. ss.
    - split; ss.
      + elim_compare; fp_compare_tac; subst; ss.
        unfold lt. unfold compare. fp_compare_tac. ss.
      + elim_compare; fp_compare_tac; subst; ss.
        unfold lt. unfold compare. fp_compare_tac. ss.
    - assert(SPEC:= (IHx y)). des.
      split; ss.
      + destruct (sz5 ?= sz0) eqn: COMP0; ss; try nat_compare_tac; subst; try econs.
        * inv SPEC; econs.
          { unfold eq in *. clarify. }
          { unfold lt. ss. des_ifs. nat_compare_tac. omega. }
          { unfold lt. ss.
            des_ifs; ss; [| |].
            { inv SPEC0; ss; unfold eq in *; clarify.
              eq_closure_tac. ss. }
            { unfold lt in *. eq_closure_tac. ss. }
            { nat_compare_tac. omega. } }
        * unfold lt. ss.
          des_ifs; nat_compare_tac; try omega.
        * unfold lt. ss.
          des_ifs; nat_compare_tac; try omega.
      + destruct (sz0 ?= sz5) eqn: COMP0; ss; try nat_compare_tac; subst; try econs.
        * inv SPEC0; econs.
          { unfold eq in *. clarify. }
          { unfold lt. ss. des_ifs. nat_compare_tac. omega. }
          { unfold lt. ss.
            des_ifs; ss; [| |].
            { inv SPEC; ss; unfold eq in *; clarify.
              eq_closure_tac. ss. }
            { unfold lt in *. eq_closure_tac. ss. }
            { nat_compare_tac. omega. } }
        * unfold lt. ss.
          des_ifs; nat_compare_tac; try omega.
        * unfold lt. ss.
          des_ifs; nat_compare_tac; try omega.
    - split; ss.
      + elim_compare.
        * des_ifs. compute.
          assert(SPEC:= (IHx y)). des.
          rewrite Heq in *. inv SPEC; ss.
          varg_compare_tac. subst.
          unfold eq in *. subst. clear_tac.
          f_equal; ss.
          clear - Heq0 IH IHx.
          ginduction l0; ii; ss.
          { des_ifs. }
          { des_ifs. clear_tac.
            inv IH.
            f_equal.
            - specialize (H1 t0). des. rewrite Heq in *. inv H1. ss.
            - eapply IHl0; ss.
          }
        *
  Qed.


End typ.

