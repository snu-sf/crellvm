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


Section LISTS.

  Fixpoint lexico_order (x0: list comparison): comparison :=
    match x0 with
    | [] => Eq
    | Eq :: x1 => lexico_order x1
    | Lt :: _ => Lt
    | Gt :: _ => Gt
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
      | a :: a1, b :: b1 => lexico_order [(compare a b) ; (compare_list_ a1 b1)]
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




(* Module Alt_from_AltUsual (E: AltUsual) <: OrdersAlt.OrderedTypeAlt := E. *)
Module Alt_from_AltUsual (E: AltUsual) <: OrdersAlt.OrderedTypeAlt := E.

Module AltUsualFacts (E: AltUsual). (* <: (AltFacts E). *)
(* TODO: How to check subtype of these? forall E, AltUsualFacts E >= AltFacts E*)

  Module EAlt <: OrdersAlt.OrderedTypeAlt := Alt_from_AltUsual E.
  Module EAltFacts := (AltFacts EAlt).
  Include EAlt.
  Include EAltFacts.

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












Module floating_point <: AltUsual.

  Definition t := floating_point.

  Definition case_ord(x: t): nat :=
    match x with
    | fp_float => 0
    | fp_double => 1
    | fp_fp128 => 2
    | fp_x86_fp80 => 3
    | fp_ppc_fp128 => 4
    end
  .

  Definition compare (x y: t): comparison := Nat.compare (case_ord x) (case_ord y).

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
         | [ H: context[Nat.compare ?a ?b] |- _ ] =>
           replace (Nat.compare a b) with (NatAltUsual.compare a b) in H by ss
         | [ |- context[Nat.compare ?a ?b] ] =>
           replace (Nat.compare a b) with (NatAltUsual.compare a b) by ss
         end.
(* I Really want to remove this tactic ... *)



Module varg <: AltUsual := option NatAltUsual.
(* Module vargFacts := AltFacts varg. *)
Module vargFacts := optionFacts varg. (* or AltUsualFacts varg directly? *)

(* Module vargFacts := OrdersFacts.OrderedTypeFacts varg. *)







(* Module CompareTac (E: Orders.UsualOrderedType). *)
(*   (* Module EAlt <: OrdersAlt.OrderedTypeAlt := OrdersAlt.OT_to_Alt E. *) *)
(*   (* Import EAlt. (* To get compare_trans *) *) *)
(*   Module EFull <: OrderedTypeFull := (OT_to_Full E). *)
(*   Module EFacts := OrdersFacts.OrderedTypeFacts EFull. *)
(*   (* Import EFacts. *) *)

(*   Ltac compare_tac := *)
(*     match goal with *)
(*     | [H: E.compare ?a ?b = Eq |- _ ] => rewrite EFacts.compare_eq_iff in H *)
(*     | [H: E.compare ?a ?b = Lt |- _ ] => rewrite EFacts.compare_lt_iff in H *)
(*     | [H: E.compare ?a ?b = Gt |- _ ] => rewrite EFacts.compare_gt_iff in H *)
(*     end. *)
  
(* End CompareTac. *)

(* Module NatCompare := CompareTac Nat. *)
(* (* NatCompare.compare_tac. *) *)
(* Module NatTacs := OrdersTac.MakeOrderTac Nat Nat. *)
(* Module NatFacts := OrdersFacts.OrderedTypeFacts Nat. *)








Module typ <: AltUsual.

  Definition t := typ.

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
    | typ_namedt id0, typ_namedt id1 => MetatheoryAtom.AtomImpl.atom_compare id0 id1

    | _, _ => Nat.compare (case_order x) (case_order y)
    end
  .



  Hint Unfold NatAltUsual.compare.

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof.
    red.
    (* unfold CompOpp. *)
    revert y.
    induction x using typ_ind_gen; ii; ss; des_ifs_safe; ss.
    - apply Nat.compare_antisym.
    - apply floating_point.compare_sym.
    - des_ifs.
    - des_ifs.
    - des_ifs.
    - erewrite IHx. abstr (compare x t0) X. clear IHx.
      rewrite Nat.compare_antisym. abstr (sz5 ?= sz0) Y.
      unfold CompOpp. des_ifs.
    - erewrite IHx. abstr (compare x t0) X. clear IHx.
      rewrite varg.compare_sym. abstr (varg.compare varg5 varg0) Y.
      (* TODO: Nat is anti_sym, varg is _sym ... *)
      (* I want to use NatALt.compare_sym instead of Nat.compare_antisym *)
      erewrite compare_list_sym; ss. abstr (compare_list compare l0 l1) Z. clear IH.
      des_ifs.
    - erewrite compare_list_sym; ss.
    - admit.
  Admitted.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Admitted.

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    do 2 intro.
    revert c.
    induction x using typ_ind_gen; ii; ss.
    - destruct y, z; ss; clarify; [].
      eapply NatAltUsual.compare_trans; eauto.
    - destruct y, z; ss; clarify; [].
      eapply floating_point.compare_trans; eauto.
    - destruct y, z; ss; clarify.
    - destruct y, z; ss; clarify.
    - destruct y, z; ss; clarify.
    - destruct y, z; ss; clarify; [].
      to_nat_alt_compare.
      destruct (NatAltUsual.compare sz5 sz0) eqn:SZ0;
        destruct (NatAltUsual.compare sz0 sz1) eqn:SZ1; ss;
          try (expl NatAltUsualFacts.EAlt.compare_leibniz; clarify); ss;
            try rewrite SZ0; try rewrite SZ1; des_ifs_safe; ss;
              try (erewrite NatAltUsual.compare_trans; eauto; []); ss.
      destruct (compare x y) eqn:CMP0;
        destruct (compare y z) eqn:CMP1; ss;
          try (expl compare_leibniz; clarify); ss;
            try rewrite CMP0; try rewrite CMP1; des_ifs_safe; ss;
              try (erewrite IHx; eauto; []); ss.
    - destruct y, z; ss; clarify; [].
      destruct (compare x y) eqn:CMP0;
        destruct (compare y z) eqn:CMP1; ss;
          try (expl compare_leibniz; clarify); ss;
            try rewrite CMP0; try rewrite CMP1; des_ifs_safe; ss;
              try (erewrite IHx; eauto; []); ss.
      admit.
  Admitted.


  (* Ltac comparison_trans_tac := *)
  (*   repeat match goal with *)
  (*          | [H: comparison_trans _ Lt = Some _ |- _ ] => *)
  (*            exploit comparison_trans_any_lt_result; try exact H; eauto. *)
  (*          end *)
  (* . *)
  Lemma compare_strong_trans: forall
      x y z c
      (TRANS: comparison_trans (compare x y) (compare y z) = Some c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    ii.
    red.
    generalize dependent c.
    (* C should be generalized first, to make "specialize" on y, z easy *)
    revert y.
    revert z.
    induction x using typ_ind_gen; ii; ss.
    - apply comparison_trans_spec in TRANS. des; ss.
      + des_ifs; []. ss.
        eapply NatAltUsualFacts.eq_repl_l; ss.
      + des_ifs; []. ss.
        eapply NatAltUsualFacts.eq_repl_r; ss.
      + des_ifs; []. ss.
        apply NatAltUsualFacts.weird_lemma; ss.
    - apply comparison_trans_spec in TRANS. des; ss.
      + des_ifs; []. ss.
        eapply NatAltUsualFacts.eq_repl_l; ss.
      + des_ifs; []. ss.
        eapply NatAltUsualFacts.eq_repl_r; ss.
      + des_ifs; []. ss.
        apply NatAltUsualFacts.weird_lemma; ss.
    - apply comparison_trans_spec in TRANS. des; ss; des_ifs.
    - apply comparison_trans_spec in TRANS. des; ss; des_ifs.
    - apply comparison_trans_spec in TRANS. des; ss; des_ifs.
    - apply comparison_trans_spec in TRANS. des; ss.
      + destruct y, z; ss; [].
        all_once des_outest_ifs; []. des_ifs_safe. clear_tac.
        erewrite NatAltUsualFacts.eq_repl_l; eauto.
        Fail rewrite XY in IHx. (* TODO: I only want to specialize "y" in IHx... *)
        destruct (compare y z) eqn:T;
          (exploit IHx; [rewrite Heq0; rewrite T; ss; eauto|]; intro XZ; des);
          rewrite XZ; des_ifs.
      + destruct y, z; ss; [].
        all_once des_outest_ifs; []. des_ifs_safe. clear_tac.
        erewrite NatAltUsualFacts.eq_repl_r; eauto.
        rename Heq0 into YZ.
        destruct (compare x y) eqn:T;
          (exploit IHx; [rewrite YZ; rewrite T; ss; eauto|]; intro XZ; des);
          rewrite XZ; des_ifs.
      + destruct y, z; ss; clarify; [].
        specialize (IHx z y).
        destruct (Nat.compare sz5 sz0) eqn:SZ0;
          destruct (Nat.compare sz0 sz1) eqn:SZ1;
          ss; to_nat_alt_compare;
            try (expl NatAltUsualFacts.EAlt.compare_leibniz; clarify); ss;
              try rewrite SZ0; try rewrite SZ1; des_ifs_safe; ss;
                try (erewrite NatAltUsual.compare_trans; eauto; ss).
        des_ifs; expl NatAltUsual.compare_trans.
    - apply compare_list_trans in IH. des.
      apply comparison_trans_spec in TRANS. des; ss.
      + destruct y, z; ss; [].
        all_once des_outest_ifs; []. des_ifs_safe. clear_tac.
        erewrite vargFacts.eq_repl_l; eauto.
        rename Heq into XY.
        destruct (compare y z) eqn:T;
          (exploit IHx; [rewrite XY; rewrite T; ss; eauto|]; intro XZ; des);
          rewrite XZ; ss.
        rename Heq0 into CMPL0.
        destruct (compare_list compare l1 l2) eqn: CMPL1; ss;
          (erewrite IH; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto).
      + destruct y, z; ss; [].
        all_once des_outest_ifs; []. des_ifs_safe. clear_tac.
        erewrite vargFacts.eq_repl_r; eauto.
        rename Heq into YZ.
        destruct (compare x y) eqn:T;
          (exploit IHx; [rewrite YZ; rewrite T; ss; eauto|]; intro XZ; des);
          rewrite XZ; ss.
        rename Heq0 into CMPL1.
        destruct (compare_list compare l0 l1) eqn: CMPL0; ss;
          (erewrite IH; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto).
      + destruct y, z; ss; clarify; [].
        all_once des_outest_ifs; []. des_ifs_safe. clear_tac.
        specialize (IHx z y).
        destruct (compare x y) eqn:CMP0;
          destruct (compare y z) eqn:CMP1;
          try (expl IHx (ss; eauto)); try rewrite IHx0; ss.
        destruct (compare_list compare l0 l1) eqn:CMPL0;
          destruct (compare_list compare l1 l2) eqn:CMPL1; ss;
            (erewrite IH; [|rewrite CMPL0; rewrite CMPL1]; ss; eauto); [].
        ss.
        destruct (varg.compare varg5 varg0) eqn:CMPV0;
          destruct (varg.compare varg0 varg1) eqn:CMPV1; ss;
            (erewrite vargFacts.compare_trans; eauto; []); ss.
    - apply compare_list_trans in IH. des.
      apply comparison_trans_spec in TRANS. des; ss.
      + destruct y, z; ss; [].
        eapply IH; eauto. rewrite TRANS. rewrite TRANS0. ss. des_ifs.
      + destruct y, z; ss; [].
        eapply IH; eauto. rewrite TRANS. rewrite TRANS0.
        rewrite comparison_trans_spec; ss. right; left; ss.
      + destruct y, z; ss; clarify; ss; [].
        eapply IH; eauto. rewrite TRANS0.
        rewrite comparison_trans_spec; ss. right; right; ss.
    - apply comparison_trans_spec in TRANS. des; ss; des_ifs; ss.
      + erewrite IHx; eauto. rewrite TRANS.
        rewrite comparison_trans_spec. left; ss.
      + erewrite IHx; eauto. rewrite TRANS0.
        rewrite comparison_trans_spec. right; left; ss.
      + erewrite IHx; eauto. rewrite TRANS0.
        rewrite comparison_trans_spec. right; right; ss.
    - apply comparison_trans_spec in TRANS. des; ss; des_ifs; ss.
  Unshelve.
    all: ss.
  Admitted.

End typ.


Module Float <: AltUsual.

  (* Floats.float *)
  Definition t := Float.
  (* Integers.Int.int *)
  (* Floats.Float.to_bits *)
  (* Floats.Float *)
  (* Floats.Float.cmp *)

  Definition compare (x y: t): comparison := FLOAT.compare x y.

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

Module const <: AltUsual.

  Definition t := const.

  Definition case_order (x: t): nat :=
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

  Fixpoint compare (x y: t): comparison :=
    match x, y with
    | const_zeroinitializer ty0, const_zeroinitializer ty1 => typ.compare ty0 ty1
    | const_int sz0 i0, const_int sz1 i1 =>
      lexico_order [Nat.compare sz0 sz1 ; Z.compare i0 i1]
    | const_floatpoint fp0 f0, const_floatpoint fp1 f1 =>
      lexico_order [floating_point.compare fp0 fp1 ; Float.compare f0 f1]
    | const_undef ty0, const_undef ty1 => 3
    | const_null ty0, const_null ty1 => 4
    | const_arr ty0 cs0, const_arr ty1 cs1 => 5
    | const_struct ty0 cs0, const_struct ty1 cs1 => 6
    | const_gid ty0 i0, const_gid ty1 i1 => 7
    | const_truncop trop0 c0 ty0, const_truncop trop1 c1 ty1 => 8
    | const_extop extop0 c0 ty0, const_extop extop1 c1 ty1 => 9
    | const_castop csop0 c0 ty0, const_castop csop1 c1 ty1 => 10
    | const_gep inb0 c0 cs0, const_gep inb1 c1 cs1 => 11
    | const_select cx0 cy0 cz0, const_select cx1 cy1 cz1 => 12
    | const_icmp cx0 cy0 cz0, const_icmp cx1 cy1 cz1 => 13
    | const_fcmp fc0 cx0 cy0, const_fcmp fc1 cx1 cy1 => 14
    | const_extractvalue c0 cs0, const_extractvalue c1 cs1 => 15
    | const_insertvalue cx0 cy0 cs0, const_insertvalue cx1 cy1 cs1 => 16
    | const_bop bop0 cx0 cy0, const_bop bop1 cx1 cy1 => 17
    | const_fbop fbop0 cx0 cy0, const_fbop fbop1 cx1 cy1 => 18

    | _, _ => Nat.compare (case_order x) (case_order y)
    end
  .

End const.

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

