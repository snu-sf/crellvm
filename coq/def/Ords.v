Require Import syntax.
Require Import alist.

Require Import infrastructure.
Require vellvm. (* In order to avoid name clash on "comparison", I didn't Import it *)

Require Import sflib.
Require Export Coqlib.
Export LLVMsyntax.
Export LLVMinfra.

Require Import Decs.


Print Orders.OrderedType.
Print OrderedType.OrderedType.
(* Which one to use? *)
Print MSetAVL.Make.
(* MSet uses Orders.OrderedType. We go for that. *)
(* FYI: OrderedType.OrderedType is only for backward compatibility: *)
(* https://coq.inria.fr/library/ *)





Require Import Orders.
(* Because "Orders" name is already used, I choose "Ords" as this file's name *)
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






Fixpoint lexico_order (x0: list comparison): comparison :=
  match x0 with
  | [] => Eq
  | Eq :: x1 => lexico_order x1
  | Lt :: _ => Lt
  | Gt :: _ => Gt
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
Module option (E: Orders.UsualOrderedType) <: Orders.UsualOrderedType.

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
    compute. eapply compare_lt_iff; ss.
  Qed.
  

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *. destruct x; ss.
    apply compare_lt_iff in H. order.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. split; ii; clarify; try order.
  Qed.
  Next Obligation.
    intros x y z LTXY LTYZ. unfold lt in *.
    destruct x, y, z; ss.
    SearchAbout (EAlt.compare).
    SearchAbout (E.compare). (* Can't we search at once?? *)
    eapply EAlt.compare_trans; eauto.
  Qed.


  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
    decide equality.
    apply eq_dec.
  Defined.

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


Module varg <: Orders.OrderedType.

  Module option_nat := option Nat.
  Include option_nat.

End varg.

















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

  Fail Function compare (x y: t) {measure (wf_order x)}: comparison :=
    match x, y with
    | _, _ => Eq
    end
  .
  (* Why??????????? *)






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

  Definition compare_list (compare: t -> t -> comparison) :=
    fix compare_list_ (a0 b0: list t): comparison :=
    match a0, b0 with
    | a :: a1, b :: b1 => lexico_order [(compare a b) ; (compare_list_ a1 b1)]
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
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



  Definition lt: t -> t -> Prop := ltb.

  Definition eq_dec (x y:t): {x = y} + {x <> y}.
    apply typ_dec.
  Defined.

  Definition compare (x y: t): comparison :=
    if(eq_dec x y) then Eq else
      (if (ltb x y) then Lt else Gt)
  .
  
  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii. destruct x, y; ss; by econs.
  Qed.

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *. unfold ltb in *. des_ifs.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. clarify.
  Qed.
  Next Obligation.
    ii. unfold lt in *. unfold ltb in *. des_ifs.
  Qed.

End typ.

