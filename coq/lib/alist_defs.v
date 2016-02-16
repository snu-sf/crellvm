Require Import Metatheory.
Require Import alist.


(*
supplementary materials for assocative list (alist.v).

1) on leAL and orthogonalAL; and
2) on decidability.  We validate (rather than verify) so that we have to implement decidability.
*)

Section MoreAssocLists.
  Variable X : Set.
  Definition X_dec := forall (x y : X), {x = y} + {~ x = y}.

  Definition leAL lc1 lc2 :=
    forall i v, lookupAL X lc1 i = Some v -> lookupAL X lc2 i = Some v.

  Definition leAL_dec (dec : X_dec) (lc1 lc2 : AssocList X) :
    {leAL lc1 lc2} + {True}.
  Proof.
    generalize dependent lc2. induction lc1.

    (* lc1 is nil *)
    intros lc2. left. unfold leAL. intros i v H. inversion H.

    (* lc1 is not nil *)
    destruct a. intros lc2. remember (lookupAL X lc2 a). 
    destruct o; [idtac|right;auto].
    destruct (dec x x0); [idtac|right;auto].
    destruct (IHlc1 lc2); [idtac|right;auto].
    left. unfold leAL. simpl. intros i v H. destruct (eq_dec i a).
    inversion H. subst. subst. auto. apply l. auto.
  Defined.

End MoreAssocLists.
