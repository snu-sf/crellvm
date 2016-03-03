Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import sflib.
Import LLVMsyntax.
Import LLVMinfra.

Set Implicit Arguments.

Fixpoint list_forallb2 A B (P: A -> B -> bool) (la:list A) (lb:list B): bool :=
  match la, lb with
  | a::la, b::lb => P a b && list_forallb2 P la lb
  | nil, nil => true
  | _, _ => false
  end.

Fixpoint list_forallb3 A B C (P: A -> B -> C -> bool) (la:list A) (lb:list B) (lc:list C): bool :=
  match la, lb, lc with
  | a::la, b::lb, c::lc => P a b c && list_forallb3 P la lb lc
  | nil, nil, nil => true
  | _, _, _ => false
  end.

Definition forallb2AL A B (P: atom -> A -> B -> bool) (la:AssocList A) (lb:AssocList B): bool :=
  list_forallb2
    (fun ea eb => id_dec ea.(fst) eb.(fst) && P ea.(fst) ea.(snd) eb.(snd))
    la lb.

Definition is_empty A (l:list A) :=
  match l with nil => true | _ => false end.

Definition lift_option A B (pred:A -> B)
           (oa:option A): option B :=
  match oa with
  | Some a => Some (pred a)
  | None => None
  end.

Definition option_to_list A (oa:option A): list A :=
  match oa with
  | Some a => a::nil
  | None => nil
  end.

Fixpoint filter_map A B (pred:A -> option B) (l:list A): list B :=
  match l with
  | nil => nil
  | a::l =>
    match pred a with
    | Some b => b::(filter_map pred l)
    | None => filter_map pred l
    end
  end.

Fixpoint forallb_map A B (pred:A -> option B) (l:list A): option (list B) :=
  match l with
  | nil => Some nil
  | a::l =>
    match pred a, forallb_map pred l with
    | Some b, Some l => Some (b::l)
    | _, _ => None
    end
  end.

Fixpoint unique
         A (eq_dec: forall (a b:A), {a = b} + {a <> b})
         (l:list A): bool :=
  match l with
  | nil => true
  | a::l => negb (in_dec eq_dec a l) && unique eq_dec l
  end.

Definition mapAL A B (f:A -> B) (l:AssocList A): AssocList B :=
  List.map
    (fun (p:atom * A) =>
       let (atom, a) := p in (atom, (f a)))
    l.

Definition mapiAL A B (f: atom -> A -> B) (l:AssocList A): AssocList B :=
  List.map
    (fun (p:atom * A) =>
       let (atom, a) := p in (atom, (f atom a)))
    l.

(* Find FIRST occurence of element satisfying f. *)
(* If there is not, return None *)
Fixpoint find_index (A : Type) (l : list A) (f : A -> bool) : option nat :=
  match l with
      | nil => None
      | head :: tail =>
        (if(f head) then Some 0%nat else option_map S (find_index tail f))%nat
  end.

Theorem find_index_sound : forall (A : Type) (l : list A) (f : A -> bool)
                                  (idx : nat) (FIND : find_index l f = Some idx),
                             exists y, nth_error l idx = Some y /\
                                       f y = true.
Proof.
  intros A l f. induction l; intros; simpl.
  - simpl in FIND. inversion FIND.
  - simpl in FIND.
    remember (f a) as tmp.
    destruct tmp.
    + exists a; intros; split; inv FIND; auto.
    + destruct idx.
      * unfold option_map in FIND. destruct (find_index l0 f); simpl in FIND; inversion FIND.
      * exploit (IHl idx).
        destruct (find_index l0 f); simpl in FIND; inversion FIND; subst; auto.
        intro.
        inv x0.
        des.
        eexists; split; simpl; eauto.
Qed.

Theorem find_index_complete : forall (A : Type) (l : list A) (f : A -> bool)
                                     (idx : nat) (FIND : find_index l f = None),
                                (existsb f l) = false.
Proof.
  intros A l.
  induction l; intros; simpl; auto.
  simpl in FIND.
  destruct (f a); simpl in FIND.
  inversion FIND.
  simpl. apply IHl; auto.
  destruct (find_index l0 f); simpl in FIND; inversion FIND; auto.
Qed.

(* Insert element BEFORE index. If index is out of bound, it SILENTLY inserts at the last. *)
Definition insert_at (A : Type) (l : list A) (idx : nat) (x : A) : list A :=
  (firstn idx l) ++ [x] ++ (skipn idx l).

Theorem insert_at_next : forall A idx (l : list A) x y,
                           insert_at (y :: l) (S idx) x = y :: (insert_at l idx x).
Proof.
  intros.
  induction l0; simpl; auto.
Qed.

Theorem insert_at_outside_bound : forall (A : Type) (idx : nat) (l : list A) x,
                                  (idx >= length l)%nat ->
                                  insert_at l idx x = l ++ [x].
Proof.
  intros A idx l x H.
  generalize dependent idx.
  induction l; intros; simpl in *; auto.
  - induction idx; simpl; auto.
  - destruct idx.
    + inv H.
    + exploit (IHl idx).
      omega.
      intro.
      rewrite <- x1.
      rewrite <- insert_at_next.
      auto.
Qed.