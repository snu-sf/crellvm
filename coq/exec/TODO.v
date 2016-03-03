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
      | head :: tail => (if(f head) then Some 0%nat else option_map (fun p => (1 + p)) (find_index tail f))%nat
  end.

Theorem find_index_sound : forall (A : Type) (l : list A) (f : A -> bool) (idx : nat),
                             find_index l f = Some idx ->
                             exists y, nth_error l idx = Some y ->
                                       f y = true.
Proof.
  intros A l f. induction l; intros; simpl.
  - simpl in H. inversion H.
  - simpl in H.
    remember (f a) as tmp.
    destruct tmp.
    + eexists; intros.
      instantiate (1:=a).
      rewrite <- Heqtmp. auto.
    + destruct idx.
      * unfold option_map in H. destruct (find_index l0 f); simpl in H; inversion H.
      * exploit (IHl idx).
        destruct (find_index l0 f); simpl in H; inversion H; subst; auto.
        intro.
        inv x0.
        eexists; intro.
        simpl in H1.
        apply H0 in H1.
        auto.
Qed.

Theorem find_index_complete : forall (A : Type) (l : list A) (f : A -> bool) (idx : nat),
                                find_index l f = None ->
                                (existsb f l) = false.
Proof.
  intros A l.
  induction l; intros; simpl; auto.
  simpl in H.
  destruct (f a); simpl in H.
  inversion H.
  simpl. apply IHl; auto.
  destruct (find_index l0 f); simpl in H; inversion H; auto.
Qed.

(* Insert element BEFORE index. If index is not in [0,length], return None. *)
Fixpoint insert_at (A : Type) (l : list A) (idx : nat) (x : A) : option (list A) :=
  match (idx, l) with
    | (O, _) => Some (x :: l)
    | (S idx', nil) => None
    | (S idx', h :: t) => option_map (fun y => h :: y) (insert_at t idx' x)
  end.

Theorem insert_at_inside_bound : forall A (l : list A) idx x,
                                 (idx <= (length l))%nat ->
                                 exists l2,
                                   insert_at l idx x = Some l2
                                   /\ (length l + 1 = length l2)%nat
                                   /\ nth_error l2 idx = Some x
                                   /\ firstn idx l = firstn idx l2
                                   /\ skipn idx l = skipn (idx +1) l2
.
Proof.
  intros A l.
  induction l; intros; simpl.
  - eexists.
    destruct idx; subst; simpl in *; inv H.
    splits; auto.
  - destruct idx.
    + eexists.
      splits; simpl; auto.
      simpl.
      rewrite Nat.add_comm; auto.
    + remember (insert_at l0 idx x) as result.
      destruct result; subst; simpl.
      * exists (a :: l1).
        exploit (IHl idx x). simpl in H. omega.
        intro. inv x1.
        repeat des.
        rewrite <- Heqresult in H0.
        inv H0.
        splits; auto.
        subst; simpl; auto.
        rewrite H3. auto.
      * exfalso.
        exploit (IHl idx x).
        simpl in H; omega.
        intro.
        inv x1.
        repeat des.
        rewrite <- Heqresult in H0.
        inv H0.
Qed.

Theorem insert_at_outside_bound : forall A (l : list A) idx x,
                                 (idx > (length l))%nat ->
                                 insert_at l idx x = None.
Proof.
  intros A l.
  induction l; intros; simpl in *; auto.
  - destruct idx; inversion H; subst; simpl; auto.
  - destruct idx; inversion H; subst; simpl; auto.
    + unfold option_map.
    exploit (IHl (S (length l0)) x); auto.
    intro.
    rewrite x1; auto.
    + exploit (IHl idx x); auto; try omega.
      intro.
      rewrite x1.
      auto.
Qed.
