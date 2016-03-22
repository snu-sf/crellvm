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

Definition get_or_else A (x: option A) (default: A) :=
  match x with
    | None => default
    | Some _x => _x
  end.

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

Definition lift2_option
           A B (pred:A -> B -> Prop)
           (oa:option A) (ob:option B): Prop :=
  match oa, ob with
  | Some a, Some b => pred a b
  | None, None => True
  | _, _ => False
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

Definition mapAL := Metatheory.EnvImpl.map.

Definition mapiAL A B (f: atom -> A -> B) (l:AssocList A): AssocList B :=
  List.map
    (fun (p:atom * A) =>
       let (atom, a) := p in (atom, (f atom a)))
    l.

(* Find FIRST occurence of element satisfying f. *)
(* If there is not, return None *)
Fixpoint find_index (A:Type) (l:list A) (f:A -> bool):option nat :=
  match l with
  | nil => None
  | head :: tail =>
    if (f head) then Some 0%nat else option_map S (find_index tail f)
  end.

Lemma find_index_sound
      (A:Type) (l:list A) (f:A -> bool) (idx:nat)
      (FIND:find_index l f = Some idx):
  exists y, nth_error l idx = Some y /\
       f y = true.
Proof.
  revert idx FIND. induction l; intros; simpl in *.
  - inv FIND.
  - destruct (f a) eqn:FA.
    + inv FIND. exists a. split; auto.
    + destruct (find_index l0 f) eqn:FIND'; inv FIND.
      exploit IHl; eauto.
Qed.

Lemma find_index_complete
      (A:Type) (l:list A) (f:A -> bool)
      (idx:nat) (FIND:find_index l f = None):
  negb (existsb f l).
Proof.
  revert FIND. induction l; intros; simpl in *; auto.
  destruct (f a), (find_index l0 f);
    simpl in *; try congruence.
  auto.
Qed.

(* Insert element BEFORE index. If index is out of bound, it SILENTLY inserts at the last. *)
Definition insert_at (A:Type) (idx:nat) (x:A) (l:list A): list A :=
  (firstn idx l) ++ [x] ++ (skipn idx l).
