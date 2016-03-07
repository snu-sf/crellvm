Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
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
