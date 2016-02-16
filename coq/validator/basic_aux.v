Require Import syntax.
Require Import decs.

Set Implicit Arguments.


(** * Auxiliary Functions on Program *)

Definition is_malloc (i: cmd) : bool :=
  match i with
    | insn_malloc _ _ _ _ => true
    | insn_alloca _ _ _ _ => true
    | _ => false
  end.

Definition get_all_nexts (t:terminator) : list l :=
  match t with
    | insn_return _ _ _ => nil
    | insn_return_void _ => nil
    | insn_br _ _ l1 l2 => l1::l2::nil
    | insn_br_uncond _ l1 => l1::nil
    | insn_unreachable _ => nil
  end.

Fixpoint power_sz (s:sz) : positive :=
  match s with
    | O => xH
    | S n => xO (power_sz n)
  end.

Definition signbit_of (s:sz) : option Int :=
  match s with 
    | O => None
    | S n => Some (Zneg (power_sz n))
  end.

Definition my_option_INTEGER_dec x y := option_dec _ INTEGER.dec x y.

Definition my_Zsucc : INTEGER.t -> INTEGER.t := Zsucc.

Definition is_even (x:INTEGER.t) : bool := INTEGER.dec (Zmod x 2) 0.
