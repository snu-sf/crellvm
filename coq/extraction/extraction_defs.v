Require Import syntax.
Require Import ZArith.

(* Arithmetic operations that will be used for validation, e.g. add
for the addition associativity-related optimization.  Temporarily, the
operations are defined by plus of ZArith, but later, it should be
defined by operations that are used by vellvm for soundness proof. *)

Module INTEGER_OPERATION.
  Definition add (lhs rhs : INTEGER.t) : INTEGER.t := (lhs + rhs)%Z.
  Definition sub (lhs rhs : INTEGER.t) : INTEGER.t := (lhs - rhs)%Z.
End INTEGER_OPERATION.
