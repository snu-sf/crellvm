Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Integers.

Require Import Exprs.
Require Import Hints.
Require Import TODO.

Require Import Decs.
Set Implicit Arguments.

(* Copied from validator/basic_aux.v because ocaml-extracted version of this code cannot find validator/basic_aux.v *)
Fixpoint power_sz (s:sz) : positive :=
  match s with
    | O => xH
    | S n => xO (power_sz n)
  end.

(* Copied from validator/basic_aux.v because ocaml-extracted version of this code cannot find validator/basic_aux.v *)
Definition signbit_of (s:sz) : option Int :=
  match s with 
    | O => None
    | S n => Some (Zneg (power_sz n))
  end.

Definition is_ghost (g:IdT.t) :=
  match g with
  | (tag, _) => if Tag.eq_dec tag Tag.ghost then true else false
  end.

Definition cond_fresh (g:IdT.t) (inv:Invariant.t) : bool :=
  negb (List.existsb (fun x => IdT.eq_dec g x) (Invariant.get_idTs inv)).

Definition cond_plus (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec _)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
    (Int.add (Size.to_nat s - 1)
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Definition cond_minus (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec (Size.to_nat s - 1))
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
  (Int.sub (Size.to_nat s - 1)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Definition cond_mask_up (s:sz) (c1i c2i:INTEGER.t) : bool :=
  let ws := (Size.to_nat s - 1)%nat in
  let c1 := (Int.repr ws (INTEGER.to_Z c1i)) in
  let mc1 := (Int.sub ws (Int.zero ws) c1) in
  let c2 := (Int.repr ws (INTEGER.to_Z c2i)) in
  let c1up := (Int.not ws (Int.sub ws (Int.and ws c1 mc1) (Int.one ws))) in
    (Int.eq_dec ws) (Int.and ws c1up c2) c1up.


Definition cond_signbit (s:sz) (v:ValueT.t) : bool :=
  match signbit_of s, v with
  | None, _ => false
  | Some n, ValueT.const (const_int s' n') =>
    sz_dec s s' && INTEGER.dec n n'
  | _, _ => false
  end.


(* cond_replace_value_lessdef x y v v' : 
   Given x >= y, if all x in v1 are replaced into y(let the replaced value v2), is v2 >= v'? *)
Definition cond_replace_lessdef_value (x:IdT.t) (y:ValueT.t) (v v':ValueT.t) : bool :=
  match v, v' with
  | ValueT.id a, _ =>
    (IdT.eq_dec a x && ValueT.eq_dec v' y) || (ValueT.eq_dec v v')
  | ValueT.const c1, ValueT.const c2 => const_dec c1 c2 (* How about the case, c1 == undef? *)
  | _,_ => false
  end.

(* cond_replace_lessdef x y e e' : 
   Given x >= y, If all x in e are replaced into y(let the replaced expression e2), is e2 >= e'? *)
Definition cond_replace_lessdef (x:IdT.t) (y:ValueT.t) (e e':Expr.t) : bool :=
  match e, e' with
  | Expr.bop b1 s1 v1 w1, Expr.bop b2 s2 v2 w2 =>
    bop_dec b1 b2 &&
    Size.dec s1 s2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    cond_replace_lessdef_value x y w1 w2
  | Expr.fbop fb1 fp1 v1 w1, Expr.fbop fb2 fp2 v2 w2 =>
    fbop_dec fb1 fb2 &&
    floating_point_dec fp1 fp2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    cond_replace_lessdef_value x y w1 w2
  | Expr.extractvalue t1 v1 lc1 u1, Expr.extractvalue t2 v2 lc2 u2 =>
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    list_const_dec lc1 lc2 &&
    typ_dec u1 u2
  | Expr.insertvalue t1 v1 u1 w1 lc1, Expr.insertvalue t2 v2 u2 w2 lc2 =>
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec u1 u2 &&
    cond_replace_lessdef_value x y w1 w2 &&
    list_const_dec lc1 lc2
  | Expr.gep ib1 t1 v1 lsv1 u1, Expr.gep ib2 t2 v2 lsv2 u2 =>
    inbounds_dec ib1 ib2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    beq_nat (List.length lsv1) (List.length lsv2) &&
    List.forallb (fun k => match k with ((_, h1), (_, h2)) => cond_replace_lessdef_value x y h1 h2 end) (List.combine lsv1 lsv2) &&
    typ_dec u1 u2
  | Expr.trunc top1 t1 v1 u1, Expr.trunc top2 t2 v2 u2 =>
    truncop_dec top1 top2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec u1 u2
  | Expr.ext ex1 t1 v1 u1, Expr.ext ex2 t2 v2 u2 =>
    extop_dec ex1 ex2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec u1 u2
  | Expr.cast cop1 t1 v1 u1, Expr.cast cop2 t2 v2 u2 =>
    castop_dec cop1 cop2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec u1 u2
  | Expr.icmp con1 t1 v1 w1, Expr.icmp con2 t2 v2 w2 =>
    cond_dec con1 con2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    cond_replace_lessdef_value x y w1 w2
  | Expr.fcmp fcon1 fp1 v1 w1, Expr.fcmp fcon2 fp2 v2 w2 =>
    fcond_dec fcon1 fcon2 &&
    floating_point_dec fp1 fp2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    cond_replace_lessdef_value x y w1 w2
  | Expr.select v1 t1 w1 z1, Expr.select v2 t2 w2 z2 =>
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y w1 w2 &&
    cond_replace_lessdef_value x y z1 z2
  | Expr.value v1, Expr.value v2 =>
    cond_replace_lessdef_value x y v1 v2
  | Expr.load v1 t1 a1, Expr.load v2 t2 a2 => 
    (* FIXME : Is this condition ok? *)
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec t1 t2 &&
    Align.dec a1 a2
  | _, _ => false
  end.


Notation "$$ inv |- y >=src rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.src).(Invariant.lessdef)) (at level 41).
Notation "$$ inv |- y >=tgt rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.tgt).(Invariant.lessdef)) (at level 41).
Notation "$$ inv |-allocasrc y $$" := (IdTSet.mem y inv.(Invariant.src).(Invariant.allocas)) (at level 41).
Notation "$$ inv |-allocatgt y $$" := (IdTSet.mem y inv.(Invariant.tgt).(Invariant.allocas)) (at level 41).
Notation "{{ inv +++ y >=src rhs }}" := (Invariant.update_src (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41).
Notation "{{ inv +++ y >=tgt rhs }}" := (Invariant.update_tgt (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41).
Notation "{{ inv +++ y _|_src x }}" := (Invariant.update_src (Invariant.update_noalias (ValueTPairSet.add (y, x))) inv) (at level 41).
Notation "{{ inv +++ y _|_tgt x }}" := (Invariant.update_tgt (Invariant.update_noalias (ValueTPairSet.add (y, x))) inv) (at level 41).

(* TODO *)
Definition apply_infrule
           (m_src m_tgt:module)
           (infrule:Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  match infrule with
  | Infrule.add_associative x y z c1 c2 c3 s =>
    if $$ inv0 |- (Expr.value y) >=src (Expr.bop bop_add s x (const_int s c1)) $$ &&
       $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_add s y (const_int s c2)) $$ &&
       cond_plus s c1 c2 c3
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_add s x (const_int s c3))}}
    else inv0
  | Infrule.add_const_not z y x c1 c2 s =>
    if $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_xor s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id y) (ValueT.const (const_int s c1))) $$ &&
       cond_minus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub s (ValueT.const (const_int s c2)) x)}}
    else inv0
  | Infrule.add_sub z minusy x y s =>
    if $$ inv0 |- (Expr.value minusy) >=src (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_add s x minusy) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_sub s x y)}}
    else inv0
  | Infrule.add_commutative z x y s =>
    if $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_add s x y) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_add s y x)}}
    else inv0
  | Infrule.add_mask z y y' x c1 c2 s =>
      if $$ inv0 |- (Expr.bop bop_and s x (ValueT.const (const_int s c2))) >=tgt (Expr.value (ValueT.id y)) $$ &&
         $$ inv0 |- (Expr.bop bop_add s x (ValueT.const (const_int s c1))) >=tgt (Expr.value (ValueT.id y')) $$ &&
         $$ inv0 |- (Expr.bop bop_and s (ValueT.id y') (ValueT.const (const_int s c2))) >=tgt (Expr.value (ValueT.id z)) $$ &&
         cond_mask_up s c1 c2
      then {{inv0 +++ (Expr.bop bop_add s (ValueT.id y) (ValueT.const (const_int s c1))) >=tgt (Expr.value (ValueT.id z)) }}
      else inv0
  | Infrule.add_select_zero z x y c n a s =>
      if $$ inv0 |- (Expr.value (ValueT.id x)) >=src (Expr.bop bop_sub s n a) $$ &&
         $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.select c (typ_int s) (ValueT.id x) (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$ &&
         $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id y) a) $$
      then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.select c (typ_int s) n a) }}
      else inv0
  | Infrule.add_select_zero2 z x y c n a s =>
      if $$ inv0 |- (Expr.value (ValueT.id x)) >=src (Expr.bop bop_sub s n a) $$ &&
         $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.select c (typ_int s) (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (ValueT.id x)) $$ &&
         $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id y) a) $$
      then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.select c (typ_int s) a n) }}
      else inv0
  | Infrule.add_shift y v s =>
    if $$ inv0 |- (Expr.value y) >=src (Expr.bop bop_add s v v) $$
    then {{inv0 +++ (Expr.value y) >=src (Expr.bop bop_shl s v (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true)))}}
    else inv0
  | Infrule.add_signbit x e1 e2 s =>
    if $$ inv0 |- (Expr.value x) >=src (Expr.bop bop_add s e1 e2) $$ &&
       cond_signbit s e2
    then {{inv0 +++ (Expr.value x) >=src (Expr.bop bop_xor s e1 e2)}}
    else inv0
  | Infrule.sub_add z my x y s =>
    if $$ inv0 |- (Expr.value my) >=src (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_sub s x my) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_add s x y)}}
    else inv0
  | Infrule.neg_val c1 c2 s =>
    if cond_plus s c1 c2 (INTEGER.of_Z (Size.to_Z s) 0%Z true)  
    then {{inv0 +++ (Expr.value (const_int s c1)) >=src (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) (const_int s c2))}}
    else inv0
  | Infrule.mul_neg z mx my x y s =>
    if $$ inv0 |- (Expr.value mx) >=src (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) x) $$ &&
       $$ inv0 |- (Expr.value my) >=src (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_mul s mx my) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_mul s x y)}}
    else inv0
  | Infrule.mul_bool z x y =>
    if $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_mul Size.One x y) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_and Size.One x y) }}
    else inv0
  | Infrule.sub_mone z x s =>
    if $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub s 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))) x) $$
      then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_xor s x 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))))}}
      else inv0
  | Infrule.sub_remove z y a b sz =>
    if $$ inv0 |- (Expr.value y) >=src (Expr.bop bop_add sz a b) $$ &&
       $$ inv0 |- (Expr.value z) >=src (Expr.bop bop_sub sz a y) $$
    then {{inv0 +++ (Expr.value z) >=src (Expr.bop bop_sub sz (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true)) b) }}
    else inv0
  | Infrule.sub_onebit z x y =>
    if $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub Size.One x y) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_xor Size.One x y)}}
    else inv0
  | Infrule.sub_shl z x y mx a sz =>
    if $$ inv0 |- (Expr.value x) >=src (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) mx) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_shl sz x a) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) (ValueT.id y)) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_shl sz mx a) }}
    else inv0
  | Infrule.sub_sdiv z y x c c' sz =>
    if $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_sdiv sz x (ValueT.const (const_int sz c))) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) (ValueT.id y)) $$ &&
       cond_minus sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true) c c'
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sdiv sz x (ValueT.const (const_int sz c'))) }}
    else inv0
  | Infrule.add_onebit z x y =>
    if $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add Size.One x y) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_xor Size.One x y)}}
    else inv0
  | Infrule.add_zext_bool x y b c c' sz =>
    if $$ inv0 |- (Expr.value (ValueT.id x)) >=src (Expr.ext extop_z (typ_int Size.One) b (typ_int sz)) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_add sz (ValueT.id x) (ValueT.const (const_int sz c))) $$ &&
       cond_plus sz c (INTEGER.of_Z (Size.to_Z sz) 1%Z true) c'
    then {{ inv0 +++ (Expr.value (ValueT.id y)) >=src (Expr.select b (typ_int sz) (ValueT.const (const_int sz c')) (ValueT.const (const_int sz c))) }}
    else inv0
  | Infrule.transitivity e1 e2 e3 =>
    if $$ inv0 |- e1 >=src e2 $$ &&
       $$ inv0 |- e2 >=src e3 $$ 
    then {{inv0 +++ e1 >=src e3}}
    else inv0
  | Infrule.noalias_global_alloca x y =>
    match x with
    | (Tag.physical, x_id) =>
      match lookupTypViaGIDFromModule m_src x_id with
      | None => inv0
      | Some x_type => (* x is a global variable *)
        if $$ inv0 |-allocasrc y $$ then
          {{inv0 +++ (ValueT.id y) _|_src (ValueT.const (const_gid x_type x_id)) }}
        else inv0
      end
    | _ => inv0
    end
  | Infrule.transitivity_pointer_lhs p q v ty a =>
    if $$ inv0 |- (Expr.value p) >=src (Expr.value q) $$ &&
       $$ inv0 |- (Expr.load q ty a) >=src (Expr.value v) $$
    then {{inv0 +++ (Expr.load p ty a) >=src (Expr.value v)}}
    else inv0
  | Infrule.transitivity_pointer_rhs p q v ty a =>
    if $$ inv0 |- (Expr.value p) >=src (Expr.value q) $$ &&
       $$ inv0 |- (Expr.value v) >=src (Expr.load p ty a) $$
    then {{inv0 +++ (Expr.value v) >=src (Expr.load q ty a)}}
    else inv0
  | Infrule.bop_both_src_left b x y z sz =>
    if $$ inv0 |- (Expr.value y) >=src (Expr.value z) $$
    then {{inv0 +++ (Expr.bop b sz x y) >=src (Expr.bop b sz x z)}}
    else inv0
  | Infrule.bop_both_src_right b x y z sz =>
    if $$ inv0 |- (Expr.value y) >=src (Expr.value z) $$
    then {{inv0 +++ (Expr.bop b sz y x) >=src (Expr.bop b sz z x)}}
    else inv0
  | Infrule.bop_both_tgt_left b x y z sz =>
    if $$ inv0 |- (Expr.value y) >=tgt (Expr.value z) $$
    then {{inv0 +++ (Expr.bop b sz x y) >=tgt (Expr.bop b sz x z)}}
    else inv0
  | Infrule.bop_both_tgt_right b x y z sz =>
    if $$ inv0 |- (Expr.value y) >=tgt (Expr.value z) $$
    then {{inv0 +++ (Expr.bop b sz y x) >=tgt (Expr.bop b sz z x)}}
    else inv0
 | Infrule.intro_eq e g =>
    if is_ghost g
       && Invariant.not_in_maydiff_expr inv0 e
       && cond_fresh g inv0
    then {{ {{ {{ {{inv0 +++ e >=src (Expr.value (ValueT.id g)) }}
                         +++ (Expr.value (ValueT.id g)) >=src e }}
                         +++ e >=tgt (Expr.value (ValueT.id g)) }}
                         +++ (Expr.value (ValueT.id g)) >=tgt e }}
    else inv0
  | Infrule.replace_rhs x y e1 e2 e2' =>
    if $$ inv0 |- (Expr.value x) >=src (Expr.value y) $$ &&
       $$ inv0 |- e1 >=src e2 $$ &&
       cond_replace_lessdef x y e2 e2'
    then {{inv0 +++ e1 >=src e2'}}
    else inv0
  | _ => inv0 (* TODO *)
  end.

(* TODO *)
Definition apply_infrules
           (m_src m_tgt:module)
           (infrules:list Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  fold_left (fun i r => apply_infrule m_src m_tgt r i) infrules inv0.
