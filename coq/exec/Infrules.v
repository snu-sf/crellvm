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
Require Import Debug.
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
  | ValueT.const c1, ValueT.const c2 => const_eqb c1 c2 (* How about the case, c1 == undef? *)
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
    list_forallb2 const_eqb lc1 lc2 &&
    typ_dec u1 u2
  | Expr.insertvalue t1 v1 u1 w1 lc1, Expr.insertvalue t2 v2 u2 w2 lc2 =>
    typ_dec t1 t2 &&
    cond_replace_lessdef_value x y v1 v2 &&
    typ_dec u1 u2 &&
    cond_replace_lessdef_value x y w1 w2 &&
    list_forallb2 const_eqb lc1 lc2
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

Definition cond_gep_zero (v':ValueT.t) (e:Expr.t) : bool :=
  match e with
  | Expr.gep inbound ty1 v idxlist ty2 =>
    ValueT.eq_dec v v' &&
    (List.forallb 
      (fun itm => 
        match itm with
        | (sz,idx) =>
          match idx with 
          | (ValueT.const (const_int sz_i i)) => 
            sz_dec sz sz_i &&
            const_eqb (const_int sz_i i) (const_int sz_i (INTEGER.of_Z (Size.to_Z sz_i) 0%Z true))
          | _ => false
          end
        end)
      idxlist)
  | _ => false
  end.

Definition cond_bitcast_ptr (v':ValueT.t) (e:Expr.t) : bool :=
  match e with
  | Expr.cast eop fromty v toty =>
    (match eop with 
    | castop_bitcast => 
      (match fromty, toty with
      | typ_pointer _, typ_pointer_ => ValueT.eq_dec v v'
      | _, _ => false
      end)
    | _ => false
    end)
  | _ => false
  end.

Definition cond_pointertyp (t:typ) : bool :=
  match t with
  | typ_pointer _ => true
  | _ => false
  end.

(* getInversePredicate in lib/IR/Instructions.cpp *)
Definition get_inverse_icmp_cond (c:cond) : cond :=
  match c with
    | cond_eq => cond_ne
    | cond_ne => cond_eq
    | cond_ugt => cond_ule
    | cond_uge => cond_ult
    | cond_ult => cond_uge
    | cond_ule => cond_ugt
    | cond_sgt => cond_sle
    | cond_sge => cond_slt
    | cond_slt => cond_sge
    | cond_sle => cond_sgt
  end.

Definition get_inverse_boolean_Int (b:INTEGER.t) : INTEGER.t :=
  if (Z.eq_dec (INTEGER.to_Z b) 0)
  then INTEGER.of_Z 1 1 true
  else INTEGER.of_Z 1 0 true.

Notation "$$ inv |-src y >= rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.src).(Invariant.lessdef)) (at level 41, inv, y, rhs at level 41).
Notation "$$ inv |-tgt y >= rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.tgt).(Invariant.lessdef)) (at level 41, inv, y, rhs at level 41).
Notation "$$ inv |-src y 'alloca' $$" := (IdTSet.mem y inv.(Invariant.src).(Invariant.allocas)) (at level 41, inv, y at level 41).
Notation "$$ inv |-tgt y 'alloca' $$" := (IdTSet.mem y inv.(Invariant.tgt).(Invariant.allocas)) (at level 41, inv, y at level 41).
Notation "$$ inv |-src x _|_ y $$" := ((PtrPairSet.mem (x, y) inv.(Invariant.src).(Invariant.alias).(Invariant.noalias)) || (PtrPairSet.mem (y, x) inv.(Invariant.src).(Invariant.alias).(Invariant.noalias))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-tgt x _|_ y $$" := ((PtrPairSet.mem (x, y) inv.(Invariant.tgt).(Invariant.alias).(Invariant.noalias)) || (PtrPairSet.mem (y, x) inv.(Invariant.tgt).(Invariant.alias).(Invariant.noalias))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-src x _||_ y $$" := ((ValueTPairSet.mem (x, y) inv.(Invariant.src).(Invariant.alias).(Invariant.diffblock)) || (ValueTPairSet.mem (y, x) inv.(Invariant.src).(Invariant.alias).(Invariant.diffblock))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-tgt x _||_ y $$" := ((ValueTPairSet.mem (x, y) inv.(Invariant.tgt).(Invariant.alias).(Invariant.diffblock)) || (ValueTPairSet.mem (y, x) inv.(Invariant.tgt).(Invariant.alias).(Invariant.diffblock))) (at level 41, inv, x, y at level 41).
Notation "{{ inv +++src y >= rhs }}" := (Invariant.update_src (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41, inv, y, rhs at level 41).
Notation "{{ inv +++tgt y >= rhs }}" := (Invariant.update_tgt (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41, inv, y, rhs at level 41).
Notation "{{ inv +++src y _|_ x }}" := (Invariant.update_src (Invariant.update_noalias (PtrPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++tgt y _|_ x }}" := (Invariant.update_tgt (Invariant.update_noalias (PtrPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++src y _||_ x }}" := (Invariant.update_src (Invariant.update_diffblock (ValueTPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++tgt y _||_ x }}" := (Invariant.update_tgt (Invariant.update_diffblock (ValueTPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).

(* TODO *)
Definition apply_infrule
           (m_src m_tgt:module)
           (infrule:Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  let apply_fail := (fun _: unit => (debug_print2 infrule_printer infrule
                                                  (debug_string "Infrule application failed!" inv0))) in
  let no_match_fail := (fun _: unit => debug_string "Infrule match failed!"
                                                    (debug_print2 infrule_printer infrule inv0)) in
  match infrule with
  | Infrule.add_associative x y z c1 c2 c3 s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_add s x (const_int s c1)) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_add s y (const_int s c2)) $$ &&
       cond_plus s c1 c2 c3
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_add s x (const_int s c3))}}
    else apply_fail tt
  | Infrule.add_const_not z y x c1 c2 s =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_xor s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id y) (ValueT.const (const_int s c1))) $$ &&
       cond_minus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.const (const_int s c2)) x)}}
    else apply_fail tt
  | Infrule.add_dist_sub z minusx minusy w x y s =>
    if $$ inv0 |-tgt (Expr.value (ValueT.id minusx)) 
                  >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) $$
        && $$ inv0 |-tgt (Expr.value minusy)
                      >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$
        && $$ inv0 |-tgt (Expr.bop bop_add s x y) 
                      >= (Expr.value (ValueT.id w)) $$ 
        && $$ inv0 |-tgt (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (ValueT.id w))
                      >= (Expr.value (ValueT.id z)) $$  
    then {{inv0 +++tgt (Expr.bop bop_add s (ValueT.id minusx) minusy) >= (Expr.value (ValueT.id z))}}  
    else apply_fail tt
  | Infrule.add_sub z minusy x y s =>
    if $$ inv0 |-src (Expr.value minusy) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_add s x minusy) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_sub s x y)}}
    else apply_fail tt
  | Infrule.add_commutative z x y s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_add s x y) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_add s y x)}}
    else apply_fail tt
  | Infrule.add_commutative_tgt z x y s =>
    if $$ inv0 |-tgt (Expr.bop bop_add s x y) >= (Expr.value z) $$
    then {{inv0 +++tgt (Expr.bop bop_add s y x) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.add_mask z y y' x c1 c2 s =>
      if $$ inv0 |-tgt (Expr.bop bop_and s x (ValueT.const (const_int s c2))) >= (Expr.value (ValueT.id y)) $$ &&
         $$ inv0 |-tgt (Expr.bop bop_add s x (ValueT.const (const_int s c1))) >= (Expr.value (ValueT.id y')) $$ &&
         $$ inv0 |-tgt (Expr.bop bop_and s (ValueT.id y') (ValueT.const (const_int s c2))) >= (Expr.value (ValueT.id z)) $$ &&
         cond_mask_up s c1 c2
      then {{inv0 +++tgt (Expr.bop bop_add s (ValueT.id y) (ValueT.const (const_int s c1))) >= (Expr.value (ValueT.id z)) }}
      else apply_fail tt
  | Infrule.add_select_zero z x y c n a s =>
      if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_sub s n a) $$ &&
         $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.select c (typ_int s) (ValueT.id x) (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$ &&
         $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id y) a) $$
      then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.select c (typ_int s) n a) }}
      else apply_fail tt
  | Infrule.add_select_zero2 z x y c n a s =>
      if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_sub s n a) $$ &&
         $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.select c (typ_int s) (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (ValueT.id x)) $$ &&
         $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id y) a) $$
      then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.select c (typ_int s) a n) }}
      else apply_fail tt
  | Infrule.add_shift y v s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_add s v v) $$
    then {{inv0 +++src (Expr.value y) >= (Expr.bop bop_shl s v (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true)))}}
    else apply_fail tt
  | Infrule.add_signbit x e1 e2 s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_add s e1 e2) $$ &&
       cond_signbit s e2
    then {{inv0 +++src (Expr.value x) >= (Expr.bop bop_xor s e1 e2)}}
    else apply_fail tt
  | Infrule.add_xor_and z a b x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_xor s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_and s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id x) (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_or s a b)}}
    else apply_fail tt
  | Infrule.add_or_and z a b x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_or s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_and s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id x) (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s a b)}}
    else apply_fail tt
  | Infrule.and_commutative z x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_and s x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_and s y x)}}
    else apply_fail tt
  | Infrule.and_de_morgan z x y z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s a (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s b (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value (ValueT.id y))$$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s a b) >= (Expr.value (ValueT.id z')) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.id z') (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value (ValueT.id z)) $$
    then {{inv0 +++tgt (Expr.bop bop_and s (ValueT.id x) (ValueT.id y)) >= (Expr.value (ValueT.id z))}}
    else apply_fail tt
  | Infrule.and_mone z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value x) }}
    else apply_fail tt
  | Infrule.and_not z x y s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x y) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
    else apply_fail tt
  | Infrule.and_or z x y a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x y) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_or s x a) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value x) }}
    else apply_fail tt
  | Infrule.and_same z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x x) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value x)}}
    else apply_fail tt
  | Infrule.and_undef z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_undef (typ_int s)))) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_undef (typ_int s))))}}
    else apply_fail tt
  | Infrule.and_zero z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
    else apply_fail tt
  | Infrule.bitcast_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_inttoptr src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_inttoptr srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ 
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_inttoptr srcty src dstty) }}
    else apply_fail tt
  | Infrule.bop_distributive_over_selectinst opcode r s t' t x y z c bopsz selty =>
    if $$ inv0 |-tgt (Expr.bop opcode bopsz x y) >= (Expr.value (ValueT.id r)) $$ &&
       $$ inv0 |-tgt (Expr.bop opcode bopsz x z) >= (Expr.value (ValueT.id s)) $$ &&
       $$ inv0 |-tgt (Expr.select c (typ_int bopsz) y z) >= (Expr.value (ValueT.id t')) $$ &&
       $$ inv0 |-tgt (Expr.bop opcode bopsz x t') >= (Expr.value (ValueT.id t)) $$
     then {{ inv0 +++tgt (Expr.select c (typ_int bopsz) (ValueT.id r) (ValueT.id s)) >= (Expr.value (ValueT.id t)) }}
     else apply_fail tt
  | Infrule.bop_distributive_over_selectinst2 opcode r s t' t x y z c bopsz selty =>
    if $$ inv0 |-tgt (Expr.bop opcode bopsz y x) >= (Expr.value (ValueT.id r)) $$ &&
       $$ inv0 |-tgt (Expr.bop opcode bopsz z x) >= (Expr.value (ValueT.id s)) $$ &&
       $$ inv0 |-tgt (Expr.select c (typ_int bopsz) y z) >= (Expr.value (ValueT.id t')) $$ &&
       $$ inv0 |-tgt (Expr.bop opcode bopsz t' x) >= (Expr.value (ValueT.id t)) $$
     then {{ inv0 +++tgt (Expr.select c (typ_int bopsz) (ValueT.id r) (ValueT.id s)) >= (Expr.value (ValueT.id t)) }}
     else apply_fail tt
  | Infrule.sdiv_mone z x s => 
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_sdiv s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) }}
    else apply_fail tt
  | Infrule.bitcastptr v v' bitcastinst =>
    if $$ inv0 |-src (Expr.value v) >= bitcastinst $$ &&
       $$ inv0 |-src bitcastinst >= (Expr.value v) $$ &&
       cond_bitcast_ptr v' bitcastinst
    then 
      let inv0 := {{inv0 +++src (Expr.value v) >= (Expr.value v')}} in
      {{inv0 +++src (Expr.value v') >= (Expr.value v)}}
    else apply_fail tt
  | Infrule.bitcastptr_tgt v v' bitcastinst =>
    if $$ inv0 |-tgt (Expr.value v) >= bitcastinst $$ &&
       $$ inv0 |-tgt bitcastinst >= (Expr.value v) $$ &&
       cond_bitcast_ptr v' bitcastinst
    then 
      let inv0 := {{inv0 +++tgt (Expr.value v) >= (Expr.value v')}} in
      {{inv0 +++tgt (Expr.value v') >= (Expr.value v)}}
    else apply_fail tt
  | Infrule.fadd_commutative_tgt z x y fty =>
    if $$ inv0 |-tgt (Expr.fbop fbop_fadd fty x y) >= (Expr.value (ValueT.id z)) $$
    then {{ inv0 +++tgt (Expr.fbop fbop_fadd fty y x) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.fbop_distributive_over_selectinst fbopcode r s t' t x y z c fbopty selty =>
    if $$ inv0 |-tgt (Expr.fbop fbopcode fbopty x y) >= (Expr.value (ValueT.id r)) $$ &&
       $$ inv0 |-tgt (Expr.fbop fbopcode fbopty x z) >= (Expr.value (ValueT.id s)) $$ &&
       $$ inv0 |-tgt (Expr.select c (typ_floatpoint fbopty) y z) >= (Expr.value (ValueT.id t')) $$ &&
       $$ inv0 |-tgt (Expr.fbop fbopcode fbopty x t') >= (Expr.value (ValueT.id t)) $$
     then {{ inv0 +++tgt (Expr.select c (typ_floatpoint fbopty) (ValueT.id r) (ValueT.id s)) >= (Expr.value (ValueT.id t)) }}
    else apply_fail tt
  | Infrule.fbop_distributive_over_selectinst2 fbopcode r s t' t x y z c fbopty selty =>
    if $$ inv0 |-tgt (Expr.fbop fbopcode fbopty y x) >= (Expr.value (ValueT.id r)) $$ &&
       $$ inv0 |-tgt (Expr.fbop fbopcode fbopty z x) >= (Expr.value (ValueT.id s)) $$ &&
       $$ inv0 |-tgt (Expr.select c (typ_floatpoint fbopty) y z) >= (Expr.value (ValueT.id t')) $$ &&
       $$ inv0 |-tgt (Expr.fbop fbopcode fbopty t' x) >= (Expr.value (ValueT.id t)) $$
     then {{ inv0 +++tgt (Expr.select c (typ_floatpoint fbopty) (ValueT.id r) (ValueT.id s)) >= (Expr.value (ValueT.id t)) }}
    else apply_fail tt
  | Infrule.fpext_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_fp midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.fptosi_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_fptosi midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptosi srcty src dstty) }}
    else apply_fail tt
  | Infrule.fptoui_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_fptoui midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptoui srcty src dstty) }}
    else apply_fail tt
  | Infrule.gepzero v v' gepinst =>
    if $$ inv0 |-src (Expr.value v) >= gepinst $$ &&
       $$ inv0 |-src gepinst >= (Expr.value v) $$ &&
       cond_gep_zero v' gepinst
    then 
      let inv0 := {{inv0 +++src (Expr.value v) >= (Expr.value v')}} in
      {{inv0 +++src (Expr.value v') >= (Expr.value v)}}
    else apply_fail tt
  | Infrule.inttoptr_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_inttoptr midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_inttoptr srcty src dstty) }}
    else apply_fail tt
  | Infrule.lessthan_undef ty v => 
    {{ inv0 +++src (Expr.value (ValueT.const (const_undef ty))) >= (Expr.value v) }}
  | Infrule.sdiv_sub_srem z b a x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id b)) >= (Expr.bop bop_srem s x y) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id a)) >= (Expr.bop bop_sub s x (ValueT.id b)) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sdiv s (ValueT.id a) y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sdiv s x y) }}
    else apply_fail tt
  | Infrule.udiv_sub_urem z b a x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id b)) >= (Expr.bop bop_urem s x y) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id a)) >= (Expr.bop bop_sub s x (ValueT.id b)) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_udiv s (ValueT.id a) y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_udiv s x y) }}
    else apply_fail tt
  | Infrule.sub_add z my x y s =>
    if $$ inv0 |-src (Expr.value my) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_sub s x my) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_add s x y)}}
    else apply_fail tt
  | Infrule.sub_sub z x y w s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_sub s x y) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s w x) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y)}}
    else apply_fail tt
  | Infrule.neg_val c1 c2 s =>
    if cond_plus s c1 c2 (INTEGER.of_Z (Size.to_Z s) 0%Z true)  
    then 
      let inv0 := 
      {{inv0 +++src (Expr.value (const_int s c1)) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) (const_int s c2))}} in
      {{inv0 +++tgt (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) (const_int s c2)) >= (Expr.value (const_int s c1))}}
    else apply_fail tt
  | Infrule.mul_mone z x s =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_mul s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
    then {{ inv0 +++src (Expr.value (ValueT.id z)) 
                >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) }}
    else apply_fail tt
  | Infrule.mul_neg z mx my x y s =>
    if $$ inv0 |-src (Expr.value mx) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) x) $$ &&
       $$ inv0 |-src (Expr.value my) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_mul s mx my) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_mul s x y)}}
    else apply_fail tt
  | Infrule.mul_bool z x y =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_mul Size.One x y) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_and Size.One x y) }}
    else apply_fail tt
  | Infrule.mul_commutative z x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_mul s x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_mul s y x)}}
    else apply_fail tt
  | Infrule.mul_shl z y x a s =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_shl s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true))) a) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_mul s (ValueT.id y) x) $$
    then {{ inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_shl s x a) }}
    else apply_fail tt
  | Infrule.or_and z y x a s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_and s x a) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s y x) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value x) }}
    else apply_fail tt
  | Infrule.or_and_xor z x y a b s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_and s a b) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s a b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s x y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_or s a b) }}
    else apply_fail tt
  | Infrule.or_commutative z x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_or s x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_or s y x)}}
    else apply_fail tt
  | Infrule.or_commutative_tgt z x y s =>
    if $$ inv0 |-tgt (Expr.bop bop_or s x y) >= (Expr.value (ValueT.id z)) $$
    then {{inv0 +++tgt (Expr.bop bop_or s y x) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.or_not z y x s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s x 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s x y) $$ 
    then {{ inv0 +++src (Expr.value z) >= (Expr.value 
              (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
    else apply_fail tt
  | Infrule.or_mone z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s a 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
    else apply_fail tt
  | Infrule.or_or z x y a b s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_xor s a (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_and s x b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s y a) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_or s a b) }}
    else apply_fail tt
  | Infrule.or_or2 z x y y' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_and s a b) >= (Expr.value x) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s a (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value y) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s a (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value y') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s y' b) >= (Expr.value z)$$
    then {{ inv0 +++tgt (Expr.bop bop_or s x y) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.or_same z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s a a) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value a) }}
    else apply_fail tt
  | Infrule.or_undef z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s a (ValueT.const (const_undef (typ_int s)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value 
              (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
    else apply_fail tt
  | Infrule.or_xor w z x y a b s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_xor s b (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_and s a x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s a b) $$ &&
       $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_or s y z) $$
    then {{ inv0 +++src (Expr.value w) >= (Expr.bop bop_xor s a b) }}
    else apply_fail tt
  | Infrule.or_xor2 z x1 y1 x2 y2 a b s =>
    if $$ inv0 |-src (Expr.value x1) >= (Expr.bop bop_xor s b (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value y1) >= (Expr.bop bop_and s a x1) $$ &&
       $$ inv0 |-src (Expr.value x2) >= (Expr.bop bop_xor s a (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value y2) >= (Expr.bop bop_and s x2 b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s y1 y2) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_xor s a b) }}
    else apply_fail tt
  | Infrule.or_xor3 z y a b s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s a b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s a y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_or s a b) }}
    else apply_fail tt
  | Infrule.or_xor4 z x y a b nb s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s x (ValueT.const (const_int s 
                (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value a) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s a b) >= (Expr.value y) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s b (ValueT.const (const_int s 
                (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value nb) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s nb x) >= (Expr.value z) $$
    then {{ inv0 +++tgt (Expr.bop bop_or s x y) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.or_zero z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_or s a 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value a) }}
    else apply_fail tt
  | Infrule.ptrtoint_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_ptrtoint midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_ptrtoint srcty src dstty) }}
    else apply_fail tt
  | Infrule.sub_const_add z y x c1 c2 c3 s =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_add s x (ValueT.const (const_int s c1))) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.const (const_int s c2)) (ValueT.id y)) $$ &&
       cond_minus s c2 c1 c3
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.const (const_int s c3)) x) }}
    else apply_fail tt
  | Infrule.sub_const_not z y x c1 c2 s =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_xor s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.const (const_int s c1)) (ValueT.id y)) $$ &&
       cond_plus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s x (ValueT.const (const_int s c2)))}}
    else apply_fail tt
  | Infrule.sub_mone z x s =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))) x) $$
      then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_xor s x 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))))}}
      else apply_fail tt
  | Infrule.sub_or_xor z a b x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_or s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_xor s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub s (ValueT.id x) (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_and s a b)}}
    else apply_fail tt
  | Infrule.sub_remove z y a b sz =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_add sz a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub sz a (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub sz (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true)) b) }}
    else apply_fail tt
  | Infrule.sub_onebit z x y =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub Size.One x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_xor Size.One x y)}}
    else apply_fail tt
  | Infrule.sub_shl z x y mx a sz =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) mx) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_shl sz x a) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_shl sz mx a) }}
    else apply_fail tt
  | Infrule.sub_sdiv z y x c c' sz =>
    if $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_sdiv sz x (ValueT.const (const_int sz c))) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sub sz (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) (ValueT.id y)) $$ &&
       cond_minus sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true) c c'
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_sdiv sz x (ValueT.const (const_int sz c'))) }}
    else apply_fail tt
  | Infrule.add_onebit z x y =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add Size.One x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_xor Size.One x y)}}
    else apply_fail tt
  | Infrule.add_zext_bool x y b c c' sz =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.ext extop_z (typ_int Size.One) b (typ_int sz)) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_add sz (ValueT.id x) (ValueT.const (const_int sz c))) $$ &&
       cond_plus sz c (INTEGER.of_Z (Size.to_Z sz) 1%Z true) c'
    then {{ inv0 +++src (Expr.value (ValueT.id y)) >= (Expr.select b (typ_int sz) (ValueT.const (const_int sz c')) (ValueT.const (const_int sz c))) }}
    else apply_fail tt
  | Infrule.sext_sext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_s srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_s midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_s srcty src dstty) }}
    else apply_fail tt
  | Infrule.sitofp_sext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_s srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_sitofp midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_sitofp srcty src dstty) }}
    else apply_fail tt
  | Infrule.transitivity e1 e2 e3 =>
    if $$ inv0 |-src e1 >= e2 $$ &&
       $$ inv0 |-src e2 >= e3 $$ 
    then {{ inv0 +++src e1 >= e3 }}
    else apply_fail tt
  | Infrule.transitivity_tgt e1 e2 e3 =>
    if $$ inv0 |-tgt e1 >= e2 $$ &&
       $$ inv0 |-tgt e2 >= e3 $$
    then {{ inv0 +++tgt e1 >= e3 }}
    else apply_fail tt
  | Infrule.trunc_ptrtoint src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_ptrtoint srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_ptrtoint srcty src dstty) }}
    else apply_fail tt
  | Infrule.rem_neg z my x y s =>
    if $$ inv0 |-src (Expr.value my) >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ && 
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_srem s x my) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_srem s x y) }}
    else apply_fail tt
  | Infrule.diffblock_global_alloca gx y =>
    match gx with
    | const_gid gx_ty gx_id =>
      if $$ inv0 |-src y alloca $$ then
        let inv1 := {{inv0 +++src (ValueT.id y) _||_ (ValueT.const gx) }} in
        let inv2 := {{inv1 +++src (ValueT.const gx) _||_ (ValueT.id y) }} in
        inv2
      else apply_fail tt
    | _ => apply_fail tt
    end
  | Infrule.diffblock_global_global gx gy =>
    match gx with
    | const_gid gx_ty gx_id =>
      match gy with
      | const_gid gy_ty gy_id =>
        if id_dec gx_id gy_id
        then debug_string "diffblock_global_global : id_dec" (apply_fail tt)
        else 
          let inv1 := {{inv0 +++src (ValueT.const (const_gid gx_ty gx_id)) _||_ (ValueT.const (const_gid gy_ty gy_id)) }} in
          let inv2 := {{inv1 +++src (ValueT.const (const_gid gy_ty gy_id)) _||_ (ValueT.const (const_gid gx_ty gx_id)) }} in
          inv2
      | _ => debug_string "diffblock_global_global : gy not globalvar" (apply_fail tt)
      end
    | _ => debug_string "diffblock_global_global : gx not globalvar" (apply_fail tt)
    end
  | Infrule.diffblock_lessthan x y x' y' =>
    if $$ inv0 |-src x _||_ y $$ &&
       $$ inv0 |-src (Expr.value x) >= (Expr.value x') $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.value y') $$
    then {{inv0 +++src x' _||_ y'}}
    else apply_fail tt
  | Infrule.diffblock_noalias x y (x', x_type') (y', y_type') =>
    if $$ inv0 |-src x _||_ y $$ &&
       ValueT.eq_dec x x' && ValueT.eq_dec y y'
    then {{inv0 +++src (x', x_type') _|_ (y', y_type')}}
    else apply_fail tt
  | Infrule.transitivity_pointer_lhs p q v ty a =>
    if $$ inv0 |-src (Expr.value p) >= (Expr.value q) $$ &&
       $$ inv0 |-src (Expr.load q ty a) >= (Expr.value v) $$
    then {{inv0 +++src (Expr.load p ty a) >= (Expr.value v)}}
    else apply_fail tt
  | Infrule.transitivity_pointer_rhs p q v ty a =>
    if $$ inv0 |-src (Expr.value p) >= (Expr.value q) $$ &&
       $$ inv0 |-src (Expr.value v) >= (Expr.load p ty a) $$
    then {{inv0 +++src (Expr.value v) >= (Expr.load q ty a)}}
    else apply_fail tt
  | Infrule.trunc_trunc src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.trunc truncop_int srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$
    then {{inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_int srcty src dstty)}}
    else apply_fail tt
  | Infrule.substitute x y e =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.value y) $$
    then
      let x_to_y := (fun v =>
                       match v with
                       | ValueT.id i => if(IdT.eq_dec x i) then y else v
                       | _ => v
                       end) in
      {{inv0 +++src e >= (Expr.map_valueTs e x_to_y)}}
    else apply_fail tt
  | Infrule.substitute_rev x y e =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.value x) $$
    then
      let x_to_y := (fun v =>
                       match v with
                       | ValueT.id i => if(IdT.eq_dec x i) then y else v
                       | _ => v
                       end) in
      {{inv0 +++src (Expr.map_valueTs e x_to_y) >= e}}
    else apply_fail tt
  | Infrule.replace_rhs x y e1 e2 e2' =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.value y) $$ &&
       $$ inv0 |-src e1 >= e2 $$ &&
       cond_replace_lessdef x y e2 e2'
    then {{inv0 +++src e1 >= e2'}}
    else apply_fail tt
  | Infrule.replace_rhs_opt x y e1 e2 e2' =>
    if $$ inv0 |-tgt (Expr.value x) >= (Expr.value y) $$ &&
       $$ inv0 |-tgt e1 >= e2 $$ &&
       cond_replace_lessdef x y e2 e2'
    then {{inv0 +++tgt e1 >= e2'}}
    else apply_fail tt
  | Infrule.sext_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_s midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_z srcty src dstty) }}
    else apply_fail tt
  | Infrule.udiv_zext z x y k a b s1 s2 =>
    if $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) a (typ_int s2)) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) b (typ_int s2)) >= (Expr.value (ValueT.id y)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_udiv s1 a b) >= (Expr.value (ValueT.id k)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) (ValueT.id k) (typ_int s2)) >= (Expr.value (ValueT.id z)) $$
    then {{ inv0 +++tgt (Expr.bop bop_udiv s2 (ValueT.id x) (ValueT.id y)) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.uitofp_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_uitofp midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_uitofp srcty src dstty) }}
    else apply_fail tt
  | Infrule.urem_zext z x y k a b s1 s2 =>
    if $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) a (typ_int s2)) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) b (typ_int s2)) >= (Expr.value (ValueT.id y)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_urem s1 a b) >= (Expr.value (ValueT.id k)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) (ValueT.id k) (typ_int s2)) >= (Expr.value (ValueT.id z)) $$
    then {{ inv0 +++tgt (Expr.bop bop_urem s2 (ValueT.id x) (ValueT.id y)) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.intro_eq x => 
    {{ inv0 +++src (Expr.value x) >= (Expr.value x) }}
  | Infrule.intro_ghost x g =>
    if Invariant.not_in_maydiff inv0 x
    then if (negb (IdTSet.mem (Tag.ghost, g) (IdTSet_from_list (Invariant.get_idTs inv0))))
         then {{
          {{ inv0 +++src (Expr.value x) >= (Expr.value (ValueT.id (Tag.ghost, g))) }}
                  +++tgt (Expr.value (ValueT.id (Tag.ghost, g))) >= (Expr.value x)
         }}
         else
          (Invariant.update_src (Invariant.update_lessdef 
            (ExprPairSet.add ((Expr.value x), (Expr.value (ValueT.id (Tag.ghost, g))))))
          (Invariant.update_tgt (Invariant.update_lessdef 
            (ExprPairSet.add ((Expr.value (ValueT.id (Tag.ghost, g))), (Expr.value x))))
          (Invariant.update_src (Invariant.update_lessdef 
            (ExprPairSet.filter
              (fun (p: ExprPair.t) => negb (Expr.eq_dec (Expr.value (ValueT.id (Tag.ghost, g))) (snd p)))))
          (Invariant.update_tgt (Invariant.update_lessdef 
            (ExprPairSet.filter
              (fun (p: ExprPair.t) => negb (Expr.eq_dec (Expr.value (ValueT.id (Tag.ghost, g))) (fst p)))))
           inv0))))
    else apply_fail tt
  | Infrule.xor_commutative z x y s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s x y) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_xor s y x)}}
    else apply_fail tt
  | Infrule.xor_commutative_tgt z x y s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s x y) >= (Expr.value z) $$
    then {{inv0 +++tgt (Expr.bop bop_xor s y x) >= (Expr.value z)}}
    else apply_fail tt
  | Infrule.xor_not z y x s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s x 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s x y) $$ 
    then {{ inv0 +++src (Expr.value z) >= (Expr.value 
              (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
    else apply_fail tt
  | Infrule.xor_same z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s a a) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
    else apply_fail tt
  | Infrule.xor_undef z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s a (ValueT.const (const_undef (typ_int s)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_undef (typ_int s)))) }}
    else apply_fail tt
  | Infrule.xor_zero z a s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_xor s a 
                (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value a) }}
    else apply_fail tt
  | Infrule.zext_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_z midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_z srcty src dstty) }}
    else apply_fail tt
  | Infrule.icmp_inverse c ty x y b =>
    if $$ inv0 |-src (Expr.icmp c ty x y) >= (Expr.value (ValueT.const (const_int Size.One b))) $$
    then
      let c' := get_inverse_icmp_cond c in
      let b' := get_inverse_boolean_Int b in
      {{inv0 +++src (Expr.icmp c' ty x y) >= (Expr.value (ValueT.const (const_int Size.One b')))}}
    else apply_fail tt
  | Infrule.implies_false c1 c2 =>
    if $$ inv0 |-src (Expr.value c1) >= (Expr.value c2) $$
       && (negb (const_eqb c1 c2))
    then {{inv0 +++src fst (Invariant.false_encoding) >=
           snd (Invariant.false_encoding)}}
    else apply_fail tt
  | Infrule.icmp_eq_same ty x y =>
    let Int_one := INTEGER.of_Z 1 1 true in
    if $$ inv0 |-src (Expr.value (ValueT.const (const_int Size.One Int_one))) >= (Expr.icmp cond_eq ty x y) $$
    then {{
             {{inv0 +++src (Expr.value x) >= (Expr.value y)}}
               +++src (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | Infrule.icmp_neq_same ty x y =>
    let Int_zero := INTEGER.of_Z 1 0 true in
    if $$ inv0 |-src (Expr.value (ValueT.const (const_int Size.One Int_zero))) >= (Expr.icmp cond_ne ty x y) $$
    then {{
             {{inv0 +++src (Expr.value x) >= (Expr.value y)}}
               +++src (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | _ => no_match_fail tt (* TODO *)
  end.

(* TODO *)
Definition apply_infrules
           (m_src m_tgt:module)
           (infrules:list Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  fold_left (fun i r => apply_infrule m_src m_tgt r i) infrules inv0.
