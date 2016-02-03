Require Import syntax.
Require Import alist.
Require Import extraction_defs.
Require Import decs.
Require Import syntax_ext.
Require Import hints.
Require Import basic_aux.
Require Import vars_aux.
Require Import datatype_base.
Require Import Floats.

Require Import Integers.

Set Implicit Arguments.

(** * Inference Rules Semantics
  *)

Definition cond_plus (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec (Size.to_nat s - 1))
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

Definition cond_szplus (s2:sz) (n:INTEGER.t) (s1:sz) : bool :=
  Z_eq_dec ((Size.to_Z s2)+(INTEGER.to_Z n)) (Size.to_Z s1).

Definition cond_szlt (s1:sz) (s2:sz) : bool :=
  Z_lt_dec (Size.to_Z s1) (Size.to_Z s2).

Definition cond_mask_up (s:sz) (c1i c2i:INTEGER.t) : bool :=
let ws := (Size.to_nat s - 1)%nat in
let c1 := (Int.repr ws (INTEGER.to_Z c1i)) in
let mc1 := (Int.sub ws (Int.zero ws) c1) in
let c2 := (Int.repr ws (INTEGER.to_Z c2i)) in
let c1up := (Int.not ws (Int.sub ws (Int.and ws c1 mc1) (Int.one ws))) in
  (Int.eq_dec ws) (Int.and ws c1up c2) c1up.

Definition cond_same_value (md:maydiff_t) (v: value_ext) : bool :=
  match v with
  | value_ext_id x => negb (IdExtSetImpl.mem x md)
  | _ => true
  end.

Fixpoint cond_same_lsv (md:maydiff_t) (lsv:list (sz * value_ext)) : bool :=
  match lsv with
  | nil => true
  | (_,v)::t => cond_same_value md v && cond_same_lsv md t
  end.

Fixpoint cond_same_params (md:maydiff_t) (ps:params_ext) : bool :=
  match ps with
  | nil => true
  | (_,v)::t => cond_same_value md v && cond_same_params md t
  end.

Definition cond_same (md:maydiff_t) (e: rhs_ext) : bool :=
  match e with
  | rhs_ext_extractvalue _ ve1 _ _
  | rhs_ext_trunc _ _ ve1 _
  | rhs_ext_ext _ _ ve1 _
  | rhs_ext_cast _ _ ve1 _
  | rhs_ext_value ve1
    => cond_same_value md ve1
  | rhs_ext_bop _ _ ve1 ve2
  | rhs_ext_fbop _ _ ve1 ve2
  | rhs_ext_insertvalue _ ve1 _ ve2 _
  | rhs_ext_icmp _ _ ve1 ve2
  | rhs_ext_fcmp _ _ ve1 ve2
    => cond_same_value md ve1 && cond_same_value md ve2
  | rhs_ext_select ve1 _ ve2 ve3
    => cond_same_value md ve1 && cond_same_value md ve2 && cond_same_value md ve3
  | rhs_ext_gep _ _ ve1 lsv1 _
    => cond_same_value md ve1 && cond_same_lsv md lsv1
  | rhs_ext_old_alloca => false
  end.

Definition cond_replace_value (x:id_ext) (y:value_ext) (v1 v2:value_ext) : bool :=
  match v1, v2 with
  | value_ext_id a, _ =>
    (id_ext_dec a x && value_ext_dec v2 y) || (value_ext_dec v1 v2)
  | value_ext_const c1, value_ext_const c2 => const_dec c1 c2
  | _,_ => false
  end.

Fixpoint cond_replace_lsv (x:id_ext) (y:value_ext) (lsv1 lsv2:list (sz * value_ext)) : bool :=
  match lsv1,lsv2 with
  | nil, nil => true
  | (_,h1)::t1,(_,h2)::t2 =>
    cond_replace_value x y h1 h2 && cond_replace_lsv x y t1 t2
  | _,_ => false
  end.

Definition cond_replace (x:id_ext) (y:value_ext) (e e':rhs_ext) : bool :=
  match e, e' with
  | rhs_ext_bop b1 s1 v1 w1, rhs_ext_bop b2 s2 v2 w2 =>
    bop_dec b1 b2 &&
    sz_dec s1 s2 &&
    cond_replace_value x y v1 v2 &&
    cond_replace_value x y w1 w2
  | rhs_ext_fbop fb1 fp1 v1 w1, rhs_ext_fbop fb2 fp2 v2 w2 =>
    fbop_dec fb1 fb2 &&
    floating_point_dec fp1 fp2 &&
    cond_replace_value x y v1 v2 &&
    cond_replace_value x y w1 w2
  | rhs_ext_extractvalue t1 v1 lc1 u1, rhs_ext_extractvalue t2 v2 lc2 u2 =>
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    list_const_dec lc1 lc2 &&
    typ_dec u1 u2
  | rhs_ext_insertvalue t1 v1 u1 w1 lc1, rhs_ext_insertvalue t2 v2 u2 w2 lc2 =>
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    typ_dec u1 u2 &&
    cond_replace_value x y w1 w2 &&
    list_const_dec lc1 lc2
  | rhs_ext_gep ib1 t1 v1 lsv1 u1, rhs_ext_gep ib2 t2 v2 lsv2 u2 =>
    inbounds_dec ib1 ib2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    cond_replace_lsv x y lsv1 lsv2 &&
    typ_dec u1 u2
  | rhs_ext_trunc top1 t1 v1 u1, rhs_ext_trunc top2 t2 v2 u2 =>
    truncop_dec top1 top2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    typ_dec u1 u2
  | rhs_ext_ext ex1 t1 v1 u1, rhs_ext_ext ex2 t2 v2 u2 =>
    extop_dec ex1 ex2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    typ_dec u1 u2
  | rhs_ext_cast cop1 t1 v1 u1, rhs_ext_cast cop2 t2 v2 u2 =>
    castop_dec cop1 cop2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    typ_dec u1 u2
  | rhs_ext_icmp con1 t1 v1 w1, rhs_ext_icmp con2 t2 v2 w2 =>
    cond_dec con1 con2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y v1 v2 &&
    cond_replace_value x y w1 w2
  | rhs_ext_fcmp fcon1 fp1 v1 w1, rhs_ext_fcmp fcon2 fp2 v2 w2 =>
    fcond_dec fcon1 fcon2 &&
    floating_point_dec fp1 fp2 &&
    cond_replace_value x y v1 v2 &&
    cond_replace_value x y w1 w2
  | rhs_ext_select v1 t1 w1 z1, rhs_ext_select v2 t2 w2 z2 =>
    cond_replace_value x y v1 v2 &&
    typ_dec t1 t2 &&
    cond_replace_value x y w1 w2 &&
    cond_replace_value x y z1 z2
  | rhs_ext_value v1, rhs_ext_value v2 =>
    cond_replace_value x y v1 v2
  | rhs_ext_old_alloca, rhs_ext_old_alloca => true
  | _, _ => false
  end.

Definition cond_signbit (sz:sz) (s:value_ext) : bool :=
  match signbit_of sz, s with
  | None, _ => false
  | Some n, value_ext_const (const_int sz' n') =>
    sz_dec sz sz' &&
    INTEGER.dec n n'
  | _, _ => false
  end.

Definition cond_fresh_id_ext (t:id) (x:id_ext) : bool :=
  negb (id_dec t (fst x)).

Definition cond_fresh_md (t:id) (md:maydiff_t) : bool :=
  IdExtSetImpl.for_all (cond_fresh_id_ext t) md.

Definition cond_fresh_value_ext (t:id) (ve:value_ext) : bool :=
  match ve with
    | value_ext_id x => cond_fresh_id_ext t x
    | value_ext_const _ => true
  end.

Fixpoint cond_fresh_lsv (t:id) (lsv:list (sz * value_ext)) : bool :=
  match lsv with
  | nil => true
  | (_,h)::lsv' =>
    cond_fresh_value_ext t h && cond_fresh_lsv t lsv'
  end.

Definition cond_fresh_rhs_ext (t:id) (r:rhs_ext) : bool :=
  match r with
  | rhs_ext_extractvalue _ ve1 _ _
  | rhs_ext_trunc _ _ ve1 _
  | rhs_ext_ext _ _ ve1 _
  | rhs_ext_cast _ _ ve1 _
  | rhs_ext_value ve1
    => cond_fresh_value_ext t ve1
  | rhs_ext_bop _ _ ve1 ve2
  | rhs_ext_fbop _ _ ve1 ve2
  | rhs_ext_insertvalue _ ve1 _ ve2 _
  | rhs_ext_icmp _ _ ve1 ve2
  | rhs_ext_fcmp _ _ ve1 ve2
    => cond_fresh_value_ext t ve1 && cond_fresh_value_ext t ve2
  | rhs_ext_select ve1 _ ve2 ve3
    => cond_fresh_value_ext t ve1 && cond_fresh_value_ext t ve2 && cond_fresh_value_ext t ve3
  | rhs_ext_gep _ _ ve1 lsv1 _
    => cond_fresh_value_ext t ve1 && cond_fresh_lsv t lsv1
  | rhs_ext_old_alloca => true
  end.

Definition cond_fresh_eq_reg (t:id) (e:EqRegSetImpl.t) : bool :=
  EqRegSetImpl.for_all
  (fun xr => cond_fresh_id_ext t (fst xr) && cond_fresh_rhs_ext t (snd xr))
  e.

Definition cond_fresh_eq_heap (t:id) (e:EqHeapSetImpl.t) : bool :=
  EqHeapSetImpl.for_all
  (fun xy =>
    let '(x,_,_,y) := xy in
    cond_fresh_value_ext t x && cond_fresh_value_ext t y)
  e.

Definition cond_fresh_localglobal (t:id) (lg:localglobal_t) : bool :=
  match lg with
    | inl x => cond_fresh_id_ext t x
    | inr x => negb (id_dec t x)
  end.

Definition cond_fresh_neq_reg (t:id) (e:NeqRegSetImpl.t) : bool :=
  NeqRegSetImpl.for_all
  (fun xlg => cond_fresh_id_ext t (fst xlg) && cond_fresh_localglobal t (snd xlg))
  e.

Definition cond_fresh_eqs (t:id) (e:eqs_t) : bool :=
  cond_fresh_eq_reg t (eqs_eq_reg e) &&
  cond_fresh_eq_heap t (eqs_eq_heap e) &&
  cond_fresh_neq_reg t (eqs_neq_reg e).

Definition cond_fresh_inv (t:id) (i:invariant_t) : bool :=
  cond_fresh_eqs t (invariant_original i) &&
  cond_fresh_eqs t (invariant_optimized i).

Definition cond_fresh (t:id) (h:insn_hint_t) : bool :=
  cond_fresh_md t (hint_maydiff h) &&
  cond_fresh_inv t (hint_invariant h).

Definition float_zero_rhs (fp:floating_point) : rhs_ext :=
  rhs_ext_value (value_ext_const (const_floatpoint fp (Float.of_int (Int.one 31)))).

Definition cond_not_alloca (h:rhs_ext) : bool :=
  match h with
    | rhs_ext_old_alloca => false
    | _ => true
  end.

Definition cond_is_defined (x:id_ext) (eqs:EqRegSetImpl.t) : bool :=
  EqRegSetImpl.exists_
  (fun item => id_ext_dec (fst item) x && cond_not_alloca (snd item))
  eqs.

Definition cond_is_global (x:id) (m:module) : bool :=
  List.existsb (fun y => id_dec y x) (collect_global_ids (get_products_from_module m)).

Notation "$$ h |- y =r1 rhs $$" := (mem_eq_reg_orig (y, rhs) h) (at level 41).
Notation "$$ h |- y =r2 rhs $$" := (mem_eq_reg_opt (y, rhs) h) (at level 41).
Notation "$$ h |- pta =h1 v $$" := (mem_eq_heap_orig (pta, v) h) (at level 41).
Notation "$$ h |- pta =h2 v $$" := (mem_eq_heap_opt (pta, v) h) (at level 41).

Notation "{{ h +++ y =r1 rhs }}" := (add_eq_reg_orig (y, rhs) h) (at level 41).
Notation "{{ h +++ y =r2 rhs }}" := (add_eq_reg_opt (y, rhs) h) (at level 41).
Notation "{{ h +++ y ~=r1 rhs }}" := (add_neq_reg_orig (y, rhs) h) (at level 41).
Notation "{{ h +++ pta =h1 rhs }}" := (add_eq_heap_orig (pta, rhs) h) (at level 41).
Notation "{{ h +++ pta =h2 rhs }}" := (add_eq_heap_opt (pta, rhs) h) (at level 41).
Notation "{{ h --- md }}" := (remove_md md h) (at level 41).

Definition infrule_sem (m1 m2:module) (inf: infrule_t) (h: insn_hint_t) : insn_hint_t :=
  match inf with

    | rule_add_assoc z y x s c1 c2 c3 =>
      if $$ h |- y =r1 (rhs_ext_bop bop_add s x (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) (value_ext_const (const_int s c2))) $$ &&
         cond_plus s c1 c2 c3
      then {{h +++ z =r1 (rhs_ext_bop bop_add s x (value_ext_const (const_int s c3)))}}
      else h

    | rule_replace_rhs z x y e e' =>
      if $$ h |- x =r1 (rhs_ext_value y) $$ &&
         $$ h |- z =r1 e $$ &&
         (cond_replace x y e e')
      then {{h +++ z =r1 e'}}
      else h

    | rule_replace_rhs_opt z x y e e' =>
      if $$ h |- x =r2 (rhs_ext_value y) $$ &&
         $$ h |- z =r2 e $$ &&
         (cond_replace x y e e')
      then {{h +++ z =r2 e'}}
      else h

    | rule_replace_lhs x y e =>
      if ($$ h |- x =r1 (rhs_ext_value (value_ext_id y)) $$ ||
          $$ h |- y =r1 (rhs_ext_value (value_ext_id x)) $$) &&
          $$ h |- x =r1 e $$ &&
          cond_not_alloca e
      then {{ h +++ y =r1 e }}
      else h

    | rule_remove_maydiff z e =>
      if $$ h |- z =r1 e $$ &&
         $$ h |- z =r2 e $$ &&
         cond_same (hint_maydiff h) e
      then {{h --- z}}
      else h

    | rule_remove_maydiff_rhs z e =>
      if $$ h |- z =r1 (rhs_ext_value (value_ext_id e)) $$ &&
         $$ h |- z =r2 (rhs_ext_value (value_ext_id e)) $$ &&
         negb (mem_md z h)
      then {{h --- z}}
      else h

    | rule_eq_generate_same x y e =>
      if $$ h |- x =r1 e $$ &&
         $$ h |- y =r1 e $$ &&
         cond_not_alloca e
      then {{h +++ x =r1 (rhs_ext_value (value_ext_id y))}}
      else h

    | rule_eq_generate_same_heap x y p t a =>
      if $$ h |- (p, t, a) =h1 (value_ext_id x) $$ &&
         $$ h |- (p, t, a) =h1 (value_ext_id y) $$
      then {{h +++ x =r1 (rhs_ext_value (value_ext_id y))}}
      else h

    | rule_eq_generate_same_heap_value x p v t a =>
      if $$ h |- (p, t, a) =h1 (value_ext_id x) $$ &&
         $$ h |- (p, t, a) =h1 v $$
      then {{h +++ x =r1 (rhs_ext_value v)}}
      else h

    | rule_add_signbit x sz e s =>
      if $$ h |- x =r1 (rhs_ext_bop bop_add sz e s) $$ &&
         cond_signbit sz s
      then {{ h +++ x =r1 (rhs_ext_bop bop_xor sz e s) }}
      else h

    | rule_add_zext_bool x y b sz c c' =>
      if $$ h |- x =r1 (rhs_ext_ext extop_z (typ_int Size.One) b (typ_int sz)) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_add sz (value_ext_id x) (value_ext_const (const_int sz c))) $$ &&
         cond_plus sz c (INTEGER.of_Z (Size.to_Z sz) 1%Z true) c'
      then {{ h +++ y =r1 (rhs_ext_select b (typ_int sz) (value_ext_const (const_int sz c')) (value_ext_const (const_int sz c))) }}
      else h

    | rule_ptr_trans p q v t a =>
      if $$ h |- p =r1 (rhs_ext_value q) $$ &&
         $$ h |- (value_ext_id p, t, a) =h1 v $$
      then {{ h +++ (q, t, a) =h1 v }}
      else h

    | rule_add_onebit z x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_add Size.One x y) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_xor Size.One x y)}}
      else h

    | rule_stash_variable z t =>
      if negb (mem_md z h) &&
         cond_fresh t h &&
         cond_is_defined z (eqs_eq_reg (invariant_original (hint_invariant h))) &&
         cond_is_defined z (eqs_eq_reg (invariant_optimized (hint_invariant h)))
      then
        {{ {{h +++ (vars_aux.add_otag t) =r2 rhs_ext_value (value_ext_id z)}}
               +++ (vars_aux.add_otag t) =r1 (rhs_ext_value (value_ext_id z))}}
      else h

    | rule_add_shift y s x =>
      if $$ h |- y =r1 (rhs_ext_bop bop_add s x x) $$
      then {{h +++ y =r1 (rhs_ext_bop bop_shl s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true))))}}
      else h

    | rule_add_sub z minusy s x y =>
      if $$ h |- minusy =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s x (value_ext_id minusy)) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_sub s x y)}}
      else h

    | rule_add_commutative z s x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_add s x y) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_add s y x)}}
      else h

    | rule_sub_add z minusy s x y =>
      if $$ h |- minusy =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s x (value_ext_id minusy)) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_add s x y)}}
      else h

    | rule_sub_onebit z x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_sub Size.One x y) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_xor Size.One x y)}}
      else h

    | rule_sub_mone z s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))) x) $$
      then {{h +++ z =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true))))}}
      else h

    | rule_sub_const_not z y s x c1 c2 =>
      if $$ h |- y =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s c1)) (value_ext_id y)) $$ &&
         cond_plus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
      then {{h +++ z =r1 (rhs_ext_bop bop_add s x (value_ext_const (const_int s c2)))}}
      else h

    | rule_add_const_not z y s x c1 c2 =>
      if $$ h |- y =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) (value_ext_const (const_int s c1))) $$ &&
         cond_minus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
      then {{h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s c2)) x)}}
      else h

    | rule_add_mul_fold z y s x c1 c2 =>
      if $$ h |- y =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) x) $$ &&
         cond_plus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
      then {{h +++ z =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c2)))}}
      else h

    | rule_add_select_zero z x y c s n a =>
      if $$ h |- x =r1 (rhs_ext_bop bop_sub s n a) $$ &&
         $$ h |- y =r1 (rhs_ext_select c (typ_int s) (value_ext_id x) (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) a) $$
      then {{ h +++ z =r1 (rhs_ext_select c (typ_int s) n a) }}
      else h

    | rule_add_select_zero2 z x y c s n a =>
      if $$ h |- x =r1 (rhs_ext_bop bop_sub s n a) $$ &&
         $$ h |- y =r1 (rhs_ext_select c (typ_int s) (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (value_ext_id x)) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) a) $$
      then {{ h +++ z =r1 (rhs_ext_select c (typ_int s) a n) }}
      else h

    | rule_sub_zext_bool x y b sz c c' =>
      if $$ h |- x =r1 (rhs_ext_ext extop_z (typ_int Size.One) b (typ_int sz)) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_sub sz (value_ext_const (const_int sz c)) (value_ext_id x)) $$ &&
         cond_minus sz c (INTEGER.of_Z (Size.to_Z sz) 1%Z true) c'
      then {{ h +++ y =r1 (rhs_ext_select b (typ_int sz) (value_ext_const (const_int sz c')) (value_ext_const (const_int sz c))) }}
      else h

    | rule_sub_const_add z y s x c1 c2 c3 =>
      if $$ h |- y =r1 (rhs_ext_bop bop_add s x (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s c2)) (value_ext_id y)) $$ &&
         cond_minus s c2 c1 c3
      then {{ h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s c3)) x) }}
      else h

    | rule_sub_remove z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_add s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s a (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) b) }}
      else h

    | rule_sub_remove2 z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_sub s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_id y) a) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) b) }}
      else h

    | rule_sub_sdiv z y s x c c' =>
      if $$ h |- y =r1 (rhs_ext_bop bop_sdiv s x (value_ext_const (const_int s c))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (value_ext_id y)) $$ &&
         cond_minus s (INTEGER.of_Z (Size.to_Z s) 0%Z true) c c'
      then {{ h +++ z =r1 (rhs_ext_bop bop_sdiv s x (value_ext_const (const_int s c'))) }}
      else h

    | rule_sub_shl z x y s mx a =>
      if $$ h |- x =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) mx) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_shl s (value_ext_id x) a) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_shl s mx a) }}
      else h

    | rule_sub_mul z y s x c c' =>
      if $$ h |- y =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s x (value_ext_id y)) $$ &&
         cond_minus s (INTEGER.of_Z (Size.to_Z s) 1%Z true) c c'
      then {{ h +++ z =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c'))) }}
      else h

    | rule_sub_mul2 z y s x c c' =>
      if $$ h |- y =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sub s (value_ext_id y) x) $$ &&
         cond_minus s c (INTEGER.of_Z (Size.to_Z s) 1%Z true) c'
      then {{ h +++ z =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s c'))) }}
      else h

    | rule_mul_mone z s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_mul s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) }}
      else h

    | rule_mul_neg z mx my s x y =>
      if $$ h |- mx =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) $$ &&
         $$ h |- my =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_mul s (value_ext_id mx) (value_ext_id my)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_mul s x y) }}
      else h

    | rule_mul_bool z x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_mul Size.One x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_and Size.One x y) }}
      else h

    | rule_mul_commutative z s x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_mul s x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_mul s y x) }}
      else h

    | rule_mul_shl z y s x a =>
      if $$ h |- y =r1 (rhs_ext_bop bop_shl s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true))) a) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_mul s (value_ext_id y) x) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_shl s x a) }}
      else h

    | rule_div_sub_srem z b a s x y =>
      if $$ h |- b =r1 (rhs_ext_bop bop_srem s x y) $$ &&
         $$ h |- a =r1 (rhs_ext_bop bop_sub s x (value_ext_id b)) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_sdiv s (value_ext_id a) y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_sdiv s x y) }}
      else h

    | rule_div_sub_urem z b a s x y =>
      if $$ h |- b =r1 (rhs_ext_bop bop_urem s x y) $$ &&
         $$ h |- a =r1 (rhs_ext_bop bop_sub s x (value_ext_id b)) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_udiv s (value_ext_id a) y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_udiv s x y) }}
      else h

    | rule_div_zext z x y k s1 s2 a b =>
      if $$ h |- x =r2 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- y =r2 (rhs_ext_ext extop_z (typ_int s1) b (typ_int s2)) $$ &&
         $$ h |- k =r2 (rhs_ext_bop bop_udiv s1 a b) $$ &&
         $$ h |- z =r2 (rhs_ext_ext extop_z (typ_int s1) (value_ext_id k) (typ_int s2)) $$
      then {{ h +++ z =r2 (rhs_ext_bop bop_udiv s2 (value_ext_id x) (value_ext_id y)) }}
      else h

    | rule_div_mone z s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_sdiv s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) }}
      else h

    | rule_rem_zext z x y k s1 s2 a b =>
      if $$ h |- x =r2 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- y =r2 (rhs_ext_ext extop_z (typ_int s1) b (typ_int s2)) $$ &&
         $$ h |- k =r2 (rhs_ext_bop bop_urem s1 a b) $$ &&
         $$ h |- z =r2 (rhs_ext_ext extop_z (typ_int s1) (value_ext_id k) (typ_int s2)) $$
      then {{ h +++ z =r2 (rhs_ext_bop bop_urem s2 (value_ext_id x) (value_ext_id y)) }}
      else h

    | rule_rem_neg z my s x y =>
      if $$ h |- my =r1 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_srem s x (value_ext_id my)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_srem s x y) }}
      else h

    | rule_rem_neg2 z s x c1 c2 =>
      if $$ h |- z =r1 (rhs_ext_bop bop_srem s x (value_ext_const (const_int s c1))) $$ &&
        cond_minus s (INTEGER.of_Z (Size.to_Z s) 0%Z true) c1 c2
      then {{ h +++ z =r1 (rhs_ext_bop bop_srem s x (value_ext_const (const_int s c2))) }}
      else h

    | rule_select_trunc z x y z' s1 s2 a b c =>
      if $$ h |- x =r2 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- y =r2 (rhs_ext_trunc truncop_int (typ_int s1) b (typ_int s2)) $$ &&
         $$ h |- z' =r2 (rhs_ext_select c (typ_int s1) a b) $$ &&
         $$ h |- z =r2 (rhs_ext_trunc truncop_int (typ_int s1) (value_ext_id z') (typ_int s2)) $$
      then {{ h +++ z =r2 (rhs_ext_select c (typ_int s2) (value_ext_id x) (value_ext_id y)) }}
      else h

    | rule_select_add z x y z' s1 a b c cond =>
      if $$ h |- x =r2 (rhs_ext_bop bop_add s1 a b) $$ &&
         $$ h |- y =r2 (rhs_ext_bop bop_add s1 a c) $$ &&
         $$ h |- z' =r2 (rhs_ext_select cond (typ_int s1) b c) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_add s1 a (value_ext_id z')) $$
      then {{ h +++ z =r2 (rhs_ext_select cond (typ_int s1) (value_ext_id x) (value_ext_id y)) }}
      else h

    | rule_select_const_gt z b s x c1 c2 =>
      let md := hint_maydiff h in
      let inv := hint_invariant h in
      let eqs_orig := invariant_original inv in
      let eqs_opt := invariant_optimized inv in
      if cond_same_value (hint_maydiff h) x &&
         $$ h |- b =r1 (rhs_ext_icmp cond_sgt (typ_int s) x (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r1 (rhs_ext_select (value_ext_id b) (typ_int s) x (value_ext_const (const_int s c2))) $$ &&
         $$ h |- b =r2 (rhs_ext_icmp cond_slt (typ_int s) x (value_ext_const (const_int s c2))) $$ &&
         $$ h |- z =r2 (rhs_ext_select (value_ext_id b) (typ_int s) (value_ext_const (const_int s c2)) x) $$ &&
         cond_plus s c1 (INTEGER.of_Z (Size.to_Z s) 1%Z true) c2
      then {{h --- z}}
      else h

    | rule_or_xor z y s a b =>
      let md := hint_maydiff h in
      let inv := hint_invariant h in
      let eqs_orig := invariant_original inv in
      let eqs_opt := invariant_optimized inv in
      if $$ h |- y =r1 (rhs_ext_bop bop_xor s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_or s a (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_or s a b) }}
      else h

    | rule_or_commutative z s x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_or s y x) }}
      else h

    | rule_trunc_onebit z k s y =>
      if $$ h |- k =r2 (rhs_ext_bop bop_and s y (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true)))) $$ &&
         $$ h |- z =r2 (rhs_ext_icmp cond_ne (typ_int s) (value_ext_id k) (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r2 (rhs_ext_trunc truncop_int (typ_int s) y (typ_int Size.One)) }}
      else h

    | rule_cmp_onebit z x y =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_ne (typ_int Size.One) x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_xor Size.One x y) }}
      else h

    | rule_cmp_eq z y a b =>
      if $$ h |- z =r2 (rhs_ext_bop bop_xor Size.One (value_ext_id y) (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
         $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a b) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_eq (typ_int Size.One) a b) }}
      else h

    | rule_cmp_ult z y a b =>
      if $$ h |- z =r2 (rhs_ext_bop bop_and Size.One (value_ext_id y) b) $$ &&
         $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_ult (typ_int Size.One) a b) }}
      else h

    | rule_shift_undef z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_shl s (value_ext_const (const_undef (typ_int s))) a) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
      else h

    | rule_and_same z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s a a) $$
      then {{ h +++ z =r1 (rhs_ext_value a) }}
      else h

    | rule_and_zero z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
      else h

    | rule_and_mone z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value a) }}
      else h

    | rule_inbound_remove x y pt pa t a idx u v =>
      if $$ h |- x =r1 (rhs_ext_gep true t a idx u) $$ &&
         $$ h |- (value_ext_id x,pt,pa) =h1 v $$ &&
         $$ h |- y =r1 (rhs_ext_gep false t a idx u) $$
      then {{ h +++ x =r1 (rhs_ext_value (value_ext_id y)) }}
      else h

    | rule_inbound_remove2 x y pt pa t a idx u v =>
      if $$ h |- x =r1 (rhs_ext_gep false t a idx u) $$ &&
         $$ h |- (value_ext_id x,pt,pa) =h1 v $$ &&
         $$ h |- y =r1 (rhs_ext_gep true t a idx u) $$
      then {{ h +++ x =r1 (rhs_ext_value (value_ext_id y)) }}
      else h

    | rule_add_mask z y y' s x c1 c2 =>
      if $$ h |- y =r2 (rhs_ext_bop bop_and s x (value_ext_const (const_int s c2))) $$ &&
         $$ h |- y' =r2 (rhs_ext_bop bop_add s x (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_and s (value_ext_id y') (value_ext_const (const_int s c2))) $$ &&
         cond_mask_up s c1 c2
      then {{ h +++ z =r2 (rhs_ext_bop bop_add s (value_ext_id y) (value_ext_const (const_int s c1))) }}
      else h

    | rule_neq_generate_gm x y =>
      if $$ h |- y =r1 rhs_ext_old_alloca $$ &&
         cond_is_global x m1
      then {{h +++ y ~=r1 (inr x)}}
      else h

    | rule_and_undef z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s a (value_ext_const (const_undef (typ_int s)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
      else h

    | rule_and_not z y s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s x (value_ext_id y)) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
      else h

    | rule_and_commutative z s x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_and s y x) }}
      else h

    | rule_and_or z y s x a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_and s (value_ext_id y) x) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_or s x a) $$
      then {{ h +++ z =r1 (rhs_ext_value x) }}
      else h

    | rule_and_demorgan z x y z' s a b =>
      if $$ h |- x =r2 (rhs_ext_bop bop_xor s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
         $$ h |- y =r2 (rhs_ext_bop bop_xor s b (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
         $$ h |- z' =r2 (rhs_ext_bop bop_or s a b) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_xor s (value_ext_id z') (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r2 (rhs_ext_bop bop_and s (value_ext_id x) (value_ext_id y)) }}
      else h

    | rule_and_not_or z x y s a b =>
      if $$ h |- x =r1 (rhs_ext_bop bop_xor s b (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_or s (value_ext_id x) a) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_and s (value_ext_id y) b) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_and s a b) }}
      else h

    | rule_or_undef z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s a (value_ext_const (const_undef (typ_int s)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
      else h

    | rule_or_same z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s a a) $$
      then {{ h +++ z =r1 (rhs_ext_value a) }}
      else h

    | rule_or_zero z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value a) }}
      else h

    | rule_or_mone z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
      else h

    | rule_or_not z y s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s x (value_ext_id y)) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
      else h

    | rule_or_and z y s x a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_or s (value_ext_id y) x) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_and s x a) $$
      then {{ h +++ z =r1 (rhs_ext_value x) }}
      else h

    | rule_xor_zero z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_xor s a (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value a) }}
      else h

    | rule_xor_same z s a =>
      if $$ h |- z =r1 (rhs_ext_bop bop_xor s a a) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
      else h

    | rule_xor_commutative z s x y =>
      if $$ h |- z =r1 (rhs_ext_bop bop_xor s x y) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_xor s y x) }}
      else h

    | rule_xor_not z y s x =>
      if $$ h |- z =r1 (rhs_ext_bop bop_xor s x (value_ext_id y)) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_xor s x (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) }}
      else h

    | rule_zext_trunc_and z y x a s1 s2 c =>
      if $$ h |- x =r1 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s2)) $$  &&
        $$ h |- y =r1 (rhs_ext_bop bop_and s2 (value_ext_id x) (value_ext_const (const_int s2 c))) $$ &&
        $$ h |- z =r1 (rhs_ext_ext extop_z (typ_int s2) (value_ext_id y) (typ_int s1)) $$
      then {{ h +++ z =r1 (rhs_ext_bop bop_and s1 a (value_ext_const (const_int s1 (INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z c) true)))) }}
      else h

    | rule_zext_trunc_and_xor z y x w w' a s1 s2 c =>
      if $$ h |- x =r2 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s2)) $$  &&
        $$ h |- y =r2 (rhs_ext_bop bop_and s2 (value_ext_id x) (value_ext_const (const_int s2 c))) $$ &&
        $$ h |- w =r2 (rhs_ext_bop bop_xor s2 (value_ext_id y) (value_ext_const (const_int s2 c))) $$ &&
        $$ h |- w' =r2 (rhs_ext_bop bop_and s1 a (value_ext_const (const_int s1 (INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z c) true)))) $$ &&
        $$ h |- z =r2 (rhs_ext_bop bop_xor s1 (value_ext_id w') (value_ext_const (const_int s1 (INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z c) true)))) $$
      then {{ h +++ z =r2 (rhs_ext_ext extop_z (typ_int s2) (value_ext_id w) (typ_int s1)) }}
      else h

    | rule_zext_xor z y y' a s =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$  &&
        $$ h |- y' =r2 (rhs_ext_ext extop_z (typ_int Size.One) a (typ_int s)) $$ &&
        $$ h |- z =r2 (rhs_ext_bop bop_xor s (value_ext_id y') (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) (1)%Z true)))) $$
      then {{ h +++ z =r2 (rhs_ext_ext extop_z (typ_int Size.One) (value_ext_id y) (typ_int s)) }}
      else h

    | rule_sext_trunc z y y' a s1 s2 n =>
      if $$ h |- y =r2 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s2)) $$ &&
        $$ h |- y' =r2 (rhs_ext_bop bop_shl s1 a (value_ext_const (const_int s1 (INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z n) true)))) $$ &&
        $$ h |- z =r2 (rhs_ext_bop bop_ashr s1 (value_ext_id y') (value_ext_const (const_int s1 (INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z n) true)))) $$ &&
        cond_szplus s2 n s1
      then {{ h +++ z =r2 (rhs_ext_ext extop_s (typ_int s2) (value_ext_id y) (typ_int s1)) }}
      else h

    | rule_trunc_trunc z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s3)) $$
      then {{ h +++ z =r1 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_trunc_zext1 z y a s1 s2 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s1)) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_bitcast (typ_int s1) a (typ_int s1)) }}
      else h

    | rule_trunc_zext2 z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s3)) $$ &&
         cond_szlt s1 s3
      then {{ h +++ z =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_trunc_zext3 z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s3)) $$ &&
         cond_szlt s3 s1
      then {{ h +++ z =r1 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_trunc_sext1 z y a s1 s2 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s1)) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_bitcast (typ_int s1) a (typ_int s1)) }}
      else h

    | rule_trunc_sext2 z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s3)) $$ &&
         cond_szlt s1 s3
      then {{ h +++ z =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_trunc_sext3 z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_int (typ_int s2) (value_ext_id y) (typ_int s3)) $$ &&
         cond_szlt s3 s1
      then {{ h +++ z =r1 (rhs_ext_trunc truncop_int (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_zext_zext z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_ext extop_z (typ_int s2) (value_ext_id y) (typ_int s3)) $$
      then {{ h +++ z =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_sext_zext z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_ext extop_s (typ_int s2) (value_ext_id y) (typ_int s3)) $$
      then {{ h +++ z =r1 (rhs_ext_ext extop_z (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_sext_sext z y a s1 s2 s3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s2)) $$ &&
         $$ h |- z =r1 (rhs_ext_ext extop_s (typ_int s2) (value_ext_id y) (typ_int s3)) $$
      then {{ h +++ z =r1 (rhs_ext_ext extop_s (typ_int s1) a (typ_int s3)) }}
      else h

    | rule_fptoui_fpext z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_fp t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_cast castop_fptoui t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_fptoui t1 a t3) }}
      else h

    | rule_fptosi_fpext z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_fp t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_cast castop_fptosi t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_fptosi t1 a t3) }}
      else h

    | rule_uitofp_zext z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_z t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_cast castop_uitofp t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_uitofp t1 a t3) }}
      else h

    | rule_sitofp_sext z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_s t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_cast castop_sitofp t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_sitofp t1 a t3) }}
      else h

    | rule_fptrunc_fptrunc z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_trunc truncop_fp t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_fp t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_trunc truncop_fp t1 a t3) }}
      else h

    | rule_fptrunc_fpext z y a t1 t2 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_fp t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_trunc truncop_fp t2 (value_ext_id y) t1) $$
      then {{ h +++ z =r1 (rhs_ext_cast castop_bitcast t1 a t1) }}
      else h

    | rule_fpext_fpext z y a t1 t2 t3 =>
      if $$ h |- y =r1 (rhs_ext_ext extop_fp t1 a t2) $$ &&
         $$ h |- z =r1 (rhs_ext_ext extop_fp t2 (value_ext_id y) t3) $$
      then {{ h +++ z =r1 (rhs_ext_ext extop_fp t1 a t3) }}
      else h

    | rule_cmp_swap_ult z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_ult t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ugt t b a) }}
      else h

    | rule_cmp_swap_ugt z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_ugt t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ult t b a) }}
      else h

    | rule_cmp_swap_ule z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_ule t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_uge t b a) }}
      else h

    | rule_cmp_swap_uge z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_uge t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ule t b a) }}
      else h

    | rule_cmp_swap_slt z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_slt t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_sgt t b a) }}
      else h

    | rule_cmp_swap_sgt z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_sgt t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_slt t b a) }}
      else h

    | rule_cmp_swap_sle z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_sle t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_sge t b a) }}
      else h

    | rule_cmp_swap_sge z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_sge t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_sle t b a) }}
      else h

    | rule_cmp_swap_eq z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_eq t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_eq t b a) }}
      else h

    | rule_cmp_swap_ne z a b t =>
      if $$ h |- z =r1 (rhs_ext_icmp cond_ne t a b) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ne t b a) }}
      else h

    | rule_cmp_slt_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One b (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
        $$ h |- z =r2 (rhs_ext_bop bop_and Size.One (value_ext_id y) a) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_slt (typ_int Size.One) a b) }}
      else h

    | rule_cmp_sgt_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
        $$ h |- z =r2 (rhs_ext_bop bop_and Size.One (value_ext_id y) b) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_sgt (typ_int Size.One) a b) }}
      else h

    | rule_cmp_ugt_onebit z y a b =>
      if $$ h |- z =r2 (rhs_ext_bop bop_and Size.One (value_ext_id y) a) $$ &&
         $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One b (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_ugt (typ_int Size.One) a b) }}
      else h

    | rule_cmp_ule_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_or Size.One (value_ext_id y) b) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_ule (typ_int Size.One) a b) }}
      else h

    | rule_cmp_uge_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One b (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_or Size.One (value_ext_id y) a) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_uge (typ_int Size.One) a b) }}
      else h

    | rule_cmp_sle_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One b (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_or Size.One (value_ext_id y) a) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_sle (typ_int Size.One) a b) }}
      else h

    | rule_cmp_sge_onebit z y a b =>
      if $$ h |- y =r2 (rhs_ext_bop bop_xor Size.One a (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_or Size.One (value_ext_id y) b) $$
      then {{ h +++ z =r2 (rhs_ext_icmp cond_sge (typ_int Size.One) a b) }}
      else h

    | rule_cmp_eq_sub z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_sub s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_eq (typ_int s) (value_ext_id y) (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_eq (typ_int s) a b) }}
      else h

    | rule_cmp_ne_sub z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_sub s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_ne (typ_int s) (value_ext_id y) (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ne (typ_int s) a b) }}
      else h

    | rule_cmp_eq_srem z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_srem s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_eq (typ_int s) (value_ext_id y) b) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (0)%Z true)))) }}
      else h

    | rule_cmp_eq_srem2 z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_srem s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_eq (typ_int s) b (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (0)%Z true)))) }}
      else h

    | rule_cmp_ne_srem z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_srem s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_ne (typ_int s) (value_ext_id y) b) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) }}
      else h

    | rule_cmp_ne_srem2 z y s a b =>
      if $$ h |- y =r1 (rhs_ext_bop bop_srem s a b) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_ne (typ_int s) b (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_value (value_ext_const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true)))) }}
      else h

    | rule_cmp_eq_xor z x y s a b c =>
      if $$ h |- x =r1 (rhs_ext_bop bop_xor s a c) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_xor s b c) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_eq (typ_int s) (value_ext_id x) (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_eq (typ_int s) a b) }}
      else h

    | rule_cmp_ne_xor z x y s a b c =>
      if $$ h |- x =r1 (rhs_ext_bop bop_xor s a c) $$ &&
         $$ h |- y =r1 (rhs_ext_bop bop_xor s b c) $$ &&
         $$ h |- z =r1 (rhs_ext_icmp cond_ne (typ_int s) (value_ext_id x) (value_ext_id y)) $$
      then {{ h +++ z =r1 (rhs_ext_icmp cond_ne (typ_int s) a b) }}
      else h

    | rule_add_dist_unary z minusx minusy w s x y =>
      if $$ h |- minusx =r2 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) x) $$ &&
         $$ h |- minusy =r2 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
         $$ h |- w =r2 (rhs_ext_bop bop_add s x y) $$ &&
         $$ h |- z =r2 (rhs_ext_bop bop_sub s (value_ext_const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) w) $$
      then {{ h +++ z =r2 (rhs_ext_bop bop_add s minusx minusy)}}
      else h

  end.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
