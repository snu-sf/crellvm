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
Require Import String.
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

Definition get_bitsize (ty:typ) (m:module) : option sz :=
  match ty with
  | typ_int sz1 => Some sz1
  | typ_pointer _ =>
    (match m with
     | module_intro ls _ _ =>
       match (List.find 
          (fun h => match h with| layout_ptr _ _ _ => true | _ => false end) ls) with
       | None => None
       | Some (layout_ptr sz _ _) => Some sz
       | Some _ => None
       end
     end)
  | _ => None 
  end.

Definition cond_uint_fitinsize (s:sz) (c:INTEGER.t) : bool :=
  Z.leb 0%Z (INTEGER.to_Z c) && Z.ltb (INTEGER.to_Z c) (Zpos (power_sz s)).

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

Definition cond_mul (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec _)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
    (Int.mul (Size.to_nat s - 1)
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Definition cond_or (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec _)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
    (Int.or (Size.to_nat s - 1)
            (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
            (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Definition cond_le (s:sz) (c1 c2: INTEGER.t) : bool :=
  Z.leb (INTEGER.to_Z c1) (INTEGER.to_Z c2).

Definition cond_and (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec (Size.to_nat s - 1))
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
  (Int.and (Size.to_nat s - 1)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).
 
Definition cond_xor (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec (Size.to_nat s - 1))
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
  (Int.xor (Size.to_nat s - 1)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).
 
Definition cond_mask_up (s:sz) (c1i c2i:INTEGER.t) : bool :=
  let ws := (Size.to_nat s - 1)%nat in
  let c1 := (Int.repr ws (INTEGER.to_Z c1i)) in
  let mc1 := (Int.sub ws (Int.zero ws) c1) in
  let c2 := (Int.repr ws (INTEGER.to_Z c2i)) in
  let c1up := (Int.not ws (Int.sub ws (Int.and ws c1 mc1) (Int.one ws))) in
    (Int.eq_dec ws) (Int.and ws c1up c2) c1up.

(* cond_double_to_i64 : is (bitcast double d to i64 == i)? *)
Definition cond_double_to_i64 (d:const) (i:INTEGER.t) : bool :=
  match d with
  | const_floatpoint fpty f =>
    match fpty with
    | fp_double =>
      true (* XXX : This should be fixed.. *)
    | _ => false
    end
  | _ => false
  end.

Definition cond_signbit (s:sz) (v:ValueT.t) : bool :=
  match signbit_of s, v with
  | None, _ => false
  | Some n, ValueT.const (const_int s' n') =>
    sz_dec s s' && INTEGER.dec n n'
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
  | Expr.value vl =>
    match (vl, v') with
    | (ValueT.const e, ValueT.const v') =>
      match e with
      | const_gep inbound v idxlist =>
        const_eqb v v' &&
        (List.forallb 
          (fun idx => 
            match idx with 
            | (const_int sz_i i) => 
              INTEGER.dec i (INTEGER.of_Z (Size.to_Z sz_i) 0%Z true)
            | _ => false
            end)
          idxlist)
      | _ => false
      end
    | _ => false
    end
  | _ => false
  end.

Definition cond_bitcast_ptr (v':ValueT.t) (e:Expr.t) : bool :=
  match e with
  | Expr.cast eop fromty v toty =>
    (match eop with 
    | castop_bitcast => 
      (match fromty, toty with
      | typ_pointer _, typ_pointer _ => ValueT.eq_dec v v'
      | _, _ => false
      end)
    | _ => false
    end)
  | Expr.value vt =>
    match (vt, v') with
    | (ValueT.const e, ValueT.const v') =>
      match e with
      | const_castop eop v toty =>
        (match eop with 
        | castop_bitcast =>
          (match toty with
          | typ_pointer _ => const_eqb v v'
          | _ => false
          end)
        | _ => false
        end)
      | _ => false
      end
    | _ => false
    end
  | _ => false
  end.

Definition cond_pointertyp (t:typ) : bool :=
  match t with
  | typ_pointer _ => true
  | _ => false
  end.

Definition cond_same_bitsize (ty1:typ) (ty2:typ) (m_src:module) : bool :=
  match (ty1, ty2) with
  | (typ_int sz1, typ_int sz2) => sz_dec sz1 sz2
  | (typ_int sz1, typ_pointer _) => 
    sz_dec sz1 
      (match m_src with
       | module_intro ls _ _ =>
         match (List.find 
            (fun h => match h with| layout_ptr _ _ _ => true | _ => false end) ls) with
         | None => Size.from_Z 0%Z
         | Some (layout_ptr sz _ _) => sz
         | Some _ => Size.from_Z 0%Z
         end
       end)
  | _ => false
  end.

(* NOTE : pointer type in Vellvm does not remember address space *)
Definition cond_sameaddrspace (t1:typ) (t2:typ) : bool :=
  match (t1,t2) with
  | (typ_pointer _, typ_pointer _) => true
  | _ => false
  end.

(* NOTE : Vellvm does not support vector type *)
Definition cond_vectortyp (t:typ) : bool :=
  false.

Definition cond_inttyp (t:typ): bool :=
  match t with
  | typ_int _ => true
  | _ => false
  end.

Definition cond_floatpointtyp (t:typ) : bool :=
  match t with
  | typ_floatpoint _ => true
  | _ => false
  end.

Definition cond_onebit (s:sz) : bool :=
  sz_dec s (Size.One).

Definition cond_neg (s:sz) (c1 c2:INTEGER.t) : bool :=
  cond_plus s c1 c2 (INTEGER.of_Z (Size.to_Z s) (-1)%Z true).

Definition const_newint (s:sz) (i:INTEGER.t) : const := 
  (const_int s (INTEGER.of_Z (Size.to_Z s) (INTEGER.to_Z i) true)).

Definition const_mone (s:sz) : const := 
  (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)).

Definition const_zero (s:sz) : const := 
  (const_int s (INTEGER.of_Z (Size.to_Z s) (0)%Z true)).

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

(* getSwappedPredicate in lib/IR/Instructions.cpp *)
Definition get_swapped_icmp_cond (c:cond) : cond :=
  match c with
    | cond_eq => cond_eq
    | cond_ne => cond_ne
    | cond_ugt => cond_ult
    | cond_uge => cond_ule
    | cond_ult => cond_ugt
    | cond_ule => cond_uge
    | cond_sgt => cond_slt
    | cond_sge => cond_sle
    | cond_slt => cond_sgt
    | cond_sle => cond_sge
  end.

Definition get_swapped_fcmp_cond (c:fcond) : fcond :=
  match c with
  | fcond_false => fcond_false
  | fcond_oeq => fcond_oeq
  | fcond_ogt => fcond_olt
  | fcond_oge => fcond_ole
  | fcond_olt => fcond_ogt
  | fcond_ole => fcond_oge
  | fcond_one => fcond_one
  | fcond_ord => fcond_ord
  | fcond_ueq => fcond_ueq
  | fcond_ugt => fcond_ult
  | fcond_uge => fcond_ule
  | fcond_ult => fcond_ugt
  | fcond_ule => fcond_uge
  | fcond_une => fcond_une
  | fcond_uno => fcond_uno
  | fcond_true => fcond_true
  end.

Definition is_commutative_bop (opcode:bop) :=
  match opcode with
  | bop_add | bop_mul | bop_and | bop_or | bop_xor => true
  | _ => false
  end.

Definition is_commutative_fbop (opcode:fbop) :=
  match opcode with
  | fbop_fadd | fbop_fmul => true
  | _ => false
  end.

Definition load_realign (e1: Expr.t): Expr.t :=
  match e1 with
  | Expr.load v ty a => Expr.load v ty Align.One
  | _ => e1
  end
.

Notation "$$ inv |-src y >= rhs $$" := (Assertion.lessdef_expr (y, rhs) inv.(Assertion.src).(Assertion.lessdef)) (at level 41, inv, y, rhs at level 41).
Notation "$$ inv |-tgt y >= rhs $$" := (Assertion.lessdef_expr (y, rhs) inv.(Assertion.tgt).(Assertion.lessdef)) (at level 41, inv, y, rhs at level 41).
Notation "$$ inv |-src y 'unique' $$" :=
  ((Tag.eq_dec (fst y) Tag.physical) &&
   (AtomSetImpl.mem (snd y) inv.(Assertion.src).(Assertion.unique))) (at level 41, inv, y at level 41).
Notation "$$ inv |-tgt y 'unique' $$" :=
  ((Tag.eq_dec (fst y) Tag.physical) &&
   (AtomSetImpl.mem (snd y) inv.(Assertion.tgt).(Assertion.unique))) (at level 41, inv, y at level 41).
Notation "$$ inv |-src x _|_ y $$" := ((PtrPairSet.mem (x, y) inv.(Assertion.src).(Assertion.alias).(Assertion.noalias)) || (PtrPairSet.mem (y, x) inv.(Assertion.src).(Assertion.alias).(Assertion.noalias))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-tgt x _|_ y $$" := ((PtrPairSet.mem (x, y) inv.(Assertion.tgt).(Assertion.alias).(Assertion.noalias)) || (PtrPairSet.mem (y, x) inv.(Assertion.tgt).(Assertion.alias).(Assertion.noalias))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-src x _||_ y $$" := ((ValueTPairSet.mem (x, y) inv.(Assertion.src).(Assertion.alias).(Assertion.diffblock)) || (ValueTPairSet.mem (y, x) inv.(Assertion.src).(Assertion.alias).(Assertion.diffblock))) (at level 41, inv, x, y at level 41).
Notation "$$ inv |-tgt x _||_ y $$" := ((ValueTPairSet.mem (x, y) inv.(Assertion.tgt).(Assertion.alias).(Assertion.diffblock)) || (ValueTPairSet.mem (y, x) inv.(Assertion.tgt).(Assertion.alias).(Assertion.diffblock))) (at level 41, inv, x, y at level 41).
Notation "{{ inv +++src y >= rhs }}" := (Assertion.update_src (Assertion.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41, inv, y, rhs at level 41).
Notation "{{ inv +++tgt y >= rhs }}" := (Assertion.update_tgt (Assertion.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41, inv, y, rhs at level 41).
Notation "{{ inv +++src y _|_ x }}" := (Assertion.update_src (Assertion.update_noalias (PtrPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++tgt y _|_ x }}" := (Assertion.update_tgt (Assertion.update_noalias (PtrPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++src y _||_ x }}" := (Assertion.update_src (Assertion.update_diffblock (ValueTPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv +++tgt y _||_ x }}" := (Assertion.update_tgt (Assertion.update_diffblock (ValueTPairSet.add (y, x))) inv) (at level 41, inv, y, x at level 41).
Notation "{{ inv --- x }}" := (Assertion.update_maydiff (IdTSet.filter (fun y => negb (IdT.eq_dec x y))) inv) (at level 41, inv, x at level 41).


Definition load_align_one (e1: Expr.t): Expr.t :=
  match e1 with
  | Expr.load v ty a => Expr.load v ty Align.One
  | _ => e1
  end
.

Definition reduce_maydiff_preserved (used_ids: list IdT.t) :=
  (fun idt => (Tag.eq_dec (fst idt) Tag.physical) || (List.find (IdT.eq_dec idt) used_ids)).

(* Non-physical that is only in maydiff is safe to remove *)
Definition reduce_maydiff_non_physical (inv0: Assertion.t): Assertion.t :=
  let used_ids := (Assertion.get_idTs_unary inv0.(Assertion.src))
                    ++ (Assertion.get_idTs_unary inv0.(Assertion.tgt))
  in
  Assertion.update_maydiff (IdTSet.filter (reduce_maydiff_preserved used_ids)) inv0.

Definition reduce_maydiff_lessdef (inv0:Assertion.t): Assertion.t :=
    let lessdef_src := inv0.(Assertion.src).(Assertion.lessdef) in
    let lessdef_tgt := inv0.(Assertion.tgt).(Assertion.lessdef) in
  Assertion.update_maydiff
    (IdTSet.filter
       (fun id =>
          negb (ExprPairSet.exists_
                  (fun p => ExprPairSet.exists_
                           (fun q => Assertion.inject_expr inv0 (snd p) (fst q))
                           (Assertion.get_lhs lessdef_tgt (fst p)))
                  (Assertion.get_rhs lessdef_src
                                     (Expr.value (ValueT.id id)))))) inv0.

(* Definition reduce_maydiff_old_fun (inv0:Assertion.t): Assertion.t := *)
(*   let inv1 := reduce_maydiff_non_physical_old inv0 in *)
(*   reduce_maydiff_lessdef_old inv1. *)

Definition apply_infrule
           (m_src m_tgt:module)
           (infrule:Infrule.t)
           (inv0:Assertion.t): Assertion.t :=
  let apply_fail := (fun _: unit => (debug_print2 infrule_printer infrule
                                                  (debug_string "Infrule application failed!" inv0))) in
  let no_match_fail := (fun _: unit => debug_string "Infrule match failed!"
                                                    (debug_print2 infrule_printer infrule inv0)) in
  match infrule with
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
  | Infrule.add_onebit z x y =>
    if $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add Size.One x y) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_xor Size.One x y)}}
    else apply_fail tt
  | Infrule.add_sub z minusy x y s =>
    if $$ inv0 |-src (Expr.value minusy) >= (Expr.bop bop_sub s (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)) y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_add s x minusy) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.bop bop_sub s x y)}}
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
  | Infrule.add_or_and z a b x y s =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.bop bop_or s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_and s a b) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s (ValueT.id x) (ValueT.id y)) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_add s a b)}}
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
  | Infrule.add_zext_bool x y b c c' sz =>
    if $$ inv0 |-src (Expr.value (ValueT.id x)) >= (Expr.ext extop_z (typ_int Size.One) b (typ_int sz)) $$ &&
       $$ inv0 |-src (Expr.value (ValueT.id y)) >= (Expr.bop bop_add sz (ValueT.id x) (ValueT.const (const_int sz c))) $$ &&
       cond_plus sz c (INTEGER.of_Z (Size.to_Z sz) 1%Z true) c'
    then {{ inv0 +++src (Expr.value (ValueT.id y)) >= (Expr.select b (typ_int sz) (ValueT.const (const_int sz c')) (ValueT.const (const_int sz c))) }}
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
  | Infrule.and_or_const2 z y y' x c1 c2 c3 s =>
    if $$ inv0 |-tgt (Expr.bop bop_or s x (const_int s c1)) >= (Expr.value (ValueT.id y')) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x (const_int s c3)) >= (Expr.value (ValueT.id y)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s y (const_int s c1)) >= (Expr.value (ValueT.id z)) $$ &&
       cond_xor s c1 c2 c3 && cond_and s c1 c2 c1
    then {{inv0 +++tgt (Expr.bop bop_and s y' (const_int s c2)) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.and_same z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x x) $$
    then {{inv0 +++src (Expr.value z) >= (Expr.value x)}}
    else apply_fail tt
  | Infrule.and_true_bool x y =>
    let true_expr := Expr.value (ValueT.const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true))) in
    if $$ inv0 |-src true_expr >= (Expr.bop bop_and Size.One x y) $$
    then {{
             {{
                 {{
                     {{inv0 +++src true_expr >= (Expr.value x)}}
                       +++src (Expr.value x) >= true_expr
                 }}
                   +++src true_expr >= (Expr.value y)
             }}
               +++src (Expr.value y) >= true_expr
         }}
    else apply_fail tt
  | Infrule.and_true_bool_tgt x y =>
    let true_expr := Expr.value (ValueT.const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) (-1)%Z true))) in
    if $$ inv0 |-tgt true_expr >= (Expr.bop bop_and Size.One x y) $$
    then {{
             {{
                 {{
                     {{inv0 +++tgt true_expr >= (Expr.value x)}}
                       +++tgt (Expr.value x) >= true_expr
                 }}
                   +++tgt true_expr >= (Expr.value y)
             }}
               +++tgt (Expr.value y) >= true_expr
         }}
    else apply_fail tt
  | Infrule.and_undef z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_undef (typ_int s)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value
              (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (0)%Z true)))) }}
    else apply_fail tt
  | Infrule.and_xor_const z y y' x c1 c2 c3 s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s x (const_int s c1)) >= (Expr.value (ValueT.id y')) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x (const_int s c2)) >= (Expr.value (ValueT.id y)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s y (const_int s c3)) >= (Expr.value (ValueT.id z)) $$ &&
       cond_and s c1 c2 c3
    then {{inv0 +++tgt (Expr.bop bop_and s y' (const_int s c2)) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.and_zero z x s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true)))) }}
    else apply_fail tt
  | Infrule.and_or_not1 z x y a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s b (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s (ValueT.id x) a) >= (Expr.value (ValueT.id y)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s a b) >= (Expr.value (ValueT.id z)) $$
    then {{ inv0 +++tgt (Expr.bop bop_and s y b) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.bitcast_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_bitcast_rev_tgt src mid dst srcty midty dstty =>
    if $$ inv0 |-tgt (Expr.cast castop_bitcast srcty src midty) >= (Expr.value mid) $$ &&
       $$ inv0 |-tgt (Expr.cast castop_bitcast midty mid dstty) >= (Expr.value dst) $$
    then {{ inv0 +++tgt (Expr.cast castop_bitcast srcty src dstty) >= (Expr.value dst) }}
    else apply_fail tt
  | Infrule.bitcast_double_i64 src tgt =>
    let s := Size.from_Z 64%Z in
    if cond_double_to_i64 src tgt
    then {{ inv0 +++tgt (Expr.cast castop_bitcast 
        (typ_floatpoint fp_double)
        (ValueT.const src)
        (typ_int s))
        >=
        (Expr.value (ValueT.const (const_int s tgt))) }}
    else apply_fail tt
  | Infrule.bitcast_load ptr ty v1 ty2 v2 a =>
    if $$ inv0 |-src (Expr.load ptr ty a) >= (Expr.value v1) $$ &&
       $$ inv0 |-src (Expr.cast castop_bitcast ty v1 ty2) >= (Expr.value v2) $$
    then {{inv0 +++src (Expr.load ptr ty2 a) >= (Expr.value v2)}}
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
  | Infrule.bitcastptr v' bitcastinst =>
    if cond_bitcast_ptr v' bitcastinst
    then 
      let inv0 := {{inv0 +++src bitcastinst >= (Expr.value v')}} in
      {{inv0 +++src (Expr.value v') >= bitcastinst}}
    else apply_fail tt
  | Infrule.bitcast_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       cond_floatpointtyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_fptosi src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_fptosi srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb (cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptosi srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_fptoui src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_fptoui srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb (cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptoui srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_fptrunc src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.trunc truncop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       cond_floatpointtyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_ptrtoint src mid dst srcty midty dstty => 
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_ptrtoint srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb(cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_ptrtoint srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_sext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_s srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb(cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_s srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_sametype src dst tty =>
    if $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast tty src tty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.value src) }}
    else apply_fail tt
  | Infrule.bitcast_sitofp src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_sitofp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       cond_floatpointtyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_sitofp srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_trunc src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.trunc truncop_int srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb(cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_int srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_uitofp src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_uitofp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       cond_floatpointtyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_uitofp srcty src dstty) }}
    else apply_fail tt
  | Infrule.bitcast_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_bitcast midty mid dstty) $$ &&
       negb(cond_vectortyp srcty) && cond_inttyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_z srcty src dstty) }}
    else apply_fail tt
  | Infrule.bop_associative x y z opcode c1 c2 c3 s =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.bop opcode s x (const_int s c1)) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.bop opcode s y (const_int s c2)) $$
    then
      (* There are 5 cases (see Instruction::isAssociative(unsigned).) *)
      let cond_func_result := 
        match opcode with 
          | bop_and => cond_and s c1 c2 c3
          | bop_or => cond_or s c1 c2 c3
          | bop_xor => cond_xor s c1 c2 c3
          | bop_add => cond_plus s c1 c2 c3
          | bop_mul => cond_mul s c1 c2 c3
          | _ => false (* The bop is not associative.. *)
        end
      in
      if cond_func_result
      then 
        {{inv0 +++src (Expr.value z) >= (Expr.bop opcode s x (const_int s c3))}}
      else apply_fail tt
    else apply_fail tt
  | Infrule.bop_commutative e opcode x y s =>
    if $$ inv0 |-src e >= (Expr.bop opcode s x y) $$ &&
      (is_commutative_bop opcode)
    then {{ inv0 +++src e >= (Expr.bop opcode s y x) }}
    else apply_fail tt
  | Infrule.bop_commutative_rev e opcode x y s =>
    if $$ inv0 |-src (Expr.bop opcode s x y) >= e $$ &&
      (is_commutative_bop opcode)
    then {{ inv0 +++src (Expr.bop opcode s y x) >= e }}
    else apply_fail tt
  | Infrule.bop_commutative_tgt e opcode x y s =>
    if $$ inv0 |-tgt e >= (Expr.bop opcode s x y) $$ &&
      (is_commutative_bop opcode)
    then {{ inv0 +++tgt e >= (Expr.bop opcode s y x) }}
    else apply_fail tt
  | Infrule.bop_commutative_rev_tgt e opcode x y s =>
    if $$ inv0 |-tgt (Expr.bop opcode s x y) >= e $$ &&
      (is_commutative_bop opcode)
    then {{ inv0 +++tgt (Expr.bop opcode s y x) >= e }}
    else apply_fail tt
  | Infrule.fbop_commutative e opcode x y fty =>
    if $$ inv0 |-src e >= (Expr.fbop opcode fty x y) $$ &&
      (is_commutative_fbop opcode)
    then {{ inv0 +++src e >= (Expr.fbop opcode fty y x) }}
    else apply_fail tt
  | Infrule.fbop_commutative_rev e opcode x y fty =>
    if $$ inv0 |-src (Expr.fbop opcode fty x y) >= e $$ &&
      (is_commutative_fbop opcode)
    then {{ inv0 +++src (Expr.fbop opcode fty y x) >= e }}
    else apply_fail tt
  | Infrule.fbop_commutative_tgt e opcode x y fty =>
    if $$ inv0 |-tgt e >= (Expr.fbop opcode fty x y) $$ &&
      (is_commutative_fbop opcode)
    then {{ inv0 +++tgt e >= (Expr.fbop opcode fty y x) }}
    else apply_fail tt
  | Infrule.fbop_commutative_rev_tgt e opcode x y fty =>
    if $$ inv0 |-tgt (Expr.fbop opcode fty x y) >= e $$ &&
      (is_commutative_fbop opcode)
    then {{ inv0 +++tgt (Expr.fbop opcode fty y x) >= e }}
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
  | Infrule.fmul_commutative_tgt z x y fty =>
    if $$ inv0 |-tgt (Expr.fbop fbop_fmul fty x y) >= (Expr.value (ValueT.id z)) $$
    then {{ inv0 +++tgt (Expr.fbop fbop_fmul fty y x) >= (Expr.value (ValueT.id z)) }}
    else apply_fail tt
  | Infrule.fpext_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_fp midty mid dstty) $$ &&
       cond_floatpointtyp dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.fpext_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_fp midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.fptosi_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_fptosi midty mid dstty) $$ &&
       cond_floatpointtyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptosi srcty src dstty) }}
    else apply_fail tt
  | Infrule.fptoui_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_fptoui midty mid dstty) $$ &&
       cond_floatpointtyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_fptoui srcty src dstty) }}
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
  | Infrule.fptrunc_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_fp midty mid dstty) $$ &&
       cond_floatpointtyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_fp srcty src dstty) }}
    else apply_fail tt
  | Infrule.fptrunc_fpext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_fp srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_fp midty mid dstty) $$ &&
       typ_dec srcty dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
    else apply_fail tt
  | Infrule.gepzero v' gepinst =>
    if cond_gep_zero v' gepinst
    then 
      let inv0 := {{inv0 +++src gepinst >= (Expr.value v')}} in
      {{inv0 +++src (Expr.value v') >= gepinst}}
    else apply_fail tt
  | Infrule.gep_inbounds_remove gepinst =>
    match gepinst with
    | Expr.gep _ t v lsv u =>
      {{inv0 +++src (Expr.gep true t v lsv u) >= (Expr.gep false t v lsv u) }}
    | _ => apply_fail tt
    end
  | Infrule.gep_inbounds_remove_tgt gepinst =>
    match gepinst with
    | Expr.gep _ t v lsv u =>
      {{inv0 +++tgt (Expr.gep true t v lsv u) >= (Expr.gep false t v lsv u) }}
    | _ => apply_fail tt
    end
  | Infrule.gep_inbounds_add loadv ptr loadty al e =>
    match e with
    | Expr.gep _ t v lsv u =>
      if $$ inv0 |-src (Expr.value loadv) >= (Expr.load ptr loadty al) $$ &&
         $$ inv0 |-src (Expr.value ptr) >= (Expr.gep true t v lsv u) $$ &&
         $$ inv0 |-src (Expr.gep true t v lsv u) >= (Expr.value ptr) $$
      then
        {{ inv0 +++src (Expr.gep false t v lsv u) >= (Expr.gep true t v lsv u) }}
      else apply_fail tt
    | _ => apply_fail tt
    end
  | Infrule.inttoptr_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_inttoptr midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_inttoptr srcty src dstty) }} 
    else apply_fail tt
  | Infrule.inttoptr_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_inttoptr midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_inttoptr srcty src dstty) }}
    else apply_fail tt
  | Infrule.inttoptr_load ptr intty v1 ptrty v2 a =>
    if $$ inv0 |-src (Expr.load ptr intty a) >= (Expr.value v1) $$ &&
       $$ inv0 |-src (Expr.cast castop_inttoptr intty v1 ptrty) >= (Expr.value v2) $$ &&
       cond_same_bitsize intty ptrty m_src
    then {{ inv0 +++src (Expr.load ptr ptrty a) >= (Expr.value v2) }}
    else apply_fail tt
(* need to check that v's type is equal to ty and v do not invoke undefined behavior, but cannot  *)
  | Infrule.lessthan_undef ty v => 
    {{ inv0 +++src (Expr.value (ValueT.const (const_undef ty))) >= (Expr.value v) }}
  | Infrule.lessthan_undef_tgt ty v => 
    {{ inv0 +++tgt (Expr.value (ValueT.const (const_undef ty))) >= (Expr.value v) }}
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
  | Infrule.or_false x y sz =>
    let false_expr := Expr.value (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) in
    if $$ inv0 |-src false_expr >= (Expr.bop bop_or sz x y) $$
    then {{
             {{
                 {{
                     {{inv0 +++src false_expr >= (Expr.value x)}}
                       +++src (Expr.value x) >= false_expr
                 }}
                   +++src false_expr >= (Expr.value y)
             }}
               +++src (Expr.value y) >= false_expr
         }}
    else apply_fail tt
  | Infrule.or_false_tgt x y sz =>
    let false_expr := Expr.value (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 0%Z true))) in
    if $$ inv0 |-tgt false_expr >= (Expr.bop bop_or sz x y) $$
    then {{
             {{
                 {{
                     {{inv0 +++tgt false_expr >= (Expr.value x)}}
                       +++tgt (Expr.value x) >= false_expr
                 }}
                   +++tgt false_expr >= (Expr.value y)
             }}
               +++tgt (Expr.value y) >= false_expr
         }}
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
  | Infrule.ptrtoint_inttoptr src mid dst srcty midty dstty =>
    let srcty_sz_opt := get_bitsize srcty m_src in
    let midty_sz_opt := get_bitsize midty m_src in
    let dstty_sz_opt := get_bitsize dstty m_src in
    match (get_bitsize srcty m_src), (get_bitsize midty m_src), 
        (get_bitsize dstty m_src) with
    | (Some srcty_sz), (Some midty_sz), (Some dstty_sz) =>
      if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_inttoptr srcty src midty) $$ &&
         $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_ptrtoint midty mid dstty) $$ &&
         cond_le (Size.ThirtyTwo)
                 (INTEGER.of_Z (Size.to_Z Size.ThirtyTwo) (Size.to_Z srcty_sz) true) 
                 (INTEGER.of_Z (Size.to_Z Size.ThirtyTwo) (Size.to_Z midty_sz) true) &&
         sz_dec srcty_sz dstty_sz
      then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
      else apply_fail tt
    | _, _, _ => apply_fail tt
    end
  | Infrule.ptrtoint_load ptr ptrty v1 intty v2 a =>
    if $$ inv0 |-src (Expr.load ptr ptrty a) >= (Expr.value v1) $$ &&
       $$ inv0 |-src (Expr.cast castop_ptrtoint ptrty v1 intty) >= (Expr.value v2) $$ &&
       cond_same_bitsize intty ptrty m_src
    then {{ inv0 +++src (Expr.load ptr intty a) >= (Expr.value v2) }}
    else apply_fail tt
  | Infrule.ptrtoint_zero ptrty intty =>
    match ptrty with
    | typ_pointer elemty =>
      match intty with
      | typ_int sz =>
        let castlhs := (Expr.cast castop_ptrtoint ptrty
             (ValueT.const (const_null elemty)) intty)
        in
        let castrhs := (Expr.value (ValueT.const (const_zero sz))) in
        let inv1 := {{ inv0 +++src castlhs >= castrhs }} in
        {{ inv1 +++tgt castlhs >= castrhs }}
      | _ => apply_fail tt
      end
    | _ => apply_fail tt
    end
  | Infrule.inttoptr_ptrtoint src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_ptrtoint srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_inttoptr midty mid dstty) $$ &&
       cond_sameaddrspace srcty dstty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
    else apply_fail tt
  | Infrule.select_icmp_eq z y x v c cty =>
    let vc := ValueT.const c in
    if $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_eq cty x vc) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.select y cty x v) $$
    then
      {{ inv0 +++src (Expr.value z) >= (Expr.select y cty vc v) }}
    else apply_fail tt
  | Infrule.select_icmp_eq_xor1 z z' v x u w c c' s =>
    let vc := ValueT.const (const_newint s c) in
    let vnotc := ValueT.const (const_newint s c') in
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_and s x vc) >= (Expr.value w) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_eq (typ_int s) w vc0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x vnotc) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) x u) >= (Expr.value z) $$ &&
       cond_neg s c c'
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_eq_xor2 z z' v x u w c s =>
    let vc := ValueT.const (const_newint s c) in
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_and s x vc) >= (Expr.value w) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_eq (typ_int s) w vc0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s x vc) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) u x) >= (Expr.value z) $$ 
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_ne z y x v c cty =>
    let vc := ValueT.const c in
    if $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_ne cty x vc) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.select y cty v x) $$
    then
      {{ inv0 +++src (Expr.value z) >= (Expr.select y cty v vc) }}
    else apply_fail tt
  | Infrule.select_icmp_ne_xor1 z z' v x u w c c' s =>
    let vc := ValueT.const (const_newint s c) in
    let vnotc := ValueT.const (const_newint s c') in
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_and s x vc) >= (Expr.value w) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_ne (typ_int s) w vc0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x vnotc) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) u x) >= (Expr.value z) $$ &&
       cond_neg s c c'
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_ne_xor2 z z' v x u w c s =>
    let vc := ValueT.const (const_newint s c) in
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_and s x vc) >= (Expr.value w) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_ne (typ_int s) w vc0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s x vc) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) x u) >= (Expr.value z) $$ 
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_sgt_xor1 z z' v x u c c' s =>
    let vc := ValueT.const (const_newint s c) in
    let vm1 := ValueT.const (const_mone s) in
    let vnotc := ValueT.const (const_newint s c') in
    if $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_sgt (typ_int s) x vm1) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) x u) >= (Expr.value z) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x vnotc) >= (Expr.value z') $$ &&
       cond_neg s c c' && cond_signbit s vc
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_sgt_xor2 z z' v x u c s =>
    let vc := ValueT.const (const_newint s c) in
    let vm1 := ValueT.const (const_mone s) in
    if $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_sgt (typ_int s) x vm1) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) u x) >= (Expr.value z) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s x vc) >= (Expr.value z') $$ &&
       cond_signbit s vc
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_slt_xor1 z z' v x u c c' s =>
    let vc := ValueT.const (const_newint s c) in
    let vnotc := ValueT.const (const_newint s c') in
    let v0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_slt (typ_int s) x v0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) u x) >= (Expr.value z) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s x vnotc) >= (Expr.value z') $$ &&
       cond_neg s c c' && cond_signbit s vc
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_slt_xor2 z z' v x u c s =>
    let vc := ValueT.const (const_newint s c) in
    let v0 := ValueT.const (const_zero s) in
    if $$ inv0 |-tgt (Expr.bop bop_xor s x vc) >= (Expr.value u) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_slt (typ_int s) x v0) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.select v (typ_int s) x u) >= (Expr.value z) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s x vc) >= (Expr.value z') $$ &&
       cond_signbit s vc
    then
      {{ inv0 +++tgt (Expr.value z) >= (Expr.value z') }}
    else apply_fail tt
  | Infrule.select_icmp_sgt_const z y x c c' selcomm s =>
    let vz := ValueT.id z in
    let vc := ValueT.const (const_newint s c) in
    let vc' := ValueT.const (const_newint s c') in
    let i1 := INTEGER.of_Z (Size.to_Z s) (1%Z) true in
    let (sel_src, sel_tgt) := 
        if selcomm then ((Expr.select y (typ_int s) vc' x),
                         (Expr.select y (typ_int s) x vc'))
        else ((Expr.select y (typ_int s) x vc'),
              (Expr.select y (typ_int s) vc' x))
    in
    if $$ inv0 |-src (Expr.value vz) >= sel_src $$ &&
       $$ inv0 |-tgt sel_tgt >= (Expr.value vz) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_sgt (typ_int s) x vc) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_slt (typ_int s) x vc') >= (Expr.value y) $$ &&
       cond_plus s c i1 c'
    then {{ inv0 --- z }}
    else apply_fail tt
  | Infrule.select_icmp_slt_const z y x c c' selcomm s =>
    let vz := ValueT.id z in
    let vc := ValueT.const (const_newint s c) in
    let vc' := ValueT.const (const_newint s c') in
    let i1 := INTEGER.of_Z (Size.to_Z s) (1%Z) true in
    let (sel_src, sel_tgt) :=
        if selcomm then ((Expr.select y (typ_int s) vc' x),
                         (Expr.select y (typ_int s) x vc'))
        else ((Expr.select y (typ_int s) x vc'),
              (Expr.select y (typ_int s) vc' x))
    in
    if $$ inv0 |-src (Expr.value vz) >= sel_src $$ &&
       $$ inv0 |-tgt sel_tgt >= (Expr.value vz) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_slt (typ_int s) x vc) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_sgt (typ_int s) x vc') >= (Expr.value y) $$ &&
       cond_minus s c i1 c'
    then {{ inv0 --- z }}
    else apply_fail tt
  | Infrule.select_icmp_ugt_const z y x c c' selcomm s =>
    let vz := ValueT.id z in
    let vc := ValueT.const (const_newint s c) in
    let vc' := ValueT.const (const_newint s c') in
    let i1 := INTEGER.of_Z (Size.to_Z s) (1%Z) true in
    let (sel_src, sel_tgt) :=
        if selcomm then ((Expr.select y (typ_int s) vc' x),
                         (Expr.select y (typ_int s) x vc'))
        else ((Expr.select y (typ_int s) x vc'),
              (Expr.select y (typ_int s) vc' x))
    in
    if $$ inv0 |-src (Expr.value vz) >= sel_src $$ &&
       $$ inv0 |-tgt sel_tgt >= (Expr.value vz) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_ugt (typ_int s) x vc) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_ult (typ_int s) x vc') >= (Expr.value y) $$ &&
       cond_plus s c i1 c'
    then {{ inv0 --- z }}
    else apply_fail tt
  | Infrule.select_icmp_ult_const z y x c c' selcomm s =>
    let vz := ValueT.id z in
    let vc := ValueT.const (const_newint s c) in
    let vc' := ValueT.const (const_newint s c') in
    let i1 := INTEGER.of_Z (Size.to_Z s) (1%Z) true in
    let (sel_src, sel_tgt) :=
        if selcomm then ((Expr.select y (typ_int s) vc' x),
                         (Expr.select y (typ_int s) x vc'))
        else ((Expr.select y (typ_int s) x vc'),
              (Expr.select y (typ_int s) vc' x))
    in
    if $$ inv0 |-src (Expr.value vz) >= sel_src $$ &&
       $$ inv0 |-tgt sel_tgt >= (Expr.value vz) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.icmp cond_ult (typ_int s) x vc) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_ugt (typ_int s) x vc') >= (Expr.value y) $$ &&
       cond_minus s c i1 c'
    then {{ inv0 --- z }}
    else apply_fail tt
  | Infrule.sext_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_s midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_s srcty src dstty) }}
    else apply_fail tt
  | Infrule.sext_trunc_ashr z x x' v s1 s2 i3 =>
    let i1 := INTEGER.of_Z (Size.to_Z s1) (Size.to_Z s1) true in
    let i2 := INTEGER.of_Z (Size.to_Z s1) (Size.to_Z s2) true in
    let vs3 := ValueT.const (const_newint s1 i3) in
    if $$ inv0 |-tgt (Expr.trunc truncop_int (typ_int s1) v (typ_int s2)) >= (Expr.value x) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_shl s1 v vs3) >= (Expr.value x') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_ashr s1 x' vs3) >= (Expr.value z) $$ &&
       cond_plus s1 i3 i2 i1
    then
      {{ inv0 +++tgt (Expr.ext extop_s (typ_int s2) x (typ_int s1)) >= (Expr.value z) }}
    else 
      apply_fail tt
  | Infrule.shift_undef1 z y s =>
    let vundef := ValueT.const (const_undef (typ_int s)) in
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_shl s y vundef) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_ashr s y vundef) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_lshr s y vundef) $$
    then
      let inv1 := {{ inv0 +++src (Expr.value z) >= (Expr.value vundef) }} in
      {{ inv1 +++src (Expr.value vundef) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.shift_undef2 z y c s =>
    let vc := ValueT.const (const_newint s c) in
    let vundef := ValueT.const (const_undef (typ_int s)) in
    if ($$ inv0 |-src (Expr.value z) >= (Expr.bop bop_shl s y vc) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_ashr s y vc) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_lshr s y vc) $$) &&
       ((cond_le s (INTEGER.of_Z (Size.to_Z s) (Size.to_Z s) true) c) ||
        (cond_le s c (INTEGER.of_Z (Size.to_Z s) (-1)%Z true)))
    then
      let inv1 := {{ inv0 +++src (Expr.value z) >= (Expr.value vundef) }} in
      {{ inv1 +++src (Expr.value vundef) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.shift_zero1 z y s =>
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_shl s vc0 y) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_ashr s vc0 y) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_lshr s vc0 y) $$
    then
      let inv1 := {{ inv0 +++src (Expr.value z) >= (Expr.value vc0) }} in
      {{ inv1 +++src (Expr.value vc0) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.shift_zero2 z y s =>
    let vc0 := ValueT.const (const_zero s) in
    if $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_shl s y vc0) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_ashr s y vc0) $$ ||
       $$ inv0 |-src (Expr.value z) >= (Expr.bop bop_lshr s y vc0) $$
    then
      let inv1 := {{ inv0 +++src (Expr.value z) >= (Expr.value y) }} in
      {{ inv1 +++src (Expr.value y) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.sitofp_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_sitofp midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_sitofp srcty src dstty) }}
    else apply_fail tt
  | Infrule.sitofp_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_sitofp midty mid dstty) $$ 
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_uitofp srcty src dstty) }}
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
    let e1' := load_realign e1 in
    let e2' := load_realign e2 in
    let e3' := load_realign e3 in
    if ($$ inv0 |-src e1 >= e2 $$ || $$ inv0 |-src e1 >= e2' $$ ||
        $$ inv0 |-src e1' >= e2 $$ || $$ inv0 |-src e1' >= e2' $$) &&
       ($$ inv0 |-src e2 >= e3 $$ || $$ inv0 |-src e2 >= e3' $$ ||
        $$ inv0 |-src e2' >= e3 $$ || $$ inv0 |-src e2' >= e3' $$)
    then {{ inv0 +++src e1 >= e3 }}
    else apply_fail tt
  | Infrule.transitivity_tgt e1 e2 e3 =>
    let e1' := load_realign e1 in
    let e2' := load_realign e2 in
    let e3' := load_realign e3 in
    if ($$ inv0 |-tgt e1 >= e2 $$ || $$ inv0 |-tgt e1 >= e2' $$ ||
        $$ inv0 |-tgt e1' >= e2 $$ || $$ inv0 |-tgt e1' >= e2' $$) &&
       ($$ inv0 |-tgt e2 >= e3 $$ || $$ inv0 |-tgt e2 >= e3' $$ ||
        $$ inv0 |-tgt e2' >= e3 $$ || $$ inv0 |-tgt e2' >= e3' $$)
    then {{ inv0 +++tgt e1 >= e3 }}
    else apply_fail tt
  | Infrule.trunc_onebit z x y orgsz =>
    if $$ inv0 |-tgt (Expr.bop bop_and orgsz x (ValueT.const (const_int orgsz (INTEGER.of_Z (Size.to_Z orgsz) 1%Z true))))
          >= (Expr.value y) $$ &&
       $$ inv0 |-tgt (Expr.icmp cond_ne (typ_int orgsz) y 
            (ValueT.const (const_int orgsz (INTEGER.of_Z (Size.to_Z orgsz) 0%Z true)))) 
          >= (Expr.value z) $$
    then {{ inv0 +++tgt (Expr.trunc truncop_int (typ_int orgsz) x (typ_int (Size.from_Z 1))) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.trunc_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_int srcty src dstty) }}
    else apply_fail tt
  | Infrule.trunc_load_bitcast_rev_tgt src mid1 mid2 dst srcty midty a =>
    if $$ inv0 |-tgt (Expr.cast castop_bitcast (typ_pointer srcty) src (typ_pointer midty)) >= (Expr.value mid1) $$ &&
       $$ inv0 |-tgt (Expr.load mid1 midty a) >= (Expr.value mid2) $$ &&
       $$ inv0 |-tgt (Expr.trunc truncop_int midty mid2 srcty) >= (Expr.value dst) $$
    then {{ inv0 +++tgt (Expr.load src srcty a) >= (Expr.value dst) }}
    else apply_fail tt
  | Infrule.trunc_load_const_bitcast_rev_tgt src mid dst srcty midty a =>
    if $$ inv0 |-tgt (Expr.load (ValueT.const (const_castop castop_bitcast src (typ_pointer midty))) midty a) >= (Expr.value mid) $$ &&
       $$ inv0 |-tgt (Expr.trunc truncop_int midty mid srcty) >= (Expr.value dst) $$
    then {{ inv0 +++tgt (Expr.load src srcty a) >= (Expr.value dst) }}
    else apply_fail tt
  | Infrule.trunc_ptrtoint src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_ptrtoint srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_ptrtoint srcty src dstty) }}
    else apply_fail tt
  | Infrule.trunc_sext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_s srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$ 
    then
      match (srcty, dstty) with
      | (typ_int srcsz, typ_int dstsz) => 
        if Z.ltb (Size.to_Z srcsz) (Size.to_Z dstsz) then 
          {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_s srcty src dstty) }}
        else if sz_dec srcsz dstsz then
          {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
        else if Z.ltb (Size.to_Z dstsz) (Size.to_Z srcsz) then
          {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_int srcty src dstty) }}
        else apply_fail tt
      | _ => apply_fail tt
      end
    else apply_fail tt
  | Infrule.trunc_zext src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.ext extop_z srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.trunc truncop_int midty mid dstty) $$ 
    then
      match (srcty, dstty) with
      | (typ_int srcsz, typ_int dstsz) => 
        if Z.ltb (Size.to_Z srcsz) (Size.to_Z dstsz) then 
          {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_z srcty src dstty) }}
        else if sz_dec srcsz dstsz then
          {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_bitcast srcty src dstty) }}
        else if Z.ltb (Size.to_Z dstsz) (Size.to_Z srcsz) then
          {{ inv0 +++src (Expr.value dst) >= (Expr.trunc truncop_int srcty src dstty) }}
        else apply_fail tt
      | _ => apply_fail tt
      end
    else apply_fail tt
  | Infrule.rem_neg z my x y s =>
    if $$ inv0 |-src (Expr.value my) >= (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ && 
       $$ inv0 |-src (Expr.value (ValueT.id z)) >= (Expr.bop bop_srem s x my) $$
    then {{inv0 +++src (Expr.value (ValueT.id z)) >= (Expr.bop bop_srem s x y) }}
    else apply_fail tt
  | Infrule.diffblock_unique x y =>
    if $$ inv0 |-src x unique $$ ||
       $$ inv0 |-src y unique $$ then
      let inv1 := {{inv0 +++src (ValueT.id y) _||_ (ValueT.id x) }} in
      let inv2 := {{inv1 +++src (ValueT.id x) _||_ (ValueT.id y) }} in
      inv2
    else apply_fail tt
  | Infrule.diffblock_global_unique gx y =>
    match gx with
    | const_gid gx_ty gx_id =>
      if $$ inv0 |-src y unique $$ 
      then
        let inv1 := {{inv0 +++src (ValueT.const (const_gid gx_ty gx_id)) _||_ (ValueT.id y) }} in
        let inv2 := {{inv0 +++src (ValueT.id y) _||_ (ValueT.const (const_gid gx_ty gx_id)) }} in
        inv2
      else apply_fail tt
    | _ => debug_string "diffblock_global_unique : gx not globalvar" (apply_fail tt)
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
          let inv3 := {{inv2 +++tgt (ValueT.const (const_gid gx_ty gx_id)) _||_ (ValueT.const (const_gid gy_ty gy_id)) }} in
          let inv4 := {{inv3 +++tgt (ValueT.const (const_gid gy_ty gy_id)) _||_ (ValueT.const (const_gid gx_ty gx_id)) }} in
          inv4
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
  | Infrule.trunc_trunc_rev_tgt src mid dst srcty midty dstty =>
    if $$ inv0 |-tgt (Expr.trunc truncop_int srcty src midty) >= (Expr.value mid) $$ &&
       $$ inv0 |-tgt (Expr.trunc truncop_int midty mid dstty) >= (Expr.value dst) $$
    then {{inv0 +++tgt (Expr.trunc truncop_int srcty src dstty) >= (Expr.value dst) }}
    else apply_fail tt
  | Infrule.substitute x y e =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.value y) $$
    then
      {{inv0 +++src e >= (Expr.substitute x y e)}}
    else apply_fail tt
  | Infrule.substitute_rev x y e =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.value x) $$
    then
      {{inv0 +++src (Expr.substitute x y e) >= e}}
    else apply_fail tt
  | Infrule.substitute_tgt x y e =>
    if $$ inv0 |-tgt (Expr.value x) >= (Expr.value y) $$
    then
      {{inv0 +++tgt e >= (Expr.substitute x y e)}}
    else apply_fail tt
  | Infrule.substitute_rev_tgt x y e =>
    if $$ inv0 |-tgt (Expr.value y) >= (Expr.value x) $$
    then
      {{inv0 +++tgt (Expr.substitute x y e) >= e}}
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
  | Infrule.udiv_zext_const z x c k a s1 s2 =>
    let c1 := INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z c) false in
    let c2 := INTEGER.of_Z (Size.to_Z s2) (INTEGER.to_Z c) false in
    if $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) a (typ_int s2)) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_udiv s1 a (ValueT.const (const_int s1 c1)))
                     >= (Expr.value (ValueT.id k)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) (ValueT.id k) (typ_int s2))
                     >= (Expr.value (ValueT.id z)) $$ &&
       cond_uint_fitinsize s1 c 
    then
      {{ inv0 +++tgt (Expr.bop bop_udiv s2 (ValueT.id x) (ValueT.const (const_int s2 c2))) 
                     >= (Expr.value (ValueT.id z)) }}
    else 
      apply_fail tt
  | Infrule.uitofp_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.cast castop_uitofp midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.cast castop_uitofp srcty src dstty) }}
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
  | Infrule.urem_zext_const z x c k a s1 s2 =>
    let c1 := INTEGER.of_Z (Size.to_Z s1) (INTEGER.to_Z c) false in
    let c2 := INTEGER.of_Z (Size.to_Z s2) (INTEGER.to_Z c) false in
    if $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) a (typ_int s2)) >= (Expr.value (ValueT.id x)) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_urem s1 a (ValueT.const (const_int s1 c1)))
                     >= (Expr.value (ValueT.id k)) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int s1) (ValueT.id k) (typ_int s2))
                     >= (Expr.value (ValueT.id z)) $$ &&
       cond_uint_fitinsize s1 c 
    then
      {{ inv0 +++tgt (Expr.bop bop_urem s2 (ValueT.id x) (ValueT.const
                        (const_int s2 c))) >= (Expr.value (ValueT.id z)) }}
    else 
      apply_fail tt
  | Infrule.intro_eq x => 
    {{ inv0 +++src x >= x }}
  | Infrule.intro_eq_tgt x => 
    {{ inv0 +++tgt x >= x }}
  | Infrule.intro_ghost_src expr g =>
    if (match expr with | Expr.load _ _ _ => false | _ => true end)
    then
      let inv1 := (Assertion.update_src (Assertion.update_lessdef
        (ExprPairSet.filter
          (fun (p: ExprPair.t) => negb (Expr.eq_dec (Expr.value (ValueT.id (Tag.ghost, g))) (snd p)) &&
                                        negb (Expr.eq_dec (Expr.value (ValueT.id (Tag.ghost, g))) (fst p)))))
          inv0) in
      let inv2 := {{ inv1 +++src (Expr.value (ValueT.id (Tag.ghost, g))) >= expr }} in
      let inv3 := {{ inv2 +++src  expr >= (Expr.value (ValueT.id (Tag.ghost, g))) }} in
      inv3
    else apply_fail tt
  | Infrule.intro_ghost expr g =>
    if List.forallb (fun x => Assertion.not_in_maydiff inv0 x) (Expr.get_valueTs expr)
    then 
      let inv1 := Assertion.clear_idt (Tag.ghost, g) inv0 in
      let inv2 := {{ inv1 +++src expr >= (Expr.value (ValueT.id (Tag.ghost, g))) }} in
      let inv3 := {{ inv2 +++tgt (Expr.value (ValueT.id (Tag.ghost, g))) >= expr }} in
      inv3
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
  | Infrule.zext_bitcast src mid dst srcty midty dstty =>
    if $$ inv0 |-src (Expr.value mid) >= (Expr.cast castop_bitcast srcty src midty) $$ &&
       $$ inv0 |-src (Expr.value dst) >= (Expr.ext extop_z midty mid dstty) $$ &&
       cond_inttyp srcty
    then {{ inv0 +++src (Expr.value dst) >= (Expr.ext extop_z srcty src dstty) }}
    else apply_fail tt
  | Infrule.zext_trunc_and z x y w c s s' =>
    if $$ inv0 |-src (Expr.value y) >= (Expr.trunc truncop_int (typ_int s) x (typ_int s')) $$ &&
       $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_and s' y (ValueT.const c)) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.ext extop_z (typ_int s') w (typ_int s)) $$
    then 
      match c with
      | const_int s'' iv => 
        let iv_extended := INTEGER.of_Z (Size.to_Z s) (INTEGER.to_Z iv) true in
        {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_int s iv_extended))) }}
      | _ => {{ inv0 +++src (Expr.value z) >= (Expr.bop bop_and s x (ValueT.const (const_extop extop_z c (typ_int s)))) }}
      end
    else apply_fail tt
  | Infrule.zext_trunc_and_xor z x v w y y' c s s' =>
    if $$ inv0 |-tgt (Expr.trunc truncop_int (typ_int s) x (typ_int s')) >= (Expr.value v) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s' v (ValueT.const c)) >= (Expr.value w) $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s' w (ValueT.const c)) >= (Expr.value y) $$ &&
       (match c with
       | const_int s'' iv => 
         let iv_extended := INTEGER.of_Z (Size.to_Z s) (INTEGER.to_Z iv) true in
         $$ inv0 |-tgt (Expr.bop bop_and s x (ValueT.const (const_int s iv_extended))) >= (Expr.value y') $$ &&
         $$ inv0 |-tgt (Expr.bop bop_xor s y' (ValueT.const (const_int s iv_extended))) >= (Expr.value z) $$
       | _ => 
         $$ inv0 |-tgt (Expr.bop bop_and s x (ValueT.const (const_extop extop_z c (typ_int s)))) >= (Expr.value y') $$ &&
         $$ inv0 |-tgt (Expr.bop bop_xor s y' (ValueT.const (const_extop extop_z c (typ_int s)))) >= (Expr.value z) $$
       end)
    then {{ inv0 +++tgt (Expr.ext extop_z (typ_int s') y (typ_int s)) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.zext_xor z y y' x sz =>
    if $$ inv0 |-tgt (Expr.bop bop_xor (Size.One) x 
          (ValueT.const (const_int (Size.One) (INTEGER.of_Z 1 1%Z true)))) 
        >= (Expr.value y) $$ &&
       $$ inv0 |-tgt (Expr.ext extop_z (typ_int (Size.One)) x (typ_int sz)) 
        >= (Expr.value y') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor sz y' 
          (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) 1%Z true)))) 
        >= (Expr.value z) $$
    then {{ inv0 +++tgt (Expr.ext extop_z (typ_int (Size.One)) y (typ_int sz)) 
        >= (Expr.value z) }}
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
  | Infrule.icmp_inverse_rhs c ty x y b =>
    if $$ inv0 |-src (Expr.value (ValueT.const (const_int Size.One b))) >= (Expr.icmp c ty x y) $$
    then
      let c' := get_inverse_icmp_cond c in
      let b' := get_inverse_boolean_Int b in
      let inv1 :=
          {{inv0 +++src (Expr.value (ValueT.const (const_int Size.One b'))) >= (Expr.icmp c' ty x y)}}
      in {{inv1 +++src (Expr.icmp c' ty x y) >= (Expr.value (ValueT.const (const_int Size.One b')))}}
    else apply_fail tt
  | Infrule.icmp_inverse_tgt c ty x y b =>
    if $$ inv0 |-tgt (Expr.icmp c ty x y) >= (Expr.value (ValueT.const (const_int Size.One b))) $$
    then
      let c' := get_inverse_icmp_cond c in
      let b' := get_inverse_boolean_Int b in
      {{inv0 +++tgt (Expr.icmp c' ty x y) >= (Expr.value (ValueT.const (const_int Size.One b')))}}
    else apply_fail tt
  | Infrule.icmp_inverse_rhs_tgt c ty x y b =>
    if $$ inv0 |-tgt (Expr.value (ValueT.const (const_int Size.One b))) >= (Expr.icmp c ty x y) $$
    then
      let c' := get_inverse_icmp_cond c in
      let b' := get_inverse_boolean_Int b in
      let inv1 :=
          {{inv0 +++tgt (Expr.value (ValueT.const (const_int Size.One b'))) >= (Expr.icmp c' ty x y)}}
      in {{inv1 +++tgt (Expr.icmp c' ty x y) >= (Expr.value (ValueT.const (const_int Size.One b')))}}
    else apply_fail tt
  | Infrule.icmp_swap_operands c ty x y e =>
    if $$ inv0 |-src e >= (Expr.icmp c ty x y) $$
    then
      let c' := get_swapped_icmp_cond c in
      {{inv0 +++src e >= (Expr.icmp c' ty y x) }}
    else apply_fail tt
  | Infrule.icmp_swap_operands_rev c ty x y e =>
    if $$ inv0 |-src (Expr.icmp c ty x y) >= e $$
    then
      let c' := get_swapped_icmp_cond c in
      {{inv0 +++src (Expr.icmp c' ty y x) >= e }}
    else apply_fail tt
  | Infrule.icmp_swap_operands_tgt c ty x y e =>
    if $$ inv0 |-tgt e >= (Expr.icmp c ty x y) $$
    then
      let c' := get_swapped_icmp_cond c in
      {{inv0 +++tgt e >= (Expr.icmp c' ty y x) }}
    else apply_fail tt
  | Infrule.icmp_swap_operands_rev_tgt c ty x y e =>
    if $$ inv0 |-tgt (Expr.icmp c ty x y) >= e $$
    then
      let c' := get_swapped_icmp_cond c in
      {{inv0 +++tgt (Expr.icmp c' ty y x) >= e }}
    else apply_fail tt
  | Infrule.fcmp_swap_operands c fty x y e =>
    if $$ inv0 |-src e >= (Expr.fcmp c fty x y) $$
    then
      let c' := get_swapped_fcmp_cond c in
      {{inv0 +++src e >= (Expr.fcmp c' fty y x) }}
    else apply_fail tt
  | Infrule.fcmp_swap_operands_rev c fty x y e =>
    if $$ inv0 |-src (Expr.fcmp c fty x y) >= e $$
    then
      let c' := get_swapped_fcmp_cond c in
      {{inv0 +++src (Expr.fcmp c' fty y x) >= e }}
    else apply_fail tt
  | Infrule.fcmp_swap_operands_tgt c fty x y e =>
    if $$ inv0 |-tgt e >= (Expr.fcmp c fty x y) $$
    then
      let c' := get_swapped_fcmp_cond c in
      {{inv0 +++tgt e >= (Expr.fcmp c' fty y x) }}
    else apply_fail tt
  | Infrule.fcmp_swap_operands_rev_tgt c fty x y e =>
    if $$ inv0 |-tgt (Expr.fcmp c fty x y) >= e $$
    then
      let c' := get_swapped_fcmp_cond c in
      {{inv0 +++tgt (Expr.fcmp c' fty y x) >= e }}
    else apply_fail tt
  | Infrule.implies_false c1 c2 =>
    if $$ inv0 |-src (Expr.value c1) >= (Expr.value c2) $$
       && (negb (const_eqb c1 c2))
    then {{inv0 +++src fst (Assertion.false_encoding) >=
           snd (Assertion.false_encoding)}}
    else apply_fail tt
  | Infrule.icmp_eq_add_add z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_add s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_add s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_eq_same ty x y =>
    let Int_one := INTEGER.of_Z 1 1 true in
    if $$ inv0 |-src (Expr.value (ValueT.const (const_int Size.One Int_one))) >= (Expr.icmp cond_eq ty x y) $$
    then {{
             {{inv0 +++src (Expr.value x) >= (Expr.value y)}}
               +++src (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | Infrule.icmp_eq_same_tgt ty x y =>
    let Int_one := INTEGER.of_Z 1 1 true in
    if $$ inv0 |-tgt (Expr.value (ValueT.const (const_int Size.One Int_one))) >= (Expr.icmp cond_eq ty x y) $$
    then {{
             {{inv0 +++tgt (Expr.value x) >= (Expr.value y)}}
               +++tgt (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | Infrule.icmp_eq_srem z w x y s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_srem s x y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const
            (const_int (Size.from_Z 1%Z) (INTEGER.of_Z 1%Z 0%Z true))))}}
    else apply_fail tt
  | Infrule.icmp_eq_sub z x a b s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_sub s a b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) x
          (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_eq_sub_sub z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_sub s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_sub s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_eq_xor_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s a b) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_xor s z' (ValueT.const (const_mone s))) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{inv0 +++tgt (Expr.icmp cond_eq (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_eq_xor_xor z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_xor s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_eq (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_ne_add_add z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_add s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_add s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_ne_srem z w x y s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_srem s x y) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.value (ValueT.const
            (const_int (Size.from_Z 1%Z) (INTEGER.of_Z 1%Z (-1)%Z true))))}}
    else apply_fail tt
  | Infrule.icmp_ne_sub z x a b s =>
    if $$ inv0 |-src (Expr.value x) >= (Expr.bop bop_sub s a b) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) x
          (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_ne_sub_sub z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_sub s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_sub s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_ne_xor z a b s =>
    if $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) a b) $$ &&
       cond_onebit s
    then
      {{inv0 +++src (Expr.value z) >= (Expr.bop bop_xor s a b) }}
    else apply_fail tt
  | Infrule.icmp_ne_xor_xor z w x y a b s =>
    if $$ inv0 |-src (Expr.value w) >= (Expr.bop bop_xor s a x) $$ &&
       $$ inv0 |-src (Expr.value y) >= (Expr.bop bop_xor s b x) $$ &&
       $$ inv0 |-src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) w y) $$
    then {{ inv0 +++src (Expr.value z) >= (Expr.icmp cond_ne (typ_int s) a b) }}
    else apply_fail tt
  | Infrule.icmp_neq_same ty x y =>
    let Int_zero := INTEGER.of_Z 1 0 true in
    if $$ inv0 |-src (Expr.value (ValueT.const (const_int Size.One Int_zero))) >= (Expr.icmp cond_ne ty x y) $$
    then {{
             {{inv0 +++src (Expr.value x) >= (Expr.value y)}}
               +++src (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | Infrule.icmp_neq_same_tgt ty x y =>
    let Int_zero := INTEGER.of_Z 1 0 true in
    if $$ inv0 |-tgt (Expr.value (ValueT.const (const_int Size.One Int_zero))) >= (Expr.icmp cond_ne ty x y) $$
    then {{
             {{inv0 +++tgt (Expr.value x) >= (Expr.value y)}}
               +++tgt (Expr.value y) >= (Expr.value x)
         }}
    else apply_fail tt
  | Infrule.icmp_sge_or_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) a) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s z' b) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_sge (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_sgt_and_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) a) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s z' b) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_sgt (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_sle_or_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) b) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s z' a) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_sle (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_slt_and_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) b) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s z' a) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_slt (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_ule_or_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) a) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s z' b) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_ule (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_ult_and_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) a) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s z' b) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_ult (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_uge_or_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) b) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_or s z' a) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_uge (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.icmp_ugt_and_not z z' a b s =>
    if $$ inv0 |-tgt (Expr.bop bop_xor s (ValueT.const (const_mone s)) b) >= (Expr.value z') $$ &&
       $$ inv0 |-tgt (Expr.bop bop_and s z' a) >= (Expr.value z) $$ &&
       cond_onebit s
    then
      {{ inv0 +++tgt (Expr.icmp cond_ugt (typ_int s) a b) >= (Expr.value z) }}
    else apply_fail tt
  | Infrule.reduce_maydiff_lessdef =>
    reduce_maydiff_lessdef inv0
  | Infrule.reduce_maydiff_non_physical =>
    reduce_maydiff_non_physical inv0

  | _ => no_match_fail tt (* TODO *)
  end.

(* TODO *)
Definition apply_infrules
           (m_src m_tgt:module)
           (infrules:list Infrule.t)
           (inv0:Assertion.t): Assertion.t :=
  fold_left (fun i r => apply_infrule m_src m_tgt r i) infrules inv0.
