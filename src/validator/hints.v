Require Import vellvm.
Require Import alist.
Require Import FMapWeakList.
Require Import syntax_ext.

(** There are four hints components: maydiff, newly defined variables,
equations, and inference rules. *)

(** * Hint Component : 1. Maydiff *)

Definition maydiff_t := IdExtSetImpl.t.

(** * Hint Component : 2. Equations *)

Record eqs_t :=
{ eqs_eq_reg : EqRegSetImpl.t;
  eqs_eq_heap : EqHeapSetImpl.t;
  eqs_neq_reg : NeqRegSetImpl.t }.

(** * Hint Component : 3. Inference Rules *)

(* See doc/hint for details. *)

Inductive infrule_t : Type :=
| rule_add_assoc (z:id_ext) (y:id_ext) (x:value_ext) (s:sz) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t)
| rule_replace_rhs (z:id_ext) (x:id_ext) (y:value_ext) (e:rhs_ext) (e':rhs_ext)
| rule_replace_rhs_opt (z:id_ext) (x:id_ext) (y:value_ext) (e:rhs_ext) (e':rhs_ext)
| rule_replace_lhs (x:id_ext) (y:id_ext) (e:rhs_ext)
| rule_remove_maydiff (v:id_ext) (e:rhs_ext)
| rule_remove_maydiff_rhs (v:id_ext) (e:id_ext)
| rule_eq_generate_same (x:id_ext) (y:id_ext) (e:rhs_ext)
| rule_eq_generate_same_heap (x:id_ext) (y:id_ext) (p:value_ext) (t:typ) (a:align)
| rule_eq_generate_same_heap_value (x:id_ext) (p:value_ext) (v:value_ext) (t:typ) (a:align)
| rule_add_signbit (x:id_ext) (sz:sz) (e:value_ext) (s:value_ext)
| rule_add_zext_bool (x:id_ext) (y:id_ext) (b:value_ext) (sz:sz) (c:INTEGER.t) (c':INTEGER.t)
| rule_ptr_trans (p:id_ext) (q:value_ext) (v:value_ext) (t:typ) (a:align)
| rule_add_onebit (z:id_ext) (x:value_ext) (y:value_ext)
| rule_stash_variable (z:id_ext) (t:id)
| rule_add_shift (y:id_ext) (s:sz) (v:value_ext)
| rule_add_sub (z:id_ext) (minusy:id_ext) (s:sz) (x:value_ext) (y:value_ext)
| rule_add_commutative (z:id_ext) (s:sz) (x:value_ext) (y:value_ext)
| rule_sub_add (z:id_ext) (minusy:id_ext) (s:sz) (x:value_ext) (y:value_ext)
| rule_sub_onebit (z:id_ext) (x:value_ext) (y:value_ext)
| rule_sub_mone (z:id_ext) (s:sz) (x:value_ext)
| rule_sub_const_not (z:id_ext) (y:id_ext) (s:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_add_mul_fold (z:id_ext) (y:id_ext) (s:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_add_const_not (z:id_ext) (y:id_ext) (s:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_add_select_zero (z:id_ext) (x:id_ext) (y:id_ext) (c:value_ext) (s:sz) (n:value_ext) (a:value_ext)
| rule_add_select_zero2 (z:id_ext) (x:id_ext) (y:id_ext) (c:value_ext) (s:sz) (n:value_ext) (a:value_ext)
| rule_sub_zext_bool (x:id_ext) (y:id_ext) (b:value_ext) (sz:sz) (c:INTEGER.t) (c':INTEGER.t)
| rule_sub_const_add (z:id_ext) (y:id_ext) (sz:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t)
| rule_sub_remove (z:id_ext) (y:id_ext) (sz:sz) (a:value_ext) (b:value_ext)
| rule_sub_remove2 (z:id_ext) (y:id_ext) (sz:sz) (a:value_ext) (b:value_ext)
| rule_sub_sdiv (z:id_ext) (y:id_ext) (sz:sz) (x:value_ext) (c:INTEGER.t) (c':INTEGER.t)
| rule_sub_shl (z:id_ext) (x:id_ext) (y:id_ext) (sz:sz) (mx:value_ext) (a:value_ext)
| rule_sub_mul (z:id_ext) (y:id_ext) (sz:sz) (x:value_ext) (c:INTEGER.t) (c':INTEGER.t)
| rule_sub_mul2 (z:id_ext) (y:id_ext) (sz:sz) (x:value_ext) (c:INTEGER.t) (c':INTEGER.t)
| rule_mul_mone (z:id_ext) (sz:sz) (x:value_ext)
| rule_mul_neg (z:id_ext) (mx:id_ext) (my:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_mul_bool (z:id_ext) (x:value_ext) (y:value_ext)
| rule_mul_commutative (z:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_mul_shl (z:id_ext) (y:id_ext) (sz:sz) (x:value_ext) (a:value_ext)
| rule_div_sub_srem (z:id_ext) (b:id_ext) (a:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_div_sub_urem (z:id_ext) (b:id_ext) (a:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_div_zext (z:id_ext) (x:id_ext) (y:id_ext) (k:id_ext) (sz1:sz) (sz2:sz) (a:value_ext) (b:value_ext)
| rule_div_mone (z:id_ext) (sz:sz) (x:value_ext)
| rule_rem_zext (z:id_ext) (x:id_ext) (y:id_ext) (k:id_ext) (sz1:sz) (sz2:sz) (a:value_ext) (b:value_ext)
| rule_rem_neg (z:id_ext) (my:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_rem_neg2 (z:id_ext) (sz:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_inbound_remove (x:id_ext) (y:id_ext) (pt:typ) (pa:align) (t:typ) (a:value_ext) (idx:list (sz*value_ext)) (u:typ) (v:value_ext)
| rule_inbound_remove2 (x:id_ext) (y:id_ext) (pt:typ) (pa:align) (t:typ) (a:value_ext) (idx:list (sz*value_ext)) (u:typ) (v:value_ext)
| rule_select_trunc (z:id_ext) (x:id_ext) (y:id_ext) (z':id_ext) (sz1:sz) (sz2:sz) (a:value_ext) (b:value_ext) (c:value_ext)
| rule_select_add (z:id_ext) (x:id_ext) (y:id_ext) (z':id_ext) (sz1:sz) (a:value_ext) (b:value_ext) (c:value_ext) (cond:value_ext)
| rule_select_const_gt (z:id_ext) (b:id_ext) (sz1:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_or_xor (z:id_ext) (y:id_ext) (sz1:sz) (a:value_ext) (b:value_ext)
| rule_or_commutative (z:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_trunc_onebit (z:id_ext) (k:id_ext) (sz:sz) (y:value_ext)
| rule_cmp_onebit (z:id_ext) (x:value_ext) (y:value_ext)
| rule_cmp_eq (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_ult (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_shift_undef (z:id_ext) (s:sz) (a:value_ext)
| rule_and_same (z:id_ext) (s:sz) (a:value_ext)
| rule_and_zero (z:id_ext) (s:sz) (a:value_ext)
| rule_and_mone (z:id_ext) (s:sz) (a:value_ext)
| rule_add_mask (z:id_ext) (y:id_ext) (y':id_ext) (s:sz) (x:value_ext) (c1:INTEGER.t) (c2:INTEGER.t)
| rule_neq_generate_gm (x:id) (y:id_ext)
| rule_and_undef (z:id_ext) (s:sz) (a:value_ext)
| rule_and_not (z:id_ext) (y:id_ext) (s:sz) (x:value_ext)
| rule_and_commutative (z:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_and_or (z:id_ext) (y:id_ext) (s:sz) (x:value_ext) (a:value_ext)
| rule_and_demorgan (z:id_ext) (x:id_ext) (y:id_ext) (z':id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_and_not_or (z:id_ext) (x:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_or_undef (z:id_ext) (s:sz) (a:value_ext)
| rule_or_same (z:id_ext) (s:sz) (a:value_ext)
| rule_or_zero (z:id_ext) (s:sz) (a:value_ext)
| rule_or_mone (z:id_ext) (s:sz) (a:value_ext)
| rule_or_not (z:id_ext) (y:id_ext) (s:sz) (x:value_ext)
| rule_or_and (z:id_ext) (y:id_ext) (s:sz) (x:value_ext) (a:value_ext)
| rule_xor_zero (z:id_ext) (s:sz) (a:value_ext)
| rule_xor_same (z:id_ext) (s:sz) (a:value_ext)
| rule_xor_commutative (z:id_ext) (sz:sz) (x:value_ext) (y:value_ext)
| rule_xor_not (z:id_ext) (y:id_ext) (s:sz) (x:value_ext)
| rule_zext_trunc_and (z:id_ext) (y:id_ext) (x:id_ext) (a:value_ext) (s1:sz) (s2:sz) (c:INTEGER.t)
| rule_zext_trunc_and_xor (z:id_ext) (y:id_ext) (x:id_ext) (w:id_ext) (w':id_ext) (a:value_ext) (s1:sz) (s2:sz) (c:INTEGER.t)
| rule_zext_xor (z:id_ext) (y:id_ext) (y':id_ext) (a:value_ext) (s:sz)
| rule_sext_trunc (z:id_ext) (y:id_ext) (y':id_ext) (a:value_ext) (s1:sz) (s2:sz) (n:INTEGER.t)
| rule_trunc_trunc (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_trunc_zext1 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz)
| rule_trunc_zext2 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_trunc_zext3 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_trunc_sext1 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz)
| rule_trunc_sext2 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_trunc_sext3 (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_zext_zext (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_sext_zext (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_sext_sext (z:id_ext) (y:id_ext) (a:value_ext) (s1:sz) (s2:sz) (s3:sz)
| rule_fptoui_fpext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_fptosi_fpext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_uitofp_zext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_sitofp_sext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_fptrunc_fptrunc (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_fptrunc_fpext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ)
| rule_fpext_fpext (z:id_ext) (y:id_ext) (a:value_ext) (t1:typ) (t2:typ) (t3:typ)
| rule_cmp_swap_ult (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_ugt (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_ule (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_uge (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_slt (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_sgt (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_sle (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_sge (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_eq (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_swap_ne (z:id_ext) (a:value_ext) (b:value_ext) (t:typ)
| rule_cmp_slt_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_sgt_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_ugt_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_ule_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_uge_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_sle_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_sge_onebit (z:id_ext) (y:id_ext) (a:value_ext) (b:value_ext)
| rule_cmp_eq_sub (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_ne_sub (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_eq_srem (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_eq_srem2 (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_ne_srem (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_ne_srem2 (z:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext)
| rule_cmp_eq_xor (z:id_ext) (x:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext) (c:value_ext)
| rule_cmp_ne_xor (z:id_ext) (x:id_ext) (y:id_ext) (s:sz) (a:value_ext) (b:value_ext) (c:value_ext)
.

Definition infrules_t := list infrule_t.

(** * Hint Component : 5. Isolated variables *)

Definition isolated_t := IdExtSetImpl.t.


(** * Invariants 

An invariant for a command consists of the following 2 items:
- equations_original: conditions satisfiable at certain program state
  in the original program.
- equations_optimized: conditions satisfiable at certain program state
  in the optimized program.  *)

Structure invariant_t : Type := mkInvariant {
  invariant_original: eqs_t;
  invariant_optimized: eqs_t;
  iso_original: isolated_t;
  iso_optimized: isolated_t
}.


(** * Hints

A hint for a certain program point consists of the following 3 items:
- maydiff: variables the values of which might be different between
  the left and the right program.
- invariant: invariant that is satisfied.
- infrules: inference rules which is used.  *)

Structure insn_hint_t : Type := mkInsnHint {
  hint_maydiff: maydiff_t;
  hint_invariant: invariant_t;
  hint_infrules: infrules_t
}.


(**
- Hints for a block consists of hints for each line.
- Hints for higher structures are accordingly defined.  *)

Structure block_hint_t : Type := mkBlockHint {
  phi_hint: AssocList insn_hint_t;
  cmds_hint: AssocList (list insn_hint_t);
  term_hint: insn_hint_t
}.

Record fdef_hint_t : Type := mkFdefHint {
  block_hints : AssocList block_hint_t
}.

Definition products_hint_t : Type := AssocList fdef_hint_t.

Definition modules_hint_t : Type := list products_hint_t.
Definition system_hint_t : Type := modules_hint_t.

(** * Auxiliary Functions on Hint *)

Definition first_hint {A:Type} (l:list A) : option A :=
  match l with
    | hd::_ => Some hd
    | _ => None
  end.

Fixpoint last_hint {A:Type} (l:list A) : option A :=
  match l with
    | hd::nil => Some hd
    | _::tl => last_hint tl
    | _ => None
  end.

Definition lift_fdef_hint_to_system (fid: atom) (fhint: fdef_hint_t)
  : system_hint_t := [ [(fid, fhint)] ].

(** ** General for insn_hint_t *)

Definition orig_f (f:eqs_t -> eqs_t) (inv:invariant_t) : invariant_t :=
  {| invariant_original := f (invariant_original inv);
     invariant_optimized := invariant_optimized inv;
     iso_original := iso_original inv;
     iso_optimized := iso_optimized inv |}.

Definition opt_f (f:eqs_t -> eqs_t) (inv:invariant_t) : invariant_t :=
  {| invariant_original := invariant_original inv;
     invariant_optimized := f (invariant_optimized inv);
     iso_original := iso_original inv;
     iso_optimized := iso_optimized inv |}.

Definition iso_orig_f (f:isolated_t -> isolated_t) (inv:invariant_t) : invariant_t :=
  {| invariant_original := invariant_original inv;
     invariant_optimized := invariant_optimized inv;
     iso_original := f (iso_original inv);
     iso_optimized := iso_optimized inv |}.

Definition iso_opt_f (f:isolated_t -> isolated_t) (inv:invariant_t) : invariant_t :=
  {| invariant_original := invariant_original inv;
     invariant_optimized := invariant_optimized inv;
     iso_original := iso_original inv;
     iso_optimized := f (iso_optimized inv) |}.

Definition md_f (f:maydiff_t -> maydiff_t) (h:insn_hint_t) : insn_hint_t :=
  {| hint_maydiff := f (hint_maydiff h);
     hint_invariant := hint_invariant h;
     hint_infrules := hint_infrules h |}.

Definition inv_f (f:invariant_t -> invariant_t) (h:insn_hint_t) : insn_hint_t :=
  {| hint_maydiff := hint_maydiff h;
     hint_invariant := f (hint_invariant h);
     hint_infrules := hint_infrules h |}.

(** ** Add for invariant_t *)

Definition add_eq_reg (x:EqRegSetImpl.elt) (e:eqs_t) : eqs_t :=
  {| eqs_eq_reg := EqRegSetImpl.add x (eqs_eq_reg e);
     eqs_eq_heap := eqs_eq_heap e;
     eqs_neq_reg := eqs_neq_reg e |}.

Definition add_eq_heap (x:EqHeapSetImpl.elt) (e:eqs_t) : eqs_t :=
  {| eqs_eq_reg := eqs_eq_reg e;
     eqs_eq_heap := EqHeapSetImpl.add x (eqs_eq_heap e);
     eqs_neq_reg := eqs_neq_reg e |}.

Definition add_neq_reg (x:NeqRegSetImpl.elt) (e:eqs_t) : eqs_t :=
  {| eqs_eq_reg := eqs_eq_reg e;
     eqs_eq_heap := eqs_eq_heap e;
     eqs_neq_reg := NeqRegSetImpl.add x (eqs_neq_reg e) |}.

Definition add_eq_reg_orig (x:EqRegSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (orig_f (add_eq_reg x)) h.

Definition add_eq_reg_opt (x:EqRegSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (opt_f (add_eq_reg x)) h.

Definition add_eq_heap_orig (x:EqHeapSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (orig_f (add_eq_heap x)) h.

Definition add_eq_heap_opt (x:EqHeapSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (opt_f (add_eq_heap x)) h.

Definition add_neq_reg_orig (x:NeqRegSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (orig_f (add_neq_reg x)) h.

Definition add_neq_reg_opt (x:NeqRegSetImpl.elt) (h:insn_hint_t) : insn_hint_t :=
  inv_f (opt_f (add_neq_reg x)) h.

Definition add_iso_orig (x:id_ext) (h:insn_hint_t) : insn_hint_t :=
  inv_f (iso_orig_f (IdExtSetImpl.add x)) h.

Definition add_iso_opt (x:id_ext) (h:insn_hint_t) : insn_hint_t :=
  inv_f (iso_opt_f (IdExtSetImpl.add x)) h.

(** ** Mem for invariant_t *)

Definition mem_eq_reg (x:EqRegSetImpl.elt) (e:eqs_t) : bool :=
  EqRegSetImpl.mem x (eqs_eq_reg e).

Definition mem_eq_heap (x:EqHeapSetImpl.elt) (e:eqs_t) : bool :=
  EqHeapSetImpl.mem x (eqs_eq_heap e).

Definition mem_neq_reg (x:NeqRegSetImpl.elt) (e:eqs_t) : bool :=
  NeqRegSetImpl.mem x (eqs_neq_reg e).

Definition mem_eq_reg_orig (x:EqRegSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_eq_reg x (invariant_original (hint_invariant h)).

Definition mem_eq_reg_opt (x:EqRegSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_eq_reg x (invariant_optimized (hint_invariant h)).

Definition mem_eq_heap_orig (x:EqHeapSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_eq_heap x (invariant_original (hint_invariant h)).

Definition mem_eq_heap_opt (x:EqHeapSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_eq_heap x (invariant_optimized (hint_invariant h)).

Definition mem_neq_reg_orig (x:NeqRegSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_neq_reg x (invariant_original (hint_invariant h)).

Definition mem_neq_reg_opt (x:NeqRegSetImpl.elt) (h:insn_hint_t) : bool :=
  mem_neq_reg x (invariant_optimized (hint_invariant h)).

Definition mem_iso_orig (x:id_ext) (h:insn_hint_t) : bool :=
  IdExtSetImpl.mem x (iso_original (hint_invariant h)).

Definition mem_iso_opt (x:id_ext) (h:insn_hint_t) : bool :=
  IdExtSetImpl.mem x (iso_optimized (hint_invariant h)).

(** ** Add/Remove for maydiff_t *)

Definition add_md (x:id_ext) (h:insn_hint_t) : insn_hint_t :=
  md_f (IdExtSetImpl.add x) h.

Definition remove_md (x:id_ext) (h:insn_hint_t) : insn_hint_t :=
  md_f (IdExtSetImpl.remove x) h.

(** ** Mem for maydiff_t *)

Definition mem_md (x:id_ext) (h:insn_hint_t) : bool :=
  IdExtSetImpl.mem x (hint_maydiff h).


(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
