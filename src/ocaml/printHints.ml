open Infrastructure
(* open Interpreter *)
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open ParseHints
open Coq_pretty_printer
open Datatype_base

let string_of_atom ?(indent=0) x = (String.make indent ' ') ^ x

let string_of_atom_opt ?(indent=0) x =
  (String.make indent ' ')
  ^ (match x with
     | Some x -> x
     | None -> "None")

let rec string_of_module_hint ?(indent=0) hint =
  string_of_alist_endline ~indent:(indent) string_of_product_hint hint

and string_of_product_hint ?(indent=0) (hint:fdef_hint_t) =
    (String.make indent ' ') ^ "blocks:\n"
  ^ (string_of_alist_endline ~indent:(indent+1) (string_of_block_hint ~indent:(indent+2)) hint)

and string_of_block_hint ?(indent=0) hint =
  (String.make indent ' ') ^ "phis:\n"
  ^ (string_of_AL_phi_insn_hint ~indent:(indent+1) hint.phi_hint)
  ^ (String.make indent ' ') ^ "cmds:\n"
  ^ (string_of_AL_insn_hint ~indent:(indent+1) hint.cmds_hint)
  ^ (String.make indent ' ') ^ "tmns:\n"
  ^ (string_of_insn_hint ~indent:(indent+1) hint.term_hint)

and string_of_AL_insn_hint ?(indent=0) hint = 
  string_of_alist_endline ~indent:(indent+1) (fun i -> (string_of_insn_list_hint ~indent:(indent+2) i) ^ "\n") hint

and string_of_AL_phi_insn_hint ?(indent=0) hint = 
  string_of_alist_endline ~indent:(indent+1) (string_of_insn_hint ~indent:(indent+2)) hint

and string_of_insn_list_hint ?(indent=0) hint =
  string_of_list_endline (string_of_insn_hint ~indent:(indent+1)) hint

and string_of_insn_hint ?(indent=0) hint =
  (String.make indent ' ') ^ "maydiffs:\n"
  ^ (string_of_maydiff ~indent:(indent+1) hint.hint_maydiff)
  ^ (String.make indent ' ') ^ "invariants:\n"
  ^ (string_of_invariant ~indent:(indent+1) hint.hint_invariant)
  ^ (String.make indent ' ') ^ "infrules:\n"
  ^ (string_of_list_endline (fun i -> (String.make (indent+2) ' ') ^ (string_of_infrule i)) hint.hint_infrules)

and string_of_maydiff ?(indent=0) hint =
  (String.make indent ' ') ^ (string_of_atom_exts hint) ^ "\n"
    
and string_of_invariant ?(indent=0) hint =
  (String.make indent ' ') ^ "left:\n" ^ (string_of_equations ~indent:(indent+1) hint.invariant_original)
  ^ (String.make indent ' ') ^ "right:\n" ^ (string_of_equations ~indent:(indent+1) hint.invariant_optimized) 
  ^ (String.make indent ' ') ^ "isolated_orig: " ^ (string_of_atom_exts hint.iso_original) ^ "\n"
  ^ (String.make indent ' ') ^ "isolated_opt: " ^ (string_of_atom_exts hint.iso_optimized) ^ "\n"

and string_of_APInt i =
  Int64.to_string (Llvm.APInt.get_sext_value i)

and string_of_infrule hint =
  match hint with
  | Coq_rule_add_assoc (z, y, x, s, c1, c2, c3) -> sprintf "add_assoc(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext x) (string_of_int s) (string_of_APInt c1) (string_of_APInt c2) (string_of_APInt c3)
  | Coq_rule_replace_rhs (z, x, y, e, e') -> sprintf "replace_rhs(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_value_ext y) (string_of_rhs_ext e) (string_of_rhs_ext e')
  | Coq_rule_replace_rhs_opt (z, x, y, e, e') -> sprintf "replace_rhs_opt(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_value_ext y) (string_of_rhs_ext e) (string_of_rhs_ext e')
  | Coq_rule_replace_lhs (x, y, e) -> sprintf "replace_lhs(%s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_rhs_ext e)
  | Coq_rule_remove_maydiff (v, e) -> sprintf "remove_maydiff(%s, %s)" (string_of_id_ext v) (string_of_rhs_ext e)
  | Coq_rule_remove_maydiff_rhs (v, e) -> sprintf "remove_maydiff_rhs(%s, %s)" (string_of_id_ext v) (string_of_id_ext e)
  | Coq_rule_eq_generate_same (x, y, e) -> sprintf "eq_generate_same(%s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_rhs_ext e)
  | Coq_rule_eq_generate_same_heap (x, y, p, t, a) -> sprintf "eq_generate_same_heap(%s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_value_ext p) (string_of_typ t) (string_of_int a)
  | Coq_rule_eq_generate_same_heap_value (x, p, v, t, a) -> sprintf "eq_generate_same_heap_value(%s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_value_ext p) (string_of_value_ext v) (string_of_typ t) (string_of_int a)
  | Coq_rule_neq_generate_gm (x, y) -> sprintf "neq_generate_gm(%s, %s)" (x) (string_of_id_ext y)
  | Coq_rule_add_signbit (x, sz, e, s) -> sprintf "add_signbit(%s, %s, %s, %s)" (string_of_id_ext x) (string_of_int sz) (string_of_value_ext e) (string_of_value_ext s)
  | Coq_rule_add_zext_bool (x, y, b, sz, c, c') -> sprintf "add_zext_bool(%s, %s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_value_ext b) (string_of_int sz) (string_of_APInt c) (string_of_APInt c')
  | Coq_rule_ptr_trans (p, q, v, t, a) -> sprintf "ptr_trans(%s, %s, %s, %s, %s)" (string_of_id_ext p) (string_of_value_ext q) (string_of_value_ext v) (string_of_typ t) (string_of_int a)
  | Coq_rule_add_onebit (x, x0, x1) -> sprintf "add_onebit(%s, %s, %s)" (string_of_id_ext x) (string_of_value_ext x0) (string_of_value_ext x1)
  | Coq_rule_stash_variable (z, t) -> sprintf "stash_variable(%s, %s)" (string_of_id_ext z) (t)
  | Coq_rule_add_shift (y, s, x) -> sprintf "add_shift(%s, %s, %s)" (string_of_id_ext y) (string_of_int s) (string_of_value_ext x)
  | Coq_rule_add_sub (z, minusy, s, x, y) -> sprintf "add_sub(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext minusy) (string_of_int s) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_add_commutative (z, s, x, y) -> sprintf "add_commutative(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_sub_add (z, minusy, s, x, y) -> sprintf "sub_add(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext minusy) (string_of_int s) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_sub_onebit (x, x0, x1) -> sprintf "sub_onebit(%s, %s, %s)" (string_of_id_ext x) (string_of_value_ext x0) (string_of_value_ext x1)
  | Coq_rule_sub_mone (z, s, x) -> sprintf "sub_mone(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext x)
  | Coq_rule_sub_const_not (z, y, s, x, c1, c2) -> sprintf "sub_const_not(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_add_mul_fold (z, y, s, x, c1, c2) -> sprintf "add_mul_fold(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_add_const_not (z, y, s, x, c1, c2) -> sprintf "add_const_not(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_add_select_zero (z, x, y, c, s, n, a) -> sprintf "add_select_zero(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_value_ext c) (string_of_int s) (string_of_value_ext n) (string_of_value_ext a)
  | Coq_rule_add_select_zero2 (z, x, y, c, s, n, a) -> sprintf "add_select_zero2(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_value_ext c) (string_of_int s) (string_of_value_ext n) (string_of_value_ext a)
  | Coq_rule_sub_zext_bool (x, y, b, sz, c, c') -> sprintf "sub_zext_bool(%s, %s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_value_ext b) (string_of_int sz) (string_of_APInt c) (string_of_APInt c')
  | Coq_rule_sub_const_add (z, y, sz, x, c1, c2, c3) -> sprintf "sub_const_add(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2) (string_of_APInt c3)
  | Coq_rule_sub_remove (z, y, sz, a, b) -> sprintf "sub_remove(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_sub_remove2 (z, y, sz, a, b) -> sprintf "sub_remove2(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_sub_sdiv (z, y, sz, x, c, c') -> sprintf "sub_sdiv(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext x) (string_of_APInt c) (string_of_APInt c')
  | Coq_rule_sub_shl (z, x, y, sz, mx, a) -> sprintf "sub_shl(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext mx) (string_of_value_ext a)
  | Coq_rule_sub_mul (z, y, sz, x, c, c') -> sprintf "sub_mul(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext x) (string_of_APInt c) (string_of_APInt c')
  | Coq_rule_sub_mul2 (z, y, sz, x, c, c') -> sprintf "sub_mul2(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext x) (string_of_APInt c) (string_of_APInt c')
  | Coq_rule_mul_mone (z, sz, x) -> sprintf "mul_mone(%s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x)
  | Coq_rule_mul_neg (z, mx, my, sz, x, y) -> sprintf "mul_neg(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext mx) (string_of_id_ext my) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_mul_bool (z, x, y) -> sprintf "mul_bool(%s, %s, %s)" (string_of_id_ext z) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_mul_commutative (z, sz, x, y) -> sprintf "mul_commutative(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_mul_shl (z, y, sz, x, a) -> sprintf "mul_shl(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext a)
  | Coq_rule_div_sub_srem (z, b, a, sz, x, y) -> sprintf "div_sub_srem(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext b) (string_of_id_ext a) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_div_sub_urem (z, b, a, sz, x, y) -> sprintf "div_sub_urem(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext b) (string_of_id_ext a) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_div_zext (z, x, y, k, sz1, sz2, a, b) -> sprintf "div_zext(%s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_id_ext k) (string_of_int sz1) (string_of_int sz2) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_div_mone (z, sz, x) -> sprintf "div_mone(%s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x)
  | Coq_rule_rem_zext (z, x, y, k, sz1, sz2, a, b) -> sprintf "rem_zext(%s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_id_ext k) (string_of_int sz1) (string_of_int sz2) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_rem_neg (z, my, sz, x, y) -> sprintf "rem_neg(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext my) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_rem_neg2 (z, sz, x, c1, c2) -> sprintf "rem_neg2(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_inbound_remove (x, y, pt, pa, t, a ,idx, u, v) -> sprintf "inbound_remove(%s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_typ pt) "string_of_align" (string_of_typ t) (string_of_value_ext a) (string_of_typ u) (string_of_value_ext v)
  | Coq_rule_inbound_remove2 (x, y, pt, pa, t, a ,idx, u, v) -> sprintf "inbound_remove2(%s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext x) (string_of_id_ext y) (string_of_typ pt) "string_of_align" (string_of_typ t) (string_of_value_ext a) (string_of_typ u) (string_of_value_ext v)
  | Coq_rule_select_trunc (z, x, y, z', s1, s2, a, b, c) -> sprintf "select_trunc(%s, %s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_id_ext z') (string_of_int s1) (string_of_int s2) (string_of_value_ext a) (string_of_value_ext b) (string_of_value_ext c)
  | Coq_rule_select_add (z, x, y, z', s1, a, b, c, cond) -> sprintf "select_add(%s, %s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_id_ext z') (string_of_int s1) (string_of_value_ext a) (string_of_value_ext b) (string_of_value_ext c) (string_of_value_ext cond)
  | Coq_rule_select_const_gt (z, b, s1, x, c1, c2) -> sprintf "select_const_gt(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext b) (string_of_int s1) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_or_xor (z, y, s1, a, b) -> sprintf "or_xor(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s1) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_or_commutative (z, sz, x, y) -> sprintf "or_commutative(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_trunc_onebit (z, k, sz, y) -> sprintf "trunc_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext k) (string_of_int sz) (string_of_value_ext y)
  | Coq_rule_cmp_onebit (z, x, y) -> sprintf "cmp_onebit(%s, %s, %s)" (string_of_id_ext z) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_cmp_eq (z, y, a, b) -> sprintf "cmp_eq(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ult (z, y, a, b) -> sprintf "cmp_ult(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_shift_undef (z, s, a) -> sprintf "shift_undef(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_and_same (z, s, a) -> sprintf "and_same(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_and_zero (z, s, a) -> sprintf "and_zero(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_and_mone (z, s, a) -> sprintf "and_mone(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_add_mask (z, y, y', s, x, c1, c2) -> sprintf "add_mask(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_id_ext y') (string_of_int s) (string_of_value_ext x) (string_of_APInt c1) (string_of_APInt c2)
  | Coq_rule_and_undef (z, s, a) -> sprintf "and_undef(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_and_not (z, y, s, x) -> sprintf "and_not(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x)
  | Coq_rule_and_commutative (z, sz, x, y) -> sprintf "and_commutative(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_and_or (z, y, s, x, a) -> sprintf "and_or(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x) (string_of_value_ext a)
  | Coq_rule_and_demorgan (z, x, y, z', s, a, b) -> sprintf "and_demorgan(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_id_ext z') (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_and_not_or (z, x, y, s, a, b) -> sprintf "and_not_or(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_or_undef (z, s, a) -> sprintf "or_undef(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_or_same (z, s, a) -> sprintf "or_same(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_or_zero (z, s, a) -> sprintf "or_zero(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_or_mone (z, s, a) -> sprintf "or_mone(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_or_not (z, y, s, x) -> sprintf "or_not(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x)
  | Coq_rule_or_and (z, y, s, x, a) -> sprintf "or_and(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x) (string_of_value_ext a)
  | Coq_rule_xor_zero (z, s, a) -> sprintf "xor_zero(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_xor_same (z, s, a) -> sprintf "xor_same(%s, %s, %s)" (string_of_id_ext z) (string_of_int s) (string_of_value_ext a)
  | Coq_rule_xor_commutative (z, sz, x, y) -> sprintf "xor_commutative(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_int sz) (string_of_value_ext x) (string_of_value_ext y)
  | Coq_rule_xor_not (z, y, s, x) -> sprintf "xor_not(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext x)
  | Coq_rule_zext_trunc_and (z, y, x, a, s1, s2, c) -> sprintf "zext_trunc_and(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_id_ext x) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_APInt c)
  | Coq_rule_zext_trunc_and_xor (z, y, x, w, w', a, s1, s2, c) -> sprintf "zext_trunc_and_xor(%s, %s, %s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_id_ext x) (string_of_id_ext w) (string_of_id_ext w') (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_APInt c)
  | Coq_rule_zext_xor (z, y, y', a, s) -> sprintf "zext_xor(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_id_ext y') (string_of_value_ext a) (string_of_int s)
  | Coq_rule_sext_trunc (z, y, y', a, s1, s2, n) -> sprintf "sext_trunc(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_id_ext y') (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_APInt n)
  | Coq_rule_trunc_trunc (z, y, a, s1, s2, s3) -> sprintf "trunc_trunc(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_trunc_zext1 (z, y, a, s1, s2) -> sprintf "trunc_zext1(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2)
  | Coq_rule_trunc_zext2 (z, y, a, s1, s2, s3) -> sprintf "trunc_zext2(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_trunc_zext3 (z, y, a, s1, s2, s3) -> sprintf "trunc_zext3(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_trunc_sext1 (z, y, a, s1, s2) -> sprintf "trunc_sext1(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2)
  | Coq_rule_trunc_sext2 (z, y, a, s1, s2, s3) -> sprintf "trunc_sext2(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_trunc_sext3 (z, y, a, s1, s2, s3) -> sprintf "trunc_sext3(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_zext_zext (z, y, a, s1, s2, s3) -> sprintf "zext_zext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_sext_zext (z, y, a, s1, s2, s3) -> sprintf "sext_zext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_sext_sext (z, y, a, s1, s2, s3) -> sprintf "sext_sext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_int s1) (string_of_int s2) (string_of_int s3)
  | Coq_rule_fptoui_fpext (z, y, a, t1, t2, t3) -> sprintf "fptoui_fpext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_fptosi_fpext (z, y, a, t1, t2, t3) -> sprintf "fptosi_fpext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_uitofp_zext (z, y, a, t1, t2, t3) -> sprintf "uitofp_zext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_sitofp_sext (z, y, a, t1, t2, t3) -> sprintf "sitofp_sext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_fptrunc_fptrunc (z, y, a, t1, t2, t3) -> sprintf "fptrunc_fptrunc(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_fptrunc_fpext (z, y, a, t1, t2) -> sprintf "fptrunc_fpext(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2)
  | Coq_rule_fpext_fpext (z, y, a, t1, t2, t3) -> sprintf "fpext_fpext(%s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)
  | Coq_rule_cmp_swap_ult (z, a, b, t) -> sprintf "cmp_swap_ult(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_ugt (z, a, b, t) -> sprintf "cmp_swap_ugt(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_ule (z, a, b, t) -> sprintf "cmp_swap_ule(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_uge (z, a, b, t) -> sprintf "cmp_swap_uge(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_slt (z, a, b, t) -> sprintf "cmp_swap_slt(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_sgt (z, a, b, t) -> sprintf "cmp_swap_sgt(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_sle (z, a, b, t) -> sprintf "cmp_swap_sle(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_sge (z, a, b, t) -> sprintf "cmp_swap_sge(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_eq (z, a, b, t) -> sprintf "cmp_swap_eq(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_swap_ne (z, a, b, t) -> sprintf "cmp_swap_ne(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_value_ext a) (string_of_value_ext b) (string_of_typ t)
  | Coq_rule_cmp_slt_onebit (z, y, a, b) -> sprintf "cmp_slt_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_sgt_onebit (z, y, a, b) -> sprintf "cmp_sgt_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ugt_onebit (z, y, a, b) -> sprintf "cmp_ugt_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ule_onebit (z, y, a, b) -> sprintf "cmp_ule_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_uge_onebit (z, y, a, b) -> sprintf "cmp_uge_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_sle_onebit (z, y, a, b) -> sprintf "cmp_sle_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_sge_onebit (z, y, a, b) -> sprintf "cmp_sge_onebit(%s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_eq_sub (z, y, s, a, b) -> sprintf "cmp_eq_sub(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ne_sub (z, y, s, a, b) -> sprintf "cmp_ne_sub(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_eq_srem (z, y, s, a, b) -> sprintf "cmp_eq_srem(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_eq_srem2 (z, y, s, a, b) -> sprintf "cmp_eq_srem2(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ne_srem (z, y, s, a, b) -> sprintf "cmp_ne_srem(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_ne_srem2 (z, y, s, a, b) -> sprintf "cmp_ne_srem2(%s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b)
  | Coq_rule_cmp_eq_xor (z, x, y, s, a, b, c) -> sprintf "cmp_eq_xor(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b) (string_of_value_ext c)
  | Coq_rule_cmp_ne_xor (z, x, y, s, a, b, c) -> sprintf "cmp_ne_xor(%s, %s, %s, %s, %s, %s, %s)" (string_of_id_ext z) (string_of_id_ext x) (string_of_id_ext y) (string_of_int s) (string_of_value_ext a) (string_of_value_ext b) (string_of_value_ext c)
(* NOTE: Add here to add a new rule *)

and string_of_atoms atoms =
  "(" ^
    (AtomSetImpl.fold
       (fun atom acc -> atom ^ ", " ^ acc)
       atoms
       ")")
and string_of_atom_exts (atoms:IdExtSetImpl.t) =
  "(" ^
    (IdExtSetImpl.fold
       (fun atom acc -> (string_of_id_ext atom) ^ ", " ^ acc)
       atoms
       ")")

and string_of_value_exts (values:ValueExtSetImpl.t) =
  "(" ^
    (ValueExtSetImpl.fold
       (fun value acc -> (string_of_value_ext value) ^ ", " ^ acc)
       values
       ")")

and string_of_equations ?(indent=0) eqs =
  (String.make indent ' ') ^ (string_of_eq_regs eqs.eqs_eq_reg) ^ "\n"
  ^ (String.make indent ' ') ^ (string_of_eq_heaps eqs.eqs_eq_heap) ^ "\n"
  ^ (String.make indent ' ') ^ (string_of_neq_regs eqs.eqs_neq_reg) ^ "\n"

and string_of_eq_regs (eqs:EqRegSetImpl.t) =
  "(" ^
    (EqRegSetImpl.fold
       (fun eq acc -> (string_of_eq_reg eq) ^ ", " ^ acc)
       eqs
       ")")

and string_of_eq_reg (lhs, rhs) =
  (string_of_id_ext lhs)
  ^ " = "
  ^ (string_of_rhs_ext rhs)

and string_of_eq_heaps (eqs:EqHeapSetImpl.t) =
  "(" ^
    (EqHeapSetImpl.fold
       (fun eq acc -> (string_of_eq_heap eq) ^ ", " ^ acc)
       eqs
       ")")

and string_of_eq_heap (((lhs, t), a), rhs) =
  sprintf "*(%s:%s(%s)) = %s" (string_of_value_ext lhs) (string_of_typ t) (string_of_int a) (string_of_value_ext rhs)
    
and string_of_neq_regs (neqs:NeqRegSetImpl.t) =
  "(" ^
    (NeqRegSetImpl.fold
       (fun neq acc -> (string_of_neq_reg neq) ^ ", " ^ acc)
       neqs
       ")")

and string_of_neq_reg (lhs, rhs) =
  (string_of_id_ext lhs)
  ^ " <> "
  ^ (string_of_localglobal rhs)

and string_of_localglobal lg =
  match lg with
  | Datatypes.Coq_inl l ->
    (string_of_id_ext l)
  | Datatypes.Coq_inr v ->
    "*" ^ (v)

and string_of_insn insn =
  match insn with
  | LLVMsyntax.Coq_insn_phinode p -> string_of_phi p
  | LLVMsyntax.Coq_insn_cmd c -> string_of_cmd c
  | LLVMsyntax.Coq_insn_terminator t -> string_of_terminator t

and string_of_value = Coq_pretty_printer.string_of_value
and string_of_const = Coq_pretty_printer.string_of_constant

and string_of_terminator i =
  match i with 
  | LLVMsyntax.Coq_insn_br (id, v, l1, l2) -> 
    sprintf "  %s = br %s %s %s" id (string_of_value v) l1 l2
  | LLVMsyntax.Coq_insn_br_uncond (id, l) -> 
    sprintf "  %s = br %s " id l
  | LLVMsyntax.Coq_insn_return (id, t, v) ->
    sprintf "  %s = ret %s %s" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_return_void id ->
    sprintf "  %s = ret void" id
  | LLVMsyntax.Coq_insn_unreachable id -> 
    sprintf "  %s = unreachable" id

and string_of_cmd_opt i =
  match i with
  | None -> "None"
  | Some i -> string_of_cmd i

and string_of_cmd i =
  match i with
  | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) ->
    sprintf "%s = %s i%d %s %s" id (string_of_bop bop) sz 
      (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_fbop (id, fbop, fp, v1, v2) ->
    sprintf "%s = %s %s %s %s" id (string_of_fbop fbop) 
      (string_of_floating_point fp) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs, t') ->
    sprintf "%s = extractvalue %s %s %s %s" id (string_of_typ t) 
      (string_of_value v) (string_of_list_constant cs) (string_of_typ t') 
  | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) ->
    sprintf "%s = insertvalue %s %s %s %s %s" id (string_of_typ t1) 
      (string_of_value v1) (string_of_typ t2) (string_of_value v2) 
      (string_of_list_constant cs)
  | LLVMsyntax.Coq_insn_malloc (id, t, v, align) ->
    sprintf "%s = malloc %s %s %d" id (string_of_typ t) (string_of_value v)
      align
  | LLVMsyntax.Coq_insn_alloca (id, t, v, align) ->
    sprintf "%s = alloca %s %s %d" id (string_of_typ t) (string_of_value v)
      align
  | LLVMsyntax.Coq_insn_free (id, t, v) ->
    sprintf "%s = free %s %s" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_load (id, t, v, a) ->
    sprintf "%s = load %s* %s %d" id (string_of_typ t) (string_of_value v) 
      a
  | LLVMsyntax.Coq_insn_store (id, t, v1, v2, a) ->
    sprintf "%s = store %s %s %s %d" id (string_of_typ t) 
      (string_of_value v1) (string_of_value v2) a
  | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs, t') ->
    sprintf "%s = gep %s %s %s %s %s" id (string_of_bool inbounds) 
      (string_of_typ t) (string_of_value v) (string_of_list_value vs)
      (string_of_typ t') 
  | LLVMsyntax.Coq_insn_trunc (id, truncop, t1, v, t2) ->
    sprintf "%s = %s %s %s %s" id (string_of_truncop truncop) 
      (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) ->
    sprintf "%s = %s %s %s %s" id (string_of_extop extop) 
      (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) ->
    sprintf "%s = %s %s %s %s" id (string_of_castop castop) 
      (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) ->
    sprintf "%s = icmp %s %s %s %s" id (string_of_cond cond) 
      (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_fcmp (id, fcond, fp, v1, v2) ->
    sprintf "%s = fcmp %s %s %s %s" id (string_of_fcond fcond) 
      (string_of_floating_point fp) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) ->
    sprintf "%s = select %s %s %s %s" id (string_of_value v) 
      (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_call (id, noret, 
                              LLVMsyntax.Coq_clattrs_intro (tailc, cc, ra, ca), t, va, fv, ps) ->
    sprintf "%s = call %s %s %s %s %s %s" id (string_of_bool noret) 
      (string_of_bool tailc) (string_of_typ t) (string_of_varg va)
      (string_of_value fv) (string_of_params ps)
      
and string_of_rhs_ext i =
  match i with
  | Coq_rhs_ext_bop (bop, sz, v1, v2) ->
    sprintf "%s i%d %s %s" (string_of_bop bop) sz 
      (string_of_value_ext v1) (string_of_value_ext v2)
  | Coq_rhs_ext_fbop (fbop, fp, v1, v2) ->
    sprintf "%s %s %s %s" (string_of_fbop fbop) 
      (string_of_floating_point fp) (string_of_value_ext v1) (string_of_value_ext v2)
  | Coq_rhs_ext_extractvalue (t, v, cs, t') ->
    sprintf "extractvalue %s %s %s %s" (string_of_typ t) 
      (string_of_value_ext v) (string_of_list_constant cs) (string_of_typ t') 
  | Coq_rhs_ext_insertvalue (t1, v1, t2, v2, cs) ->
    sprintf "insertvalue %s %s %s %s %s" (string_of_typ t1) 
      (string_of_value_ext v1) (string_of_typ t2) (string_of_value_ext v2) 
      (string_of_list_constant cs)
  | Coq_rhs_ext_gep (inbounds, t, v, vs, t') ->
    sprintf "gep %s %s %s %s %s" (string_of_bool inbounds) 
      (string_of_typ t) (string_of_value_ext v) (string_of_list_value_ext vs)
      (string_of_typ t') 
  | Coq_rhs_ext_trunc (truncop, t1, v, t2) ->
    sprintf "%s %s %s %s" (string_of_truncop truncop) 
      (string_of_typ t1) (string_of_value_ext v) (string_of_typ t2)
  | Coq_rhs_ext_ext (extop, t1, v, t2) ->
    sprintf "%s %s %s %s" (string_of_extop extop) 
      (string_of_typ t1) (string_of_value_ext v) (string_of_typ t2)
  | Coq_rhs_ext_cast (castop, t1, v, t2) ->
    sprintf "%s %s %s %s" (string_of_castop castop) 
      (string_of_typ t1) (string_of_value_ext v) (string_of_typ t2)
  | Coq_rhs_ext_icmp (cond, t, v1, v2) ->
    sprintf "icmp %s %s %s %s" (string_of_cond cond) 
      (string_of_typ t) (string_of_value_ext v1) (string_of_value_ext v2)
  | Coq_rhs_ext_fcmp (fcond, fp, v1, v2) ->
    sprintf "fcmp %s %s %s %s" (string_of_fcond fcond) 
      (string_of_floating_point fp) (string_of_value_ext v1) (string_of_value_ext v2)
  | Coq_rhs_ext_select (v, t, v1, v2) ->
    sprintf "select %s %s %s %s" (string_of_value_ext v) 
      (string_of_typ t) (string_of_value_ext v1) (string_of_value_ext v2)
  | Coq_rhs_ext_value v ->
    sprintf "value %s" (string_of_value_ext v)
  | Coq_rhs_ext_old_alloca ->
    sprintf "old_alloca"
(*  | Coq_rhs_ext_new_alloca ->
    sprintf "new_alloca"*)

and string_of_value_ext v =
  match v with
  | Coq_value_ext_id id -> string_of_id_ext id
  | Coq_value_ext_const c -> string_of_constant c

and string_of_list_value_ext vs =
  match vs with
  | [] -> ""
  | (sz0, v)::vs' -> 
     "i"^(string_of_int sz0)^" "^(string_of_value_ext v)^", "^
       (string_of_list_value_ext vs')

and string_of_phi i =
  match i with
  | LLVMsyntax.Coq_insn_phi (id, t, list_v_l) -> 
     sprintf "%s = phi %s %s" id (string_of_typ t) 
             (string_of_list_value_l list_v_l)

and string_of_id_ext (var, n) =
  var
  ^ (match n with
     | Coq_ntag_new -> ""
     | Coq_ntag_old -> "|o")

and string_of_params_ext ps =
  match ps with
  | [] -> ""
  | ((t, _), v)::ps' -> 
     "("^(string_of_typ t)^","^(string_of_value_ext v)^")"^(string_of_params_ext ps')

and string_of_rhint_block_pos pos =
  match pos with
  | PhinodePos -> "phi"
  | CommandPos n -> string_of_int n
  | TerminatorPos -> "term"
  | UnspecifiedPos -> "block"
