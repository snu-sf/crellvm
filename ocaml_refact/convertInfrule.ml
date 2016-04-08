(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open MetatheoryAtom
open Datatype_base
open Syntax
open BinInt
open BinPos
open Extraction_defs
open AddInfrule
open CoreHint_t
open ConvertUtil

let convert_infrule (infrule:CoreHint_t.infrule) (src_fdef:LLVMsyntax.fdef) (tgt_fdef:LLVMsyntax.fdef) : Infrule.t =
  match infrule with
  | CoreHint_t.AddAssociative (args:CoreHint_t.add_associative) ->
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let z = Convert.register args.z in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let c3 = Convert.const_int args.c3 in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_associative (x, y, z, c1, c2, c3, sz)
  | CoreHint_t.AddConstNot (args:CoreHint_t.add_const_not) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let x = Convert.value args.x in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_const_not (z,y,x,c1,c2,sz)
  | CoreHint_t.AddDistSub (args:CoreHint_t.add_dist_sub) ->
     let z = Convert.register args.z in
     let minusx = Convert.register args.minusx in
     let minusy = Convert.value args.minusy in
     let w = Convert.register args.w in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_dist_sub (z, minusx, minusy, w, x, y, sz)
  | CoreHint_t.AddMask (args:CoreHint_t.add_mask) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let y' = Convert.register args.yprime in
     let x = Convert.value args.x in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_mask(z,y,y',x,c1,c2,sz)
  | CoreHint_t.AddSub (args:CoreHint_t.add_sub) ->
     let z = Convert.register args.z in
     let minusy = Convert.register args.minusy in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_sub (z, minusy, x, y, sz)
  | CoreHint_t.AddCommutative (args:CoreHint_t.add_commutative) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_commutative (z, x, y, sz)
  | CoreHint_t.AddOnebit (args:CoreHint_t.add_onebit) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     Infrule.Coq_add_onebit (z, x, y)
  | CoreHint_t.AddSelectZero (args:CoreHint_t.add_select_zero) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let c = Convert.value args.c in
     let n = Convert.value args.n in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_select_zero (z, x, y, c, n, a, sz)
  | CoreHint_t.AddSelectZero2 (args:CoreHint_t.add_select_zero2) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let c = Convert.value args.c in
     let n = Convert.value args.n in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_select_zero2 (z, x, y, c, n, a, sz)
  | CoreHint_t.AddShift (args:CoreHint_t.add_shift) ->
     let y = Convert.register args.y in
     let v = Convert.value args.v in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_shift (y, v, sz)
  | CoreHint_t.AddSignbit (args:CoreHint_t.add_signbit) ->
     let x = Convert.register args.x in
     let e1 = Convert.value args.e1 in
     let e2 = Convert.value args.e2 in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_signbit (x, e1, e2, sz)
  | CoreHint_t.AddZextBool (args:CoreHint_t.add_zext_bool) ->
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let b = Convert.value args.b in
     let c = Convert.const_int args.c in
     let c' = Convert.const_int args.cprime in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_zext_bool (x, y, b, c, c', sz)
  | CoreHint_t.SdivSubSrem (args:CoreHint_t.sdiv_sub_srem) ->
     let z = Convert.register args.z in
     let b = Convert.register args.b in
     let a = Convert.register args.a in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_sdiv_sub_srem (z, b, a, x, y, sz)
  | CoreHint_t.UdivSubUrem (args:CoreHint_t.udiv_sub_urem) ->
     let z = Convert.register args.z in
     let b = Convert.register args.b in
     let a = Convert.register args.a in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_udiv_sub_urem (z, b, a, x, y, sz)
  | CoreHint_t.SubAdd (args:CoreHint_t.sub_add) ->
     let z = Convert.register args.z in
     let my = Convert.value args.my in
     let x = Convert.register args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_add (z, my, x, y, sz)
  | CoreHint_t.NegVal (args:CoreHint_t.neg_val) ->
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let sz = Convert.size args.sz in
     Infrule.Coq_neg_val (c1, c2, sz)
  | CoreHint_t.MulBool (args:CoreHint_t.mul_bool) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     Infrule.Coq_mul_bool (z, x, y) 
  | CoreHint_t.MulCommutative (args:CoreHint_t.mul_commutative) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_mul_commutative (z, x, y, sz)
  | CoreHint_t.MulNeg (args:CoreHint_t.mul_neg) ->
     let z = Convert.register args.z in
     let mx = Convert.value args.mx in
     let my = Convert.value args.my in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_mul_neg (z, mx, my, x, y, sz)
  | CoreHint_t.MulMone (args:CoreHint_t.mul_mone) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_mul_mone (z, x, sz)
  | CoreHint_t.MulShl (args:CoreHint_t.mul_shl) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let x = Convert.value args.x in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
     Infrule.Coq_mul_shl (z, y, x, a, sz);
  | CoreHint_t.SubConstAdd (args:CoreHint_t.sub_const_add) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let x = Convert.value args.x in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let c3 = Convert.const_int args.c3 in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_const_add (z, y, x, c1, c2, c3, sz)
  | CoreHint_t.SubConstNot (args:CoreHint_t.sub_const_not) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let x = Convert.value args.x in
     let c1 = Convert.const_int args.c1 in
     let c2 = Convert.const_int args.c2 in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_const_not (z, y, x, c1, c2, sz)
  | CoreHint_t.SubMone (args:CoreHint_t.sub_mone) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_mone (z, x, sz)
  | CoreHint_t.SubOnebit (args:CoreHint_t.sub_onebit) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     Infrule.Coq_sub_onebit (z, x, y)
  | CoreHint_t.SubRemove (args:CoreHint_t.sub_remove) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_remove (z, y, a, b, sz)
  | CoreHint_t.SubSdiv (args:CoreHint_t.sub_sdiv) ->
     let z = Convert.register args.z in
     let y = Convert.register args.y in
     let x = Convert.value args.x in
     let c = Convert.const_int args.c in
     let c' = Convert.const_int args.cprime in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_sdiv (z, y, x, c, c', sz)
  | CoreHint_t.SubShl (args:CoreHint_t.sub_shl) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.register args.y in
     let mx = Convert.value args.mx in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_shl (z, x, y, mx, a, sz)
  | CoreHint_t.Transitivity (args:CoreHint_t.transitivity) ->
     let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
     let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
     let e3 = Convert.expr args.e3 src_fdef tgt_fdef in
     Infrule.Coq_transitivity (e1, e2, e3)
  | CoreHint_t.NoaliasGlobalAlloca (args:CoreHint_t.noalias_global_alloca) ->
      let x = Convert.pointer args.x src_fdef in
      let y = Convert.pointer args.y src_fdef in
      Infrule.Coq_noalias_global_alloca (x, y)
  | CoreHint_t.TransitivityPointerLhs (args:CoreHint_t.transitivity_pointer_lhs) ->
     let p = Convert.value args.p in
     let q = Convert.value args.q in
     let v = Convert.value args.v in
     let loadq = Convert.expr args.loadq src_fdef tgt_fdef in
     (match loadq with
     | Exprs.Expr.Coq_load (vq, typ, align) ->
        (* We should assert that vq == q. *)
        Infrule.Coq_transitivity_pointer_lhs (p, q, v, typ, align)
     | _ -> failwith "loadq must be load instruction."
     )
  | CoreHint_t.TransitivityPointerRhs (args:CoreHint_t.transitivity_pointer_rhs) ->
     let p = Convert.value args.p in
     let q = Convert.value args.q in
     let v = Convert.value args.v in
     let loadp = Convert.expr args.loadp src_fdef tgt_fdef in
     (match loadp with
     | Exprs.Expr.Coq_load (vp, typ, align) ->
        (* We should assert that vp == p. *)
        Infrule.Coq_transitivity_pointer_rhs (p, q, v, typ, align)
     | _ -> failwith "loadq must be load instruction."
     )
  | CoreHint_t.ReplaceRhs (args:CoreHint_t.replace_rhs) ->
     let x = Convert.register args.x in
     let y = Convert.value args.y in
     let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
     let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
     let e2' = Convert.expr args.e2' src_fdef tgt_fdef in
     Infrule.Coq_replace_rhs (x, y, e1, e2, e2')
  | _ ->
     failwith "convert_infrule does not deal with this inferece rule"
