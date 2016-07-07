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
  | CoreHint_t.AddCommutativeTgt (args:CoreHint_t.add_commutative_tgt) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_commutative_tgt (z, x, y, sz)
  | CoreHint_t.AddOnebit (args:CoreHint_t.add_onebit) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     Infrule.Coq_add_onebit (z, x, y)
  | CoreHint_t.AddOrAnd (args:CoreHint_t.add_or_and) ->
     let z = Convert.register args.z in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_or_and (z, a, b, x, y, sz)
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
  | CoreHint_t.AddXorAnd (args:CoreHint_t.add_xor_and) ->
     let z = Convert.register args.z in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_add_xor_and (z, a, b, x, y, sz)
  | CoreHint_t.AndCommutative (args:CoreHint_t.and_commutative) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_commutative (z, x, y, sz)
  | CoreHint_t.AndDeMorgan (args:CoreHint_t.and_de_morgan) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let zprime = Convert.register args.zprime in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_de_morgan (z, x, y, zprime, a, b, sz)
  | CoreHint_t.AndMone (args:CoreHint_t.and_mone) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_mone (z, x, sz)
  | CoreHint_t.AndNot (args:CoreHint_t.and_not) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_not (z, x, y, sz)
  | CoreHint_t.AndOr (args:CoreHint_t.and_or) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_or (z, x, y, a, sz)
  | CoreHint_t.AndSame (args:CoreHint_t.and_same) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_same (z, x, sz)
  | CoreHint_t.AndUndef (args:CoreHint_t.and_undef) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_undef (z, x, sz)
  | CoreHint_t.AndZero (args:CoreHint_t.and_zero) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_and_zero (z, x, sz)
  | CoreHint_t.BitcastBitcast (args:CoreHint_t.bitcast_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastLoad (args:CoreHint_t.bitcast_load) -> 
     let ptr = Convert.value args.ptr in
     let ptrty = Convert.value_type args.ptrty in
     let v1 = Convert.value args.v1 in
     let ptrty2 = Convert.value_type args.ptrty2 in
     let v2 = Convert.value args.v2 in
     let a = Convert.size args.a in 
     Infrule.Coq_bitcast_load (ptr, ptrty, v1, ptrty2, v2, a)
  | CoreHint_t.BitcastFpext (args:CoreHint_t.bitcast_fpext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_fpext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastFptosi (args:CoreHint_t.bitcast_fptosi) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_fptosi (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastFptoui (args:CoreHint_t.bitcast_fptoui) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_fptoui (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastFptrunc (args:CoreHint_t.bitcast_fptrunc) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_fptrunc (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastInttoptr (args:CoreHint_t.bitcast_inttoptr) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_inttoptr (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastPtrtoint (args:CoreHint_t.bitcast_ptrtoint) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_ptrtoint (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastSext (args:CoreHint_t.bitcast_sext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_sext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastSametype (args:CoreHint_t.bitcast_sametype) -> 
     let src = Convert.value args.src in
     let dst = Convert.value args.dst in
     let tty = Convert.value_type args.tty in
     Infrule.Coq_bitcast_sametype (src, dst, tty)
  | CoreHint_t.BitcastSitofp (args:CoreHint_t.bitcast_sitofp) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_sitofp (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastTrunc (args:CoreHint_t.bitcast_trunc) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_trunc (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastUitofp (args:CoreHint_t.bitcast_uitofp) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_uitofp (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.BitcastZext (args:CoreHint_t.bitcast_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_bitcast_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.Bitcastptr (args:CoreHint_t.bitcastptr) ->
     let v = Convert.value args.v in
     let vprime = Convert.value args.vprime in
     let bitcastinst = Convert.expr args.bitcastinst src_fdef tgt_fdef in
     Infrule.Coq_bitcastptr (v, vprime, bitcastinst)
  | CoreHint_t.BopDistributiveOverSelectinst (args:CoreHint_t.bop_distributive_over_selectinst) ->
     let opcode = Convert.bop args.opcode in
     let r = Convert.register args.r in
     let s = Convert.register args.s in
     let t' = Convert.register args.tprime in
     let t0 = Convert.register args.t0 in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let z = Convert.value args.z in
     let c = Convert.value args.c in
     let bopsz = Convert.size args.bopsz in
     let selty = Convert.value_type args.selty in
     Infrule.Coq_bop_distributive_over_selectinst (opcode, r, s, t', t0, x, y, z, c, bopsz, selty)
  | CoreHint_t.BopDistributiveOverSelectinst2 (args:CoreHint_t.bop_distributive_over_selectinst2) ->
     let opcode = Convert.bop args.opcode in
     let r = Convert.register args.r in
     let s = Convert.register args.s in
     let t' = Convert.register args.tprime in
     let t0 = Convert.register args.t0 in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let z = Convert.value args.z in
     let c = Convert.value args.c in
     let bopsz = Convert.size args.bopsz in
     let selty = Convert.value_type args.selty in
     Infrule.Coq_bop_distributive_over_selectinst2 (opcode, r, s, t', t0, x, y, z, c, bopsz, selty)
  | CoreHint_t.FaddCommutativeTgt (args:CoreHint_t.fadd_commutative_tgt) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let fty = Convert.float_type args.fty in
     Infrule.Coq_fadd_commutative_tgt (z, x, y, fty)
  | CoreHint_t.FbopDistributiveOverSelectinst (args:CoreHint_t.fbop_distributive_over_selectinst) ->
     let fopcode = Convert.fbop args.fopcode in
     let r = Convert.register args.r in
     let s = Convert.register args.s in
     let t' = Convert.register args.tprime in
     let t0 = Convert.register args.t0 in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let z = Convert.value args.z in
     let c = Convert.value args.c in
     let fbopty = Convert.float_type args.fbopty in
     let selty = Convert.value_type args.selty in
     Infrule.Coq_fbop_distributive_over_selectinst (fopcode, r, s, t', t0, x, y, z, c, fbopty, selty)
  | CoreHint_t.FbopDistributiveOverSelectinst2 (args:CoreHint_t.fbop_distributive_over_selectinst2) ->
     let fopcode = Convert.fbop args.fopcode in
     let r = Convert.register args.r in
     let s = Convert.register args.s in
     let t' = Convert.register args.tprime in
     let t0 = Convert.register args.t0 in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let z = Convert.value args.z in
     let c = Convert.value args.c in
     let fbopty = Convert.float_type args.fbopty in
     let selty = Convert.value_type args.selty in
     Infrule.Coq_fbop_distributive_over_selectinst2 (fopcode, r, s, t', t0, x, y, z, c, fbopty, selty)
  | CoreHint_t.FpextBitcast (args:CoreHint_t.fpext_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fpext_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FpextFpext (args:CoreHint_t.fpext_fpext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fpext_fpext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptosiBitcast (args:CoreHint_t.fptosi_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptosi_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptouiBitcast (args:CoreHint_t.fptoui_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptoui_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptosiFpext (args:CoreHint_t.fptosi_fpext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptosi_fpext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptouiFpext (args:CoreHint_t.fptoui_fpext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptoui_fpext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptruncBitcast (args:CoreHint_t.fptrunc_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptrunc_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.FptruncFpext (args:CoreHint_t.fptrunc_fpext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_fptrunc_fpext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.Gepzero (args:CoreHint_t.gepzero) ->
     let v = Convert.value args.v in
     let vprime = Convert.value args.vprime in
     let gepinst = Convert.expr args.gepinst src_fdef tgt_fdef in
     Infrule.Coq_gepzero (v, vprime, gepinst)
  | CoreHint_t.GepInboundsRemove (args:CoreHint_t.gep_inbounds_remove) ->
     let gepinst = Convert.expr args.gepinst src_fdef tgt_fdef in
     Infrule.Coq_gep_inbounds_remove (gepinst)
  | CoreHint_t.InttoptrLoad (args:CoreHint_t.inttoptr_load) -> 
     let ptr = Convert.value args.ptr in
     let intty = Convert.value_type args.intty in
     let v1 = Convert.value args.v1 in
     let ptrty = Convert.value_type args.ptrty in
     let v2 = Convert.value args.v2 in
     let a = Convert.size args.a in
     Infrule.Coq_inttoptr_load (ptr, intty, v1, ptrty, v2, a)
  | CoreHint_t.InttoptrBitcast (args:CoreHint_t.inttoptr_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_inttoptr_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.InttoptrPtrtoint (args:CoreHint_t.inttoptr_ptrtoint) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_inttoptr_ptrtoint (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.InttoptrZext (args:CoreHint_t.inttoptr_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_inttoptr_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.OrAnd (args:CoreHint_t.or_and) -> 
     let z = Convert.value args.z in
     let y = Convert.value args.y in
     let x = Convert.value args.x in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_and (z, y, x, a, sz)
  | CoreHint_t.OrAndXor (args:CoreHint_t.or_and_xor) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_and_xor (z, x, y, a, b, sz)
  | CoreHint_t.LessthanUndef (args:CoreHint_t.lessthan_undef) ->
     let ty = Convert.value_type args.ty in
     let v = Convert.value args.v in
     Infrule.Coq_lessthan_undef (ty, v)
  | CoreHint_t.OrCommutative (args:CoreHint_t.or_commutative) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_commutative (z, x, y, sz)
  | CoreHint_t.OrCommutativeTgt (args:CoreHint_t.or_commutative_tgt) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_commutative_tgt (z, x, y, sz)
  | CoreHint_t.OrMone (args:CoreHint_t.or_mone) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_mone (z, a, sz)
  | CoreHint_t.OrNot (args:CoreHint_t.or_not) -> 
     let z = Convert.value args.z in
     let y = Convert.value args.y in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_not (z, y, x, sz)
  | CoreHint_t.OrOr (args:CoreHint_t.or_or) ->
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_or (z, x, y, a, b, sz)
  | CoreHint_t.OrOr2 (args:CoreHint_t.or_or2) ->
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let yprime = Convert.value args.yprime in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_or2 (z, x, y, yprime, a, b, sz)
  | CoreHint_t.OrUndef (args:CoreHint_t.or_undef) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_undef (z, a, sz)
  | CoreHint_t.OrSame (args:CoreHint_t.or_same) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_same (z, a, sz)
  | CoreHint_t.OrXor (args:CoreHint_t.or_xor) ->
     let w = Convert.value args.w in
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_xor (w, z, x, y, a, b, sz)
  | CoreHint_t.OrXor2 (args:CoreHint_t.or_xor2) ->
     let z = Convert.value args.z in
     let x1 = Convert.value args.x1 in
     let y1 = Convert.value args.y1 in
     let x2 = Convert.value args.x2 in
     let y2 = Convert.value args.y2 in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_xor2 (z, x1, y1, x2, y2, a, b, sz)
  | CoreHint_t.OrXor3 (args:CoreHint_t.or_xor3) -> 
     let z = Convert.value args.z in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_xor3 (z, y, a, b, sz)
  | CoreHint_t.OrXor4 (args:CoreHint_t.or_xor4) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let nb = Convert.value args.nb in
     let sz = Convert.size args.sz in
     Infrule.Coq_or_xor4 (z, x, y, a, b, nb, sz)
  | CoreHint_t.OrZero (args:CoreHint_t.or_zero) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let sz = Convert.size args.sz in
    Infrule.Coq_or_zero (z, a, sz)
  | CoreHint_t.PtrtointBitcast (args:CoreHint_t.ptrtoint_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_ptrtoint_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.PtrtointLoad (args:CoreHint_t.ptrtoint_load) -> 
     let ptr = Convert.value args.ptr in
     let ptrty = Convert.value_type args.ptrty in
     let v1 = Convert.value args.v1 in
     let intty = Convert.value_type args.intty in
     let v2 = Convert.value args.v2 in
     let a = Convert.size args.a in
     Infrule.Coq_ptrtoint_load (ptr, ptrty, v1, intty, v2, a)
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
  | CoreHint_t.RemNeg (args:CoreHint_t.rem_neg) ->
     let z = Convert.register args.z in
     let my = Convert.value args.my in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_rem_neg (z, my, x, y, sz)
  | CoreHint_t.SdivMone (args:CoreHint_t.sdiv_mone) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let sz = Convert.size args.sz in
     Infrule.Coq_sdiv_mone (z, x, sz)
  | CoreHint_t.SextBitcast (args:CoreHint_t.sext_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sext_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SextSext (args:CoreHint_t.sext_sext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sext_sext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SextZext (args:CoreHint_t.sext_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sext_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SdivSubSrem (args:CoreHint_t.sdiv_sub_srem) ->
     let z = Convert.register args.z in
     let b = Convert.register args.b in
     let a = Convert.register args.a in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_sdiv_sub_srem (z, b, a, x, y, sz)
  | CoreHint_t.SitofpBitcast (args:CoreHint_t.sitofp_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sitofp_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SitofpSext (args:CoreHint_t.sitofp_sext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sitofp_sext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SitofpZext (args:CoreHint_t.sitofp_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_sitofp_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.SubAdd (args:CoreHint_t.sub_add) ->
     let z = Convert.register args.z in
     let my = Convert.value args.my in
     let x = Convert.register args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_add (z, my, x, y, sz)
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
  | CoreHint_t.SubOrXor (args:CoreHint_t.sub_or_xor) ->
     let z = Convert.register args.z in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_or_xor (z, a, b, x, y, sz)
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
  | CoreHint_t.SubSub (args:CoreHint_t.sub_sub) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let w = Convert.value args.w in
     let sz = Convert.size args.sz in
     Infrule.Coq_sub_sub (z, x, y, w, sz)
  | CoreHint_t.Transitivity (args:CoreHint_t.transitivity) ->
      let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
      let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
      let e3 = Convert.expr args.e3 src_fdef tgt_fdef in
      Infrule.Coq_transitivity (e1, e2, e3)
  | CoreHint_t.TransitivityTgt (args:CoreHint_t.transitivity_tgt) ->
      let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
      let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
      let e3 = Convert.expr args.e3 src_fdef tgt_fdef in
      Infrule.Coq_transitivity_tgt (e1, e2, e3)
  | CoreHint_t.UdivSubUrem (args:CoreHint_t.udiv_sub_urem) ->
     let z = Convert.register args.z in
     let b = Convert.register args.b in
     let a = Convert.register args.a in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_udiv_sub_urem (z, b, a, x, y, sz)
  | CoreHint_t.DiffblockGlobalAlloca (args:CoreHint_t.diffblock_global_alloca) ->
     let x = Convert.constant args.gx in
     let y = Convert.register args.y in
     Infrule.Coq_diffblock_global_alloca (x, y)
  | CoreHint_t.DiffblockGlobalGlobal (args:CoreHint_t.diffblock_global_global) ->
     let gx = Convert.constant args.gx in
     let gy = Convert.constant args.gy in
     Infrule.Coq_diffblock_global_global (gx, gy)
  | CoreHint_t.DiffblockLessthan (args:CoreHint_t.diffblock_lessthan) ->
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let xprime = Convert.value args.xprime in
     let yprime = Convert.value args.yprime in
     Infrule.Coq_diffblock_lessthan (x, y, xprime, yprime)
  | CoreHint_t.DiffblockNoalias (args:CoreHint_t.diffblock_noalias) ->
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let xprime = Convert.pointer args.xprime in
     let yprime = Convert.pointer args.yprime in
     Infrule.Coq_diffblock_noalias (x, y, xprime, yprime)
  | CoreHint_t.TransitivityPointerLhs (args:CoreHint_t.transitivity_pointer_lhs) ->
     let p = Convert.value args.p in
     let q = Convert.value args.q in
     let v = Convert.value args.v in
     let typ = Convert.value_type args.typ in
     let align = Convert.size args.align in
     Infrule.Coq_transitivity_pointer_lhs (p, q, v, typ, align)
  | CoreHint_t.TransitivityPointerRhs (args:CoreHint_t.transitivity_pointer_rhs) ->
     let p = Convert.value args.p in
     let q = Convert.value args.q in
     let v = Convert.value args.v in
     let typ = Convert.value_type args.typ in
     let align = Convert.size args.align in
     Infrule.Coq_transitivity_pointer_rhs (p, q, v, typ, align)
  | CoreHint_t.Substitute (args:CoreHint_t.substitute) ->
     let x = Convert.register args.x in
     let y = Convert.value args.y in
     let e = Convert.expr args.e src_fdef tgt_fdef in
     Infrule.Coq_substitute (x, y, e)
  | CoreHint_t.SubstituteRev (args:CoreHint_t.substitute_rev) ->
     let x = Convert.register args.x in
     let y = Convert.value args.y in
     let e = Convert.expr args.e src_fdef tgt_fdef in
     Infrule.Coq_substitute_rev (x, y, e)
  | CoreHint_t.ReplaceRhs (args:CoreHint_t.replace_rhs) ->
      let x = Convert.register args.x in
      let y = Convert.value args.y in
      let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
      let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
      let e2' = Convert.expr args.e2' src_fdef tgt_fdef in
      Infrule.Coq_replace_rhs (x, y, e1, e2, e2')
  | CoreHint_t.ReplaceRhsOpt (args:CoreHint_t.replace_rhs_opt) ->
      let x = Convert.register args.x in
      let y = Convert.value args.y in
      let e1 = Convert.expr args.e1 src_fdef tgt_fdef in
      let e2 = Convert.expr args.e2 src_fdef tgt_fdef in
      let e2' = Convert.expr args.e2' src_fdef tgt_fdef in
      Infrule.Coq_replace_rhs_opt (x, y, e1, e2, e2')
  | CoreHint_t.TruncBitcast (args:CoreHint_t.trunc_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_trunc_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.TruncOnebit (args:CoreHint_t.trunc_onebit) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let orgsz = Convert.size args.orgsz in
     Infrule.Coq_trunc_onebit (z, x, y, orgsz)
  | CoreHint_t.TruncPtrtoint (args:CoreHint_t.trunc_ptrtoint) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_trunc_ptrtoint (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.TruncSext (args:CoreHint_t.trunc_sext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_trunc_sext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.TruncTrunc (args:CoreHint_t.trunc_trunc) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_trunc_trunc (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.TruncZext (args:CoreHint_t.trunc_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_trunc_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.UdivZext (args:CoreHint_t.udiv_zext) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let k = Convert.register args.k in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz1 = Convert.size args.sz1 in
     let sz2 = Convert.size args.sz2 in
     Infrule.Coq_udiv_zext (z, x, y, k, a, b, sz1, sz2)
  | CoreHint_t.UitofpBitcast (args:CoreHint_t.uitofp_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_uitofp_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.UitofpZext (args:CoreHint_t.uitofp_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_uitofp_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.UremZext (args:CoreHint_t.urem_zext) ->
     let z = Convert.register args.z in
     let x = Convert.register args.x in
     let y = Convert.register args.y in
     let k = Convert.register args.k in
     let a = Convert.value args.a in
     let b = Convert.value args.b in
     let sz1 = Convert.size args.sz1 in
     let sz2 = Convert.size args.sz2 in
     Infrule.Coq_urem_zext (z, x, y, k, a, b, sz1, sz2)
  | CoreHint_t.IntroGhost (args:CoreHint_t.intro_ghost) ->
      let x = Convert.expr args.x src_fdef tgt_fdef in
      let g = args.g.name in
      Infrule.Coq_intro_ghost (x, g)
  | CoreHint_t.IntroEq (args:CoreHint_t.intro_eq) ->
      let x = Convert.value args.x in
      Infrule.Coq_intro_eq x
  | CoreHint_t.IntroEqTgt (args:CoreHint_t.intro_eq_tgt) ->
      let x = Convert.value args.x in
      Infrule.Coq_intro_eq_tgt x
  | CoreHint_t.XorCommutative (args:CoreHint_t.xor_commutative) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_xor_commutative (z, x, y, sz)
  | CoreHint_t.XorCommutativeTgt (args:CoreHint_t.xor_commutative_tgt) ->
     let z = Convert.register args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let sz = Convert.size args.sz in
     Infrule.Coq_xor_commutative_tgt (z, x, y, sz)
  | CoreHint_t.XorNot (args:CoreHint_t.xor_not) -> 
     let z = Convert.value args.z in
     let y = Convert.value args.y in
     let x = Convert.value args.x in
     let s = Convert.size args.s in
     Infrule.Coq_xor_not (z, y, x, s)
  | CoreHint_t.XorSame (args:CoreHint_t.xor_same) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let s = Convert.size args.s in
     Infrule.Coq_xor_same (z, a, s)
  | CoreHint_t.XorUndef (args:CoreHint_t.xor_undef) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let s = Convert.size args.s in
     Infrule.Coq_xor_undef (z, a, s)
  | CoreHint_t.XorZero (args:CoreHint_t.xor_zero) -> 
     let z = Convert.value args.z in
     let a = Convert.value args.a in
     let s = Convert.size args.s in
     Infrule.Coq_xor_zero (z, a, s)
  | CoreHint_t.ZextBitcast (args:CoreHint_t.zext_bitcast) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_zext_bitcast (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.ZextTruncAnd (args:CoreHint_t.zext_trunc_and) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let w = Convert.value args.w in
     let c = Convert.constant args.c in
     let s = Convert.size args.s in
     let sprime = Convert.size args.sprime in
     Infrule.Coq_zext_trunc_and (z, x, y, w, c, s, sprime)
  | CoreHint_t.ZextTruncAndXor (args:CoreHint_t.zext_trunc_and_xor) -> 
     let z = Convert.value args.z in
     let x = Convert.value args.x in
     let v = Convert.value args.v in
     let w = Convert.value args.w in
     let y = Convert.value args.y in
     let yprime = Convert.value args.yprime in
     let c = Convert.constant args.c in
     let s = Convert.size args.s in
     let sprime = Convert.size args.sprime in
     Infrule.Coq_zext_trunc_and_xor (z, x, v, w, y, yprime, c, s, sprime)
  | CoreHint_t.ZextXor (args:CoreHint_t.zext_xor) -> 
     let z = Convert.value args.z in
     let y = Convert.value args.y in
     let yprime = Convert.value args.yprime in
     let x = Convert.value args.x in
     Infrule.Coq_zext_xor (z, y, yprime, x)
  | CoreHint_t.ZextZext (args:CoreHint_t.zext_zext) -> 
     let src = Convert.value args.src in
     let mid = Convert.value args.mid in
     let dst = Convert.value args.dst in
     let srcty = Convert.value_type args.srcty in
     let midty = Convert.value_type args.midty in
     let dstty = Convert.value_type args.dstty in
     Infrule.Coq_zext_zext (src, mid, dst, srcty, midty, dstty)
  | CoreHint_t.IcmpInverse (args:CoreHint_t.icmp_inverse) ->
     let c = Convert.cond args.predicate in
     let ty = Convert.value_type args.ty in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     let b = Convert.const_int args.boolean in
     Infrule.Coq_icmp_inverse (c, ty, x, y, b)
  | CoreHint_t.ImpliesFalse (args:CoreHint_t.implies_false) ->
     let c1 = Convert.constant args.c1 in
     let c2 = Convert.constant args.c2 in
     Infrule.Coq_implies_false(c1, c2)
  | CoreHint_t.IcmpEqSame (args:CoreHint_t.icmp_eq_same) ->
     let ty = Convert.value_type args.ty in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     Infrule.Coq_icmp_eq_same (ty, x, y)
  | CoreHint_t.IcmpNeqSame (args:CoreHint_t.icmp_neq_same) ->
     let ty = Convert.value_type args.ty in
     let x = Convert.value args.x in
     let y = Convert.value args.y in
     Infrule.Coq_icmp_neq_same (ty, x, y)
  | _ ->
     failwith "convert_infrule does not deal with this inferece rule"
