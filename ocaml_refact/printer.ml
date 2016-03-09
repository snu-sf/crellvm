open Exprs
open Hints
open Syntax
       
let out_channel = ref stdout

module ExprsToString = struct
    let tag (t:Tag.t): string =
      match t with
      | Tag.Coq_physical -> "Physical"
      | Tag.Coq_previous -> "Previous"
      | Tag.Coq_ghost -> "Ghost"
    
    let idT (idt:IdT.t): string =
      let (t, id) = idt in
      Printf.sprintf "( %s, %s )" (tag t) id

    let of_const (c:LLVMsyntax.const): string =
      "TODO"

    let valueT (vt:ValueT.t): string =
      match vt with
      | ValueT.Coq_id idt ->
         Printf.sprintf "(V_id %s)" (idT idt)
      | ValueT.Coq_const c ->
         Printf.sprintf "(V_const %s)" (of_const c)

    let of_sz (s:LLVMsyntax.sz): string =
      Printf.sprintf "(sz %d)" s

    let bop (b:LLVMsyntax.bop): string=
      match b with
      | LLVMsyntax.Coq_bop_add -> "add"
      | LLVMsyntax.Coq_bop_sub -> "sub"
      | LLVMsyntax.Coq_bop_mul -> "mul"
      | LLVMsyntax.Coq_bop_udiv -> "udiv"
      | LLVMsyntax.Coq_bop_sdiv -> "sdiv"
      | LLVMsyntax.Coq_bop_urem -> "urem"
      | LLVMsyntax.Coq_bop_srem -> "srem"
      | LLVMsyntax.Coq_bop_shl -> "shl"
      | LLVMsyntax.Coq_bop_lshr -> "lshr"
      | LLVMsyntax.Coq_bop_ashr -> "ashr"
      | LLVMsyntax.Coq_bop_and -> "and"
      | LLVMsyntax.Coq_bop_or -> "or"
      | LLVMsyntax.Coq_bop_xor -> "xor"

    let fbop (fb:LLVMsyntax.fbop): string = "TODO"

    let floating_point (fp:LLVMsyntax.floating_point): string =
      "TODO"
        
    let expr (e:Expr.t): string =
      match e with
      | Expr.Coq_bop (b, s, vt1, vt2) ->
         Printf.sprintf "bop %s %s %s %s"
                       (bop b) (of_sz s) (valueT vt1) (valueT vt2)
      | Expr.Coq_fbop (fb, fp, vt1, vt2) ->
         Printf.sprintf "fbop %s %s %s %s"
                        (fbop fb) (floating_point fp)
                        (valueT vt1) (valueT vt2)
      | Expr.Coq_value vt ->
         Printf.sprintf "value %s" (valueT vt)
      | _ -> "TODO"
         
         

  end

module PrintExprs = struct
    let exprPair (ep:ExprPair.t): unit =
      let (e1, e2) = ep in
      let s1 = ExprsToString.expr e1 in
      let s2 = ExprsToString.expr e2 in
      let _ = Printf.fprintf !out_channel "DEBUG: (%s, %s)\n" s1 s2 in
      ()

    let valueTPair (vp:ValueTPair.t): unit =
      let (v1, v2) = vp in
      let s1 = ExprsToString.valueT v1 in
      let s2 = ExprsToString.valueT v2 in
      let _ = Printf.fprintf !out_channel "DEBUG: (%s, %s)\n" s1 s2 in
      ()

    let idT (idt:IdT.t): unit =
      let s = ExprsToString.idT idt in
      let _ = Printf.fprintf !out_channel "DEBUG: %s\n" s in
      ()
    
    let exprPairSet (eps: ExprPairSet.t): unit =
       let _ = ExprPairSet.fold (fun ep _ -> exprPair ep) eps () in
       ()

    let valueTPairSet (vtps: ValueTPairSet.t): unit = 
       let _ = ValueTPairSet.fold (fun vtp _ -> valueTPair vtp) vtps () in
       ()

    let idTSet (idts: IdTSet.t): unit =
       let _ = IdTSet.fold (fun idt _ -> idT idt) idts () in
       ()

  end
                      
module PrintHints = struct
    let infrules_to_string (inf:Infrule.t): string =
      match inf with
      | Infrule.Coq_add_associative (x, y, z, c1, c2, c3, sz) ->
         "add_assoc"
      | _ -> "TODO"

    let infrules (infs:Infrule.t list): unit =
      List.map
        (fun inf ->
         let s = infrules_to_string inf in
         let _ = Printf.fprintf !out_channel "DEBUG: %s\n" s in
         ())
        infs;
      ()
    
    let unary (u:Invariant.unary): unit =
      let _ = Printf.fprintf !out_channel "DEBUG: lessdef\n" in
      let _ = PrintExprs.exprPairSet (u.Invariant.lessdef) in
      let _ = Printf.fprintf !out_channel "DEBUG: noalias\n" in
      let _ = PrintExprs.valueTPairSet (u.Invariant.noalias) in
      let _ = Printf.fprintf !out_channel "DEBUG: allocas\n" in
      let _ = PrintExprs.idTSet (u.Invariant.allocas) in
      let _ = Printf.fprintf !out_channel "DEBUG: private\n" in
      let _ = PrintExprs.idTSet (u.Invariant.coq_private) in
      ()
    
    let invariant (inv:Invariant.t): unit =
      let _ = Printf.fprintf !out_channel "DEBUG: P\n" in
      let _ = unary (inv.Invariant.src) in
      let _ = Printf.fprintf !out_channel "DEBUG: Q\n" in
      let _ = unary (inv.Invariant.tgt) in

      let num_in_nat = IdTSet.cardinal inv.Invariant.maydiff in
      let num = Datatype_base.Size.from_nat num_in_nat in
      let _ = Printf.fprintf !out_channel "DEBUG: D (%d)\n" num in
      let _ = PrintExprs.idTSet (inv.Invariant.maydiff) in
      ()
  end

let debug_run f =
  if !Globalstates.debug
  then f ()
  else ()
                      
let debug_bool (b:bool) (msg:string): bool =
  let _ =
    debug_run
      (fun _ ->
       if not b
       then Printf.fprintf !out_channel "DEBUG: %s" msg
       else ())
  in b

let debug_print_invariant (inv: Invariant.t): unit =
  debug_run (fun _ -> PrintHints.invariant inv)
