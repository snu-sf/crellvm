open Exprs
open Hints
open Syntax
open Coq_pretty_printer
open Printf
open List
       
let out_channel = ref stdout

let debug_print (msg:string): unit =
  Printf.fprintf !out_channel "DEBUG: %s\n" msg

module ExprsToString = struct
    let of_Tag (t:Tag.t): string =
      match t with
      | Tag.Coq_physical -> "●"
      | Tag.Coq_previous -> "◎"
      | Tag.Coq_ghost -> "○"
    
    let of_IdT (idt:IdT.t): string =
      let (t, id) = idt in
      Printf.sprintf "(%s, %s)" (of_Tag t) id

    let of_const (c:LLVMsyntax.const): string =
      "TODO"

    let of_ValueT (vt:ValueT.t): string =
      match vt with
      | ValueT.Coq_id idt ->
         (of_IdT idt)
      | ValueT.Coq_const c ->
         (of_const c)

    let of_sz (s:LLVMsyntax.sz): string =
      Printf.sprintf "(sz %d)" s

    let of_bop (b:LLVMsyntax.bop): string=
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

    let of_fbop (fb:LLVMsyntax.fbop): string = "TODO"

    let of_floating_point (fp:LLVMsyntax.floating_point): string =
      "TODO"
        
    let of_expr (e:Expr.t): string =
      match e with
      | Expr.Coq_bop (b, s, vt1, vt2) ->
         Printf.sprintf "bop %s %s %s %s"
                       (of_bop b) (of_sz s) (of_ValueT vt1) (of_ValueT vt2)
      | Expr.Coq_fbop (fb, fp, vt1, vt2) ->
         Printf.sprintf "fbop %s %s %s %s"
                        (of_fbop fb) (of_floating_point fp)
                        (of_ValueT vt1) (of_ValueT vt2)
      | Expr.Coq_value vt ->
         Printf.sprintf "value %s" (of_ValueT vt)
      | _ -> "TODO"

    let of_exprPair (ep:ExprPair.t) (sym:string): string =
      let (e1, e2) = ep in
      let s1 = of_expr e1 in
      let s2 = of_expr e2 in
      Printf.sprintf "%s %s %s" s1 sym s2

    let of_valueTPair (vp:ValueTPair.t) (sym:string): string =
      let (v1, v2) = vp in
      let s1 = of_ValueT v1 in
      let s2 = of_ValueT v2 in
      Printf.sprintf "%s %s %s" s1 sym s2
  end

module PrintExprs = struct
    let exprPairSet (eps: ExprPairSet.t) (sym:string): string list =
      List.map
        (fun ep -> (ExprsToString.of_exprPair ep sym))
        (ExprPairSet.elements eps)

    let valueTPairSet (vtps: ValueTPairSet.t) (sym:string): string list = 
      List.map
        (fun vtp -> (ExprsToString.of_valueTPair vtp sym))
        (ValueTPairSet.elements vtps)

    let idTSet (idts: IdTSet.t) (sym: string): string list =
      List.map
        (fun idt -> (sym ^ (ExprsToString.of_IdT idt)))
        (IdTSet.elements idts)
  end
                      
module PrintHints = struct
    let infrules_to_string (inf:Infrule.t): string =
      match inf with
      | Infrule.Coq_add_associative (x, y, z, c1, c2, c3, sz) ->
         "add_assoc"
      | _ -> "TODO"

    let infrules (infs:Infrule.t list): unit =
      let _ = List.map
                (fun inf ->
                 let s = infrules_to_string inf in
                 let _ = debug_print s in ())
                infs
      in ()
        
    let unary (u:Invariant.unary): string list =
      (PrintExprs.exprPairSet (u.Invariant.lessdef) "≥") @
        (PrintExprs.valueTPairSet (u.Invariant.noalias) "≠") @
        (PrintExprs.idTSet (u.Invariant.allocas) "alc") @
        (PrintExprs.idTSet (u.Invariant.coq_private) "isol")
    
    let invariant (inv:Invariant.t): unit =
      (* print_bar(), print_sum() should be function *)
      let print_bar() = debug_print (String.make 200 '-') in
      let num_in_nat = IdTSet.cardinal inv.Invariant.maydiff in
      let num = Datatype_base.Size.from_nat num_in_nat in
      let title =
        Printf.sprintf "%30s %60s %60s (%d)"
                       "[ SOURCE ]" "[ TARGET ]" "[ MayDiff ]" num in
      let src = unary (inv.Invariant.src) in
      let tgt = unary (inv.Invariant.tgt) in
      let maydiff = PrintExprs.idTSet (inv.Invariant.maydiff) "" in
      let sum = TODOCAML.list_zip [src ; tgt ; maydiff] "-" in

      let print_sum() =
        let _ = print_bar() in
        let _ = debug_print title in
        let _ = List.iter (fun i ->
                           match i with
                           | [s ; t ; m] ->
                              debug_print (sprintf "%60s %60s %60s" s t m)
                           | x ->
                              let _ =
                                (List.iter (fun i -> debug_print i) x) in
                              failwith "should not occur!") sum in
        let _ = print_bar() in
        let _ = debug_print "" in
        () in
      let _ = if(length sum <> 0) then print_sum() else () in
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
       then debug_print msg
       else ())
  in b

let debug_option (o:'a option) (msg:string): 'a option =
  let _ =
    debug_run
      (fun _ ->
       match o with
         | None -> debug_print msg
         | Some _ -> ()
      )
  in o

let debug_print_validation_process (infrules: Infrule.t list)
                                   (inv0: Invariant.t)
                                   (inv1: Invariant.t)
                                   (inv2: Invariant.t)
                                   (inv3: Invariant.t)
                                   (inv: Invariant.t)
    : Invariant.t =
  let _ =
    debug_run
      (fun _ ->
       let _ = debug_print "** precondition" in
       let _ = PrintHints.invariant inv0 in
       let _ = debug_print "** postcond generates" in
       let _ = PrintHints.invariant inv1 in
       let _ = debug_print "** infrules" in
       let _ = PrintHints.infrules infrules in
       let _ = debug_print "** applying infrule" in
       let _ = PrintHints.invariant inv2 in
       let _ = debug_print "** reducing maydiff" in
       let _ = PrintHints.invariant inv3 in
       let _ = debug_print "** next precondition" in
       let _ = PrintHints.invariant inv in ())
  in inv

let cmd_printer (x: LLVMsyntax.cmd): unit =
  debug_run(
      fun _ ->
      debug_print (string_of_cmd x))

let cmd_pair_printer ((x,y): (LLVMsyntax.cmd * LLVMsyntax.cmd)): unit =
  debug_run(
      fun _ ->
      debug_print (sprintf "%30s %60s" "[ SRC CMD ]" "[ TGT CMD ]") ;
      debug_print (sprintf "%30s %60s" (string_of_cmd x) (string_of_cmd y)))

let string_of_char_list (l: char list) =
  List.fold_left (fun s i -> s ^ (Char.escaped i)) "" l

let atom_printer (x: string): unit =
  debug_run(
      fun _ ->
      debug_print x)

let idT_printer (x: Exprs.IdT.t): unit =
  debug_run(
      fun _ ->
      debug_print (ExprsToString.of_IdT x))

let debug_string (x: char list) (y: 'a) =
  let _ = debug_run(fun _ -> debug_print (string_of_char_list x))
  in y
