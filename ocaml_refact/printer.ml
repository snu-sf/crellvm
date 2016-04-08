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

    let of_ValueT (vt:ValueT.t): string =
      match vt with
      | ValueT.Coq_id idt ->
         (of_IdT idt)
      | ValueT.Coq_const c ->
         (string_of_constant c)

    let of_sz (s:LLVMsyntax.sz): string =
      Printf.sprintf "(sz %d)" s

    let of_align (al:LLVMsyntax.align): string =
      Printf.sprintf "(align %d)" al

    let rec of_sz_ValueT_list svl =
      String.concat ", " (List.map (fun (sz, vt) ->
                                    "i"^(string_of_int sz)^" "^(of_ValueT vt)) svl)
        
    let of_expr (e:Expr.t): string =
      match e with
      | Expr.Coq_bop (b, s, vt1, vt2) ->
         Printf.sprintf "bop %s %s %s %s"
                       (string_of_bop b) (of_sz s) (of_ValueT vt1) (of_ValueT vt2)
      | Expr.Coq_fbop (fb, fp, vt1, vt2) ->
         Printf.sprintf "fbop %s %s %s %s"
                        (string_of_fbop fb) (string_of_floating_point fp)
                        (of_ValueT vt1) (of_ValueT vt2)
      | Expr.Coq_extractvalue (ty1, vt, cl, ty2) ->
         Printf.sprintf "extractvalue %s %s %s %s"
                        (string_of_typ ty1)
                        (of_ValueT vt)
                        (string_of_list_constant cl)
                        (string_of_typ ty2)
      | Expr.Coq_insertvalue (ty1, vt1, ty2, vt2, cl) ->
         Printf.sprintf "insertvalue %s %s %s %s %s"
                        (string_of_typ ty1)
                        (of_ValueT vt1)
                        (string_of_typ ty2)
                        (of_ValueT vt2)
                        (string_of_list_constant cl)
      | Expr.Coq_gep (inb, ty1, vt, svl, ty2) ->
         Printf.sprintf "getelementptr %s %s %s (%s) %s"
                        (string_of_bool inb)
                        (string_of_typ ty1)
                        (of_ValueT vt)
                        (of_sz_ValueT_list svl)
                        (string_of_typ ty2)
      | Expr.Coq_trunc (trop, ty1, vt, ty2) ->
         Printf.sprintf "trunc %s %s %s %s"
                        (string_of_truncop trop)
                        (string_of_typ ty1)
                        (of_ValueT vt)
                        (string_of_typ ty2)
      | Expr.Coq_ext (extop, ty1, vt, ty2) ->
         Printf.sprintf "ext %s %s %s %s"
                        (string_of_extop extop)
                        (string_of_typ ty1)
                        (of_ValueT vt)
                        (string_of_typ ty2)
      | Expr.Coq_cast (castop, ty1, vt, ty2) ->
         Printf.sprintf "cast %s %s %s %s"
                        (string_of_castop castop)
                        (string_of_typ ty1)
                        (of_ValueT vt)
                        (string_of_typ ty2)
      | Expr.Coq_icmp (cond, ty, vt1, vt2) ->
         Printf.sprintf "icmp %s %s %s %s"
                        (string_of_cond cond)
                        (string_of_typ ty)
                        (of_ValueT vt1)
                        (of_ValueT vt2)
      | Expr.Coq_fcmp (fcond, fp, vt1, vt2) ->
         Printf.sprintf "fcmp %s %s %s %s"
                        (string_of_fcond fcond)
                        (string_of_floating_point fp)
                        (of_ValueT vt1)
                        (of_ValueT vt2)
      | Expr.Coq_select (vt, ty, vt1, vt2) ->
         Printf.sprintf "select %s %s %s %s"
                        (of_ValueT vt)
                        (string_of_typ ty)
                        (of_ValueT vt1)
                        (of_ValueT vt2)
      | Expr.Coq_value vt ->
         Printf.sprintf "value %s" (of_ValueT vt)
      | Expr.Coq_load (vt, ty, al) ->
         Printf.sprintf "load %s %s %s"
                        (of_ValueT vt)
                        (string_of_typ ty)
                        (of_align al)

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
    let infrule_to_string (inf:Infrule.t): string =
      (* TODO: print args *)
      match inf with
      | Infrule.Coq_add_associative (x, y, z, c1, c2, c3, sz) ->
         "add_assoc"
      | Infrule.Coq_add_const_not (x, y, v, c1, c2, sz) ->
         "add_const_not"
      | Infrule.Coq_add_sub _ -> "add_sub"
      | Infrule.Coq_add_commutative _ -> "add_commutative"
      | Infrule.Coq_sub_add _ -> "sub_add"
      | Infrule.Coq_neg_val _ -> "neg_val"
      | Infrule.Coq_add_mask _ -> "add_mask"
      | Infrule.Coq_add_onebit _ -> "add_onebit"
      | Infrule.Coq_add_select_zero _ -> "add_select_zero"
      | Infrule.Coq_add_select_zero2 _ -> "add_select_zero2"
      | Infrule.Coq_add_shift _ -> "add_shift"
      | Infrule.Coq_add_signbit _ -> "add_signbit"
      | Infrule.Coq_add_zext_bool _ -> "add_zext_bool"
      | Infrule.Coq_transitivity (a, b, c) -> "transitivity : " ^
                                                ExprsToString.of_expr a ^ " ≥ " ^
                                                  ExprsToString.of_expr b ^ " ≥ " ^
                                                    ExprsToString.of_expr c
      | Infrule.Coq_replace_rhs _ -> "replace_rhs"
      | _ -> "infrule(TODO)"

    let infrules (infs:Infrule.t list): unit =
      let _ = List.map
                (fun inf ->
                 let s = infrule_to_string inf in
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
                              TODOCAML.print_callstack_and_fail "should not occur!") sum in
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
      let print_bar() = debug_print (String.make 200 '-') in
      print_bar() ;
      debug_print (sprintf "%30s %60s" "[ SRC CMD ]" "[ TGT CMD ]") ;
      debug_print (sprintf "%30s %60s" (string_of_cmd x) (string_of_cmd y)) ;
      print_bar() ;
      debug_print(""))

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

let infrule_printer (x: Infrule.t): unit =
  debug_run(
      fun _ ->
      debug_print (PrintHints.infrule_to_string x))

let debug_string (x: char list) (y: 'a) =
  let _ = debug_run(fun _ -> debug_print (string_of_char_list x))
  in y
