open Exprs
open Hints
open Syntax
open Coq_pretty_printer
open Printf
open List
open MetatheoryAtom

type atom = AtomImpl.atom
       
let out_channel = ref stderr

let debug_run f =
  if !Globalstates.debug
  then f ()
  else ()

let debug_print s =
  debug_run (fun _ -> Printf.fprintf !out_channel "DEBUG: %s\n" s)

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

    let rec of_typ (ty:LLVMsyntax.typ): string =
      match ty with
      | LLVMsyntax.Coq_typ_int sz -> Printf.sprintf "i%d" sz
      | LLVMsyntax.Coq_typ_floatpoint fp ->
        begin match fp with
        | LLVMsyntax.Coq_fp_float -> "f32"
        | LLVMsyntax.Coq_fp_double -> "f64"
        | LLVMsyntax.Coq_fp_fp128 -> "fp128"
        | LLVMsyntax.Coq_fp_x86_fp80 -> "x86fp80"
        | LLVMsyntax.Coq_fp_ppc_fp128 -> "ppcfp128"
        end
      | LLVMsyntax.Coq_typ_void -> "void"
      | LLVMsyntax.Coq_typ_label -> "lbl"
      | LLVMsyntax.Coq_typ_metadata -> "md"
      | LLVMsyntax.Coq_typ_array (sz, typ') -> Printf.sprintf "%s[%d]" (of_typ typ') sz
      | LLVMsyntax.Coq_typ_function (ret_typ, arg_typs, vargs) -> "fun" (* TODO: more precise *)
      | LLVMsyntax.Coq_typ_struct elem_typs -> "struct" (* TODO: more precise *)
      | LLVMsyntax.Coq_typ_pointer obj_typ -> Printf.sprintf "%s*" (of_typ obj_typ)
      | LLVMsyntax.Coq_typ_namedt id -> "namedt" (* TODO: more precise *)

    let of_Ptr (p:Ptr.t): string =
      match p with
      | (vt, typ) ->
        Printf.sprintf "%s:%s" (of_ValueT vt) (of_typ typ)

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
         Printf.sprintf "gep %s %s %s (%s) %s"
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

    let of_ptrPair (pp:PtrPair.t) (sym:string): string =
      let (p1, p2) = pp in
      let s1 = of_Ptr p1 in
      let s2 = of_Ptr p2 in
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

    let idSet (ids: AtomSetImpl.t) (sym: string): string list =
      List.map
        (fun id -> (sym ^ " " ^ id))
        (AtomSetImpl.elements ids)

    let idTSet (idts: IdTSet.t) (sym: string): string list =
      List.map
        (fun idt -> (sym ^ (ExprsToString.of_IdT idt)))
        (IdTSet.elements idts)

    let ptrSet (ps: PtrSet.t) (sym: string): string list =
      List.map
        (fun p -> (sym ^ ExprsToString.of_Ptr p))
        (PtrSet.elements ps)

    let ptrPairSet (pps: PtrPairSet.t) (sym:string): string list =
      List.map
        (fun pp -> (ExprsToString.of_ptrPair pp sym))
        (PtrPairSet.elements pps)
  end
                      
module PrintHints = struct
    let infrule_to_string (inf:Infrule.t): string =
      (* TODO: print args *)
      match inf with
      | Infrule.Coq_add_const_not (x, y, v, c1, c2, sz) ->
         "add_const_not"
      | Infrule.Coq_add_sub _ -> "add_sub"
      | Infrule.Coq_bop_associative (x, y, z, bop, c1, c2, c3, sz) ->
         "bop_assoc " ^ (string_of_bop bop)
      | Infrule.Coq_bop_distributive_over_selectinst(pcode, r, s, t', t, x, y, z, c, bopsz, selty) -> 
                                                "BopDistributiveOverSelectInst"
      | Infrule.Coq_bop_commutative (e, bop, x, y, s) -> "bop_commutative : " ^ 
                                                ExprsToString.of_expr(e) ^ " ≥ " ^
                                                ExprsToString.of_expr(Expr.Coq_value x) ^ (string_of_bop bop) ^
                                                ExprsToString.of_expr(Expr.Coq_value y) ^ " to commutate"
      | Infrule.Coq_bop_commutative_rev (e, bop, x, y, s) -> "bop_commutative_rev : " ^
                                                ExprsToString.of_expr(Expr.Coq_value x) ^ (string_of_bop bop) ^ " ≥ " ^
                                                ExprsToString.of_expr(e) ^
                                                ExprsToString.of_expr(Expr.Coq_value y) ^ " to commutate"
      | Infrule.Coq_bitcast_load (ptr, ptrty, v1, ptrty2, v2, a) ->
         "bitcast_load " ^ 
             (ExprsToString.of_ValueT ptr) ^ " " ^
             (string_of_typ ptrty) ^ " " ^
             (ExprsToString.of_ValueT v1) ^ " " ^
             (string_of_typ ptrty2) ^ " " ^
             (ExprsToString.of_ValueT v2) ^ " " ^ 
             (ExprsToString.of_align a)
      | Infrule.Coq_sub_add _ -> "sub_add"
      | Infrule.Coq_neg_val _ -> "neg_val"
      | Infrule.Coq_add_mask _ -> "add_mask"
      | Infrule.Coq_add_onebit _ -> "add_onebit"
      | Infrule.Coq_add_select_zero _ -> "add_select_zero"
      | Infrule.Coq_add_select_zero2 _ -> "add_select_zero2"
      | Infrule.Coq_add_shift _ -> "add_shift"
      | Infrule.Coq_add_signbit _ -> "add_signbit"
      | Infrule.Coq_add_zext_bool _ -> "add_zext_bool"
      | Infrule.Coq_bitcastptr _ -> "bitcastptr"
      | Infrule.Coq_diffblock_lessthan (x,y,x2,y2) -> "diffblock_lessthan " ^
                                    (ExprsToString.of_ValueT x) ^ "_||_" ^
                                    (ExprsToString.of_ValueT y) ^ " >= " ^
                                    (ExprsToString.of_ValueT x2) ^ "_||_" ^
                                    (ExprsToString.of_ValueT y2)
      | Infrule.Coq_diffblock_noalias _ -> "diffblock_noalias"
      | Infrule.Coq_diffblock_unique _ -> "diffblock_unique"
      | Infrule.Coq_diffblock_global_unique _ -> "diffblock_global_unique"
      | Infrule.Coq_diffblock_global_global _ -> "diffblock_global_global"
      | Infrule.Coq_fmul_commutative_tgt (z, x, y, fty) -> "fmul_commutative_tgt " ^
                                    "fmul " ^ 
                                    (string_of_typ (LLVMsyntax.Coq_typ_floatpoint fty)) ^ 
                                    " " ^ (ExprsToString.of_ValueT x) ^
                                    " " ^ (ExprsToString.of_ValueT y) ^
                                    " >= " ^ (ExprsToString.of_IdT z)
      | Infrule.Coq_gep_inbounds_add _ ->
         "gep inbounds add"
      | Infrule.Coq_gep_inbounds_remove (gepinst) ->
         "gep inbounds remove: " ^ (ExprsToString.of_expr gepinst)
      | Infrule.Coq_gepzero _ -> "gepzero"
      | Infrule.Coq_intro_eq v -> "intro_eq : " ^ ExprsToString.of_expr(v)
      | Infrule.Coq_intro_ghost (e, id) -> "intro_ghost:"
                                           ^ "[src] " ^ (ExprsToString.of_expr e)
                                           ^ " >= " ^ (ExprsToString.of_IdT (Tag.Coq_ghost, id))
                                           ^ "[tgt] " ^ (ExprsToString.of_IdT (Tag.Coq_ghost, id))
                                           ^ " >= " ^ (ExprsToString.of_expr e)
      | Infrule.Coq_or_xor3 (z, y, a, b, s) -> "or_xor3 : " ^ 
                                                ExprsToString.of_expr(Expr.Coq_value y) ^ " ≥ "
                                                        ^ ExprsToString.of_expr(Expr.Coq_value a) ^ " ^ "
                                                        ^ ExprsToString.of_expr(Expr.Coq_value b) ^ " -> " ^
                                                ExprsToString.of_expr(Expr.Coq_value z)
      | Infrule.Coq_ptrtoint_load _ -> "ptrtoint_load"
      | Infrule.Coq_ptrtoint_zero _ -> "ptrtoint_zero"
      | Infrule.Coq_transitivity (a, b, c) -> "transitivity : " ^
                                                ExprsToString.of_expr a ^ " ≥ " ^
                                                  ExprsToString.of_expr b ^ " ≥ " ^
                                                    ExprsToString.of_expr c
      | Infrule.Coq_transitivity_tgt (a, b, c) -> "transitivity_tgt : " ^
                                                ExprsToString.of_expr a ^ " ≥ " ^
                                                  ExprsToString.of_expr b ^ " ≥ " ^
                                                    ExprsToString.of_expr c
      | Infrule.Coq_substitute (x, y, e) ->
         "substitute : "
         ^ ExprsToString.of_expr e ^ " ≥ ([ "
         ^ ExprsToString.of_IdT x ^ " := " ^ ExprsToString.of_ValueT y ^ " ] "
         ^ ExprsToString.of_expr e ^ ")"
      | Infrule.Coq_substitute_tgt (x, y, e) ->
         "substitute_tgt : "
         ^ ExprsToString.of_expr e ^ " ≥ ([ "
         ^ ExprsToString.of_IdT x ^ " := " ^ ExprsToString.of_ValueT y ^ " ] "
         ^ ExprsToString.of_expr e ^ ")"
      | Infrule.Coq_substitute_rev (x, y, e) ->
         "substitute_rev : "
         ^ "([ " ^ ExprsToString.of_IdT x ^ " := " ^ ExprsToString.of_ValueT y ^ " ] "
         ^ ExprsToString.of_expr e ^ ")"
         ^ " ≥ " ^ ExprsToString.of_expr e
      | Infrule.Coq_transitivity_pointer_lhs (p, q, v, ty, a) -> "transitivity_pointer_lhs : " ^
                                                ExprsToString.of_expr(Expr.Coq_value p) ^ " ≥ " ^
                                                ExprsToString.of_expr(Expr.Coq_value q) ^ " && " ^
                                                ExprsToString.of_expr(Expr.Coq_load (q, ty, a) ) ^ " ≥ " ^
                                                ExprsToString.of_expr(Expr.Coq_value v)
      | Infrule.Coq_transitivity_pointer_rhs (p, q, v, ty, a) -> "transitivity_pointer_rhs : " ^
                                                ExprsToString.of_expr(Expr.Coq_value p) ^ " ≥ " ^
                                                ExprsToString.of_expr(Expr.Coq_value q) ^ " && " ^
                                                ExprsToString.of_expr(Expr.Coq_value v) ^ " ≥ " ^
                                                ExprsToString.of_expr(Expr.Coq_load (p, ty, a) )
      | Infrule.Coq_icmp_eq_same (ty, v1, v2) ->
         "icmp_eq_same: " ^
           "true >= icmp eq [" ^ ExprsToString.of_expr(Expr.Coq_value v1) ^ "] [" ^
           ExprsToString.of_expr(Expr.Coq_value v2) ^ "] implies both are same"
      | Infrule.Coq_icmp_inverse_tgt (c, ty, v1, v2, b) ->
         "icmp_inverse_tgt: " ^
           (ExprsToString.of_expr(Expr.Coq_icmp(c,ty,v1,v2))) ^ " >= " ^ (string_of_constant (LLVMsyntax.Coq_const_int (1, b))) ^
             " is being inversed"
      | Infrule.Coq_and_true_bool (v1, v2) ->
         "and_true_bool: " ^
           "true >= and 1 [" ^ ExprsToString.of_expr(Expr.Coq_value v1) ^ "] [" ^
           ExprsToString.of_expr(Expr.Coq_value v2) ^ "] implies both are true"
      | _ -> "infrule(TODO)"

    let infrules (infs:Infrule.t list): unit =
      let _ = List.map
                (fun inf ->
                 let s = infrule_to_string inf in
                 let _ = debug_print s in ())
                infs
      in ()
        
    let unary (u:Assertion.unary): string list =
      (PrintExprs.exprPairSet (u.Assertion.lessdef) "≥") @
        (PrintExprs.ptrPairSet (u.Assertion.alias.Assertion.noalias) "≠") @
        (PrintExprs.valueTPairSet (u.Assertion.alias.Assertion.diffblock) "_||_") @
        (PrintExprs.idSet (u.Assertion.unique) "uniq") @
        (PrintExprs.idTSet (u.Assertion.coq_private) "prvt")
    
    let assertion (inv:Assertion.t): unit =
      (* print_bar(), print_sum() should be function *)
      let print_bar() = debug_print (String.make 200 '-') in
      let num_in_nat = IdTSet.cardinal inv.Assertion.maydiff in
      let num = Datatype_base.Size.from_nat num_in_nat in
      let title =
        Printf.sprintf "%30s %60s %60s (%d)"
                       "[ SOURCE ]" "[ TARGET ]" "[ MayDiff ]" num in
      let src = unary (inv.Assertion.src) in
      let tgt = unary (inv.Assertion.tgt) in
      let maydiff = PrintExprs.idTSet (inv.Assertion.maydiff) "" in
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

    let assertions (hint_fdef:ValidationHint.fdef) (blockids: atom list): unit =
      let print_bar() = debug_print (String.make 200 '=') in
      print_bar ();
      List.iter
          (fun blockid ->
              let stmts = TODOCAML.get (Alist.lookupAL hint_fdef blockid) in
              debug_print (sprintf "<block %s>" blockid) ; 
              assertion (stmts.assertion_after_phinodes) ;
              List.iter 
                  (fun inv -> assertion inv)
                  (List.map snd stmts.cmds))
          blockids;
      print_bar ()
  end

let debug_print_validation_process (infrules: Infrule.t list)
                                   (inv0: Assertion.t)
                                   (inv1: Assertion.t)
                                   (inv2: Assertion.t)
                                   (inv3: Assertion.t)
                                   (inv: Assertion.t)
    : Assertion.t =
  let _ =
    debug_run
      (fun _ ->
       let _ = debug_print "** precondition" in
       let _ = PrintHints.assertion inv0 in
       let _ = debug_print "** postcond generates" in
       let _ = PrintHints.assertion inv1 in
       let _ = debug_print "** infrules" in
       let _ = PrintHints.infrules infrules in
       let _ = debug_print "** applying infrule" in
       let _ = PrintHints.assertion inv2 in
       let _ = debug_print "** reducing maydiff" in
       let _ = PrintHints.assertion inv3 in
       let _ = debug_print "** next precondition" in
       let _ = PrintHints.assertion inv in ())
  in inv

let debug_print_auto (infrules: Infrule.t list)
                     (inv: Assertion.t)
    : Assertion.t =
  let _ =
    debug_run
      (fun _ ->
       let _ = debug_print "** infrules by auto" in
       let _ = PrintHints.infrules infrules in
       let _ = debug_print "** applying infrule (with reducing maydiff?)" in
       let _ = PrintHints.assertion inv in ())
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

let expr_printer (x: Expr.t): unit =
  debug_run(
      fun _ ->
      debug_print (ExprsToString.of_expr x))

let debug_string (x: char list) (y: 'a) =
  let _ = debug_run(fun _ -> debug_print (string_of_char_list x))
  in y
