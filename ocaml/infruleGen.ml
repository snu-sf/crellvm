open Hints
open Exprs
open Infrules
open Syntax
open MetatheoryAtom
open LLVMsyntax
open Infrastructure
open TODOCAML

module AutoOpt = struct
    type pass_t =
      GVN | SROA | INSTCOMBINE | LICM | TEST1 | TEST2 | TEST3 | TEST4 | DEFAULT
    let pass_option : pass_t ref = ref DEFAULT
  end

module Auto = struct
    type scope_t = Src | Tgt

    type t1 = bool -> Invariant.t -> Invariant.t -> (Infrule.t list * Invariant.t)
    type t2 = Invariant.t -> ValueTPair.t list -> (Infrule.t list * ValueTPair.t list)
    type t = t1 * t2

    (* Inference rules *)
    let transitivity (scp:scope_t) e1 e2 e3 : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_transitivity (e1, e2, e3)
      | Tgt -> Infrule.Coq_transitivity_tgt (e1, e2, e3)

    let gep_inbounds_remove scp gepinst : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_gep_inbounds_remove (gepinst)
      | Tgt -> Infrule.Coq_gep_inbounds_remove_tgt (gepinst)

    let substitute (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute (x, v, e)
      | Tgt -> Infrule.Coq_substitute_tgt (x, v, e)

    let substitute_rev (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute_rev (x, v, e)
      | Tgt -> Infrule.Coq_substitute_rev_tgt (x, v, e)

    let bop_commutative scp e op a b sz : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_bop_commutative (e, op, a, b, sz)
      | Tgt -> Infrule.Coq_bop_commutative_tgt (e, op, a, b, sz)

    let bop_commutative_rev scp e op a b sz : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_bop_commutative_rev (e, op, a, b, sz)
      | Tgt -> Infrule.Coq_bop_commutative_rev_tgt (e, op, a, b, sz)

    let fbop_commutative scp e op a b fp : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_fbop_commutative (e, op, a, b, fp)
      | Tgt -> Infrule.Coq_fbop_commutative_tgt (e, op, a, b, fp)

    let fbop_commutative_rev scp e op a b fp : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_fbop_commutative_rev (e, op, a, b, fp)
      | Tgt -> Infrule.Coq_fbop_commutative_rev_tgt (e, op, a, b, fp)

    let icmp_swap_operands scp c ty a b e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_icmp_swap_operands (c, ty, a, b, e)
      | Tgt -> Infrule.Coq_icmp_swap_operands_tgt (c, ty, a, b, e)

    let icmp_swap_operands_rev scp c ty a b e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_icmp_swap_operands_rev (c, ty, a, b, e)
      | Tgt -> Infrule.Coq_icmp_swap_operands_rev_tgt (c, ty, a, b, e)

    let fcmp_swap_operands scp c ty a b e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_fcmp_swap_operands (c, ty, a, b, e)
      | Tgt -> Infrule.Coq_fcmp_swap_operands_tgt (c, ty, a, b, e)

    let fcmp_swap_operands_rev scp c ty a b e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_fcmp_swap_operands_rev (c, ty, a, b, e)
      | Tgt -> Infrule.Coq_fcmp_swap_operands_rev_tgt (c, ty, a, b, e)

    let icmp_inverse scp c ty v1 v2 b =
      match scp with
      | Src -> Infrule.Coq_icmp_inverse (c, ty, v1, v2, b)
      | Tgt -> Infrule.Coq_icmp_inverse_tgt (c, ty, v1, v2, b)

    let icmp_inverse_rhs scp c ty v1 v2 b =
      match scp with
      | Src -> Infrule.Coq_icmp_inverse_rhs (c, ty, v1, v2, b)
      | Tgt -> Infrule.Coq_icmp_inverse_rhs_tgt (c, ty, v1, v2, b)

    let eq_exps_values (e1:Expr.t) (e2:Expr.t)
        : ((ValueT.t * ValueT.t) list) option =
      if Expr.same_modulo_value e1 e2
      then Some (List.combine (Expr.get_valueTs e1) (Expr.get_valueTs e2))
      else None

    let get_rhs_list (lessdef:ExprPairSet.t) (e:Expr.t)
        : Expr.t list =
      let ep_set = Invariant.get_rhs lessdef e in
      List.map snd (ExprPairSet.elements ep_set)

    let get_lhs_list (lessdef:ExprPairSet.t) (e:Expr.t)
        : Expr.t list =
      let ep_set = Invariant.get_lhs lessdef e in
      List.map fst (ExprPairSet.elements ep_set)

    let find_first_match (f:'b -> 'a option)
                         (b_list:'b list)
        : ('b * 'a) option =
      List.fold_left
        (fun acc e ->
         match acc with
         | Some res -> Some res
         | None -> (match f e with
                    | Some r -> Some (e, r)
                    | None -> None))
        None b_list

    let find_first_matchb (f:'b -> bool)
                          (b_list:'b list)
        : 'b option =
      match find_first_match (fun b -> if (f b) then Some () else None) b_list with
      | Some (b, _) -> Some b
      | None -> None

    let repl_value e v1 v2 : Expr.t =
      Expr.map_valueTs e (fun v -> if ValueT.eq_dec v1 v then v2 else v)
  end

module AutoTransHelper = struct
    module ExprSet = FSetExtra.Make(Expr)

    let string_of_exprlist (el:Expr.t list): string =
      let sl = List.map Printer.ExprsToString.of_expr el in
      List.fold_left (fun ss s -> ss^"-"^s) "" sl

    let rec make_trans_rev scp (el:Expr.t list): Infrule.t list =
      match el with
      | e3::e2::e1::tl ->
         (Auto.transitivity scp e1 e2 e3)::(make_trans_rev scp (e3::e1::tl))
      | _ -> []

    (* to_visit in reachables & graph *)
    let rec get_reachable
          (get_adj:Expr.t -> Expr.t list)
          (to_visit:Expr.t list)
          (reachables:ExprSet.t) (graph:ExprPairSet.t)
        : ExprSet.t * ExprPairSet.t =
      match to_visit with
      | [] -> (reachables, graph)
      | e_cur::to_visit_later ->
         Printer.debug_print ("AutoInfruleGen: Transitivity processing "^(Printer.ExprsToString.of_expr e_cur));
         let new_visit =
           List.filter (fun e -> not (ExprSet.mem e reachables)) (get_adj e_cur)
         in
         Printer.debug_print ("AutoInfruleGen: Transitivity new visit="^(string_of_exprlist new_visit));
         let new_reachables =
           List.fold_left (fun s e -> ExprSet.add e s) reachables new_visit
         in
         let new_graph =
           List.fold_left (fun g e -> ExprPairSet.add (e_cur, e) g) graph new_visit
         in
         get_reachable get_adj (to_visit_later@new_visit) new_reachables new_graph

    let get_reachable_from_l (ld:ExprPairSet.t) (e:Expr.t)
        : ExprSet.t * ExprPairSet.t =
      get_reachable (Auto.get_rhs_list ld)
                    [e] (ExprSet.singleton e) ExprPairSet.empty

    let get_reachable_from_r (ld:ExprPairSet.t) (e:Expr.t)
        : ExprSet.t * ExprPairSet.t =
      get_reachable (Auto.get_lhs_list ld)
                    [e] (ExprSet.singleton e) ExprPairSet.empty

    (* gr is always tree*)
    let rec get_path (acc:Expr.t list) (gr:ExprPairSet.t)
                     (e_from:Expr.t) (e_to:Expr.t)
        : Expr.t list =
      if Expr.eq_dec e_from e_to then e_to::acc
      else match Auto.get_lhs_list gr e_to with
           | e_l::_ -> get_path (e_to::acc) gr e_from e_l
           | _ -> []

    let rec gen_infrules (scp:Auto.scope_t) (chain:Expr.t list)
            : Infrule.t list =
      let res = match chain with
      | e1::e2::e3::chain_t ->
         (Auto.transitivity scp e1 e2 e3)::(gen_infrules scp (e1::e3::chain_t))
      | _ -> []
      in
      Printer.debug_print ("AutoInfruleGen: gen_infrules succeeds with length :"^(string_of_int (List.length res)));
      res

    let run_inj (inv:Invariant.t) (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      let (rch_src, gr_src) = get_reachable_from_l inv.Invariant.src.Invariant.lessdef e1 in
      let (rch_tgt, gr_tgt) = get_reachable_from_r inv.Invariant.tgt.Invariant.lessdef e2 in
      let cand_exprs = ExprSet.elements (ExprSet.inter rch_src rch_tgt) in
      let filtered_cand_exprs =
        List.filter
          (fun e -> List.for_all (Invariant.not_in_maydiff inv) (Expr.get_valueTs e))
          cand_exprs in
      match filtered_cand_exprs with
      | e::_ ->
         let path_src = get_path [] gr_src e1 e in
         let path_tgt = List.rev (get_path [] gr_tgt e2 e) in
         let infrs_src = gen_infrules Auto.Src path_src in
         let infrs_tgt = gen_infrules Auto.Tgt path_tgt in
         Some (infrs_src@infrs_tgt)
      | [] -> None

    let run_unary_i (scp:Auto.scope_t) (ld:ExprPairSet.t)
                    (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      Printer.debug_print "AutoInfruleGen: Transitivity-Unary_intl start";
      let (rch, gr) = get_reachable_from_l ld e1 in
      let path = get_path [] gr e1 e2 in
      Some (gen_infrules scp path)

    let run_unary (scp:Auto.scope_t) (inv_u:Invariant.unary)
                  (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      Printer.debug_print "AutoInfruleGen: Transitivity-Unary start";
      run_unary_i scp inv_u.Invariant.lessdef e1 e2
  end

module AutoCommHelper = struct
    (* Given `e1 >= e2`, returns the list of commutativity rules applicable to e2 and
        the updated invariant *)
    let find_commrules_on_e2 (scp:Auto.scope_t) (e1e2:ExprPair.t)
        : (Infrule.t * ExprPair.t) option =
      let (e1, e2) = e1e2 in
      match e2 with
       | Expr.Coq_bop (op2, sz2, a2, b2) when is_commutative_bop op2 ->
          Some ( (Auto.bop_commutative scp e1 op2 a2 b2 sz2),
                  (e1, Expr.Coq_bop (op2, sz2, b2, a2)) )
       | Expr.Coq_fbop (op2, fp2, a2, b2) when is_commutative_fbop op2 ->
          Some ( (Auto.fbop_commutative scp e1 op2 a2 b2 fp2),
                  (e1, Expr.Coq_fbop (op2, fp2, b2, a2)) )
       | Expr.Coq_icmp (c2, ty2, a2, b2) ->
          Some ( (Auto.icmp_swap_operands scp c2 ty2 a2 b2 e1),
                  (e1, Expr.Coq_icmp (get_swapped_icmp_cond c2, ty2, b2, a2)) )
       | Expr.Coq_fcmp (c2, ty2, a2, b2) ->
          Some ( (Auto.fcmp_swap_operands scp c2 ty2 a2 b2 e1),
                  (e1, Expr.Coq_fcmp (get_swapped_fcmp_cond c2, ty2, b2, a2)) )
       | _ -> None
    
    (* Given `e1 >= e2`, returns the list of commutativity rules applicable to e1 and
        the updated invariant*)
    let find_commrules_on_e1 (scp:Auto.scope_t) (e1e2:ExprPair.t)
        : (Infrule.t * ExprPair.t) option =
      let (e1, e2) = e1e2 in
      match e1 with
       | Expr.Coq_bop (op1, sz1, a1, b1) when is_commutative_bop op1 ->
          Some ( (Auto.bop_commutative_rev scp e2 op1 a1 b1 sz1),
                  (Expr.Coq_bop (op1, sz1, b1, a1), e2) )
       | Expr.Coq_fbop (op1, fp1, a1, b1) when is_commutative_fbop op1 ->
          Some ( (Auto.fbop_commutative_rev scp e2 op1 a1 b1 fp1),
                  (Expr.Coq_fbop (op1, fp1, b1, a1), e2) )
       | Expr.Coq_icmp (c1, ty1, a1, b1) ->
          Some ( (Auto.icmp_swap_operands_rev scp c1 ty1 a1 b1 e2),
                  (Expr.Coq_icmp (get_swapped_icmp_cond c1, ty1, b1, a1), e2) )
       | Expr.Coq_fcmp (c1, ty1, a1, b1) ->
          Some ( (Auto.fcmp_swap_operands_rev scp c1 ty1 a1 b1 e2),
                  (Expr.Coq_fcmp (get_swapped_fcmp_cond c1, ty1, b1, a1), e2) )
       | _ -> None
  end

module AutoSubstTransHelper = struct
    let max_depth : int = 5

    let bdd (e:Expr.t) (oe:Expr.t option) : Expr.t =
      match oe with
      | Some b -> b
      | None -> e

    let attach_oinfrs h t oinfrs =
      match oinfrs with
      | Some infrs -> Some (h@infrs@t)
      | _ -> None

    let rec do_subst scp e1 vpl acc_infrs : (Infrule.t list) option =
      match vpl with
      | [] -> Some acc_infrs
      | (v1, v2)::vplt ->
         if ValueT.eq_dec v1 v2 then do_subst scp e1 vplt acc_infrs
         else match v1 with
              | ValueT.Coq_id (x) ->
                 let e_n = Expr.map_valueTs e1 (fun v0 ->
                                                if ValueT.eq_dec v0 (ValueT.Coq_id (x))
                                                then v2 else v0) in
                 do_subst scp e_n vplt (Auto.substitute scp x v2 e1::acc_infrs)
              | _ -> match v2 with
                     | ValueT.Coq_id (y) ->
                        let e_n = Expr.map_valueTs e1 (fun v0 ->
                                                       if ValueT.eq_dec v0 v1
                                                       then v2 else v0) in
                        do_subst scp e_n vplt (Auto.substitute_rev scp y v1 e_n::acc_infrs)
                     | _ -> None


    (* Make [(bdd e1 oe1) >= (bdd e2 oe2)]. *)
    (* If e1 = e2 and oe1=oe2=None, do nothing. *)
    let rec run depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      (* let string_of_exprpairlist (el:ExprPair.t list): string = *)
      (*   let sl = List.map (fun (e1, e2) -> *)
      (*                      (Printer.ExprsToString.of_expr e1) ^ ">="^ *)
      (*                        (Printer.ExprsToString.of_expr e2)) el *)
      (*   in  *)
      (*   List.fold_left (fun ss s -> ss^"\n"^s) "" sl *)
      (* in  *)
      (* let _ = print_endline ("run d="^(string_of_int depth)) in *)
      (* let _ = print_endline ("e1="^(Printer.ExprsToString.of_expr e1)) in *)
      (* let _ = print_endline ("e2="^(Printer.ExprsToString.of_expr e2)) in *)
      if depth > max_depth then None
      else if (Expr.eq_dec e1 e2)
      then match oel, oer with
           | Some el, Some er -> Some [Auto.transitivity scp el e1 er]
           | _ -> Some []
      else if ExprPairSet.mem (e1, e2) ld
      then match oel, oer with
           | None, None -> Some []
           | Some el, None -> Some [Auto.transitivity scp el e1 e2]
           | None, Some er -> Some [Auto.transitivity scp e1 e2 er]
           | Some el, Some er -> Some [Auto.transitivity scp el e1 e2;
                                                                           Auto.transitivity scp el e2 er]
      else
        (* let _ = print_endline ((Printer.ExprsToString.of_expr e1)^">="^(Printer.ExprsToString.of_expr e2)) in *)
        (* let _ = print_endline ("not in "^string_of_exprpairlist (ExprPairSet.elements ld)) in *)
        (* let _ = print_endline "==about to call by_destruct" in *)

        match by_destruct depth scp ld oel e1 e2 oer with
        | Some infrs -> Some infrs
        | None ->
            match by_trans_left depth scp ld oel e1 e2 oer with
            | Some infrs -> Some infrs
            | None -> by_trans_right depth scp ld oel e1 e2 oer

    (* Generates (bdd oe1 e1) >= (bdd oer e2) *)
    and by_destruct depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      let do_left h e1_new : (Infrule.t list) option =
        match oel with
        | Some el ->
           attach_oinfrs (h el) [] (by_dest_intl depth scp ld oel e1_new e2 oer)
        | None -> None in
      let do_right h e2_new : (Infrule.t list) option =
        match oer with
        | Some er ->
           attach_oinfrs (h er) [] (by_dest_intl depth scp ld oel e1 e2_new oer)
        | None -> None in
      let res_fin =
      match by_dest_intl depth scp ld oel e1 e2 oer with
      | Some infrs -> Some infrs
      | None ->
         (match e1, e2 with
          | Expr.Coq_gep (true, tya, v, lsv, tyb), Expr.Coq_gep (false, _, _, _, _) ->
             attach_oinfrs
               [Auto.gep_inbounds_remove scp e1] (* assume this occurs only on SRC side *)
               (match oel with
                | Some el -> [Auto.transitivity scp el e1 (bdd e2 oer)]
                | _ -> [])
               (by_dest_intl depth scp ld (Some e1) (Expr.Coq_gep (false, tya, v, lsv, tyb)) e2 oer)
          | Expr.Coq_bop (op1, sz1, a1, b1), Expr.Coq_bop (op2, sz2, a2, b2)
               when LLVMinfra.bop_dec op1 op2 && is_commutative_bop op1 ->
             (match do_left (fun el -> [Auto.bop_commutative scp el op1 a1 b1 sz1])
                            (Expr.Coq_bop (op1, sz1, b1, a1)) with
              | Some infrs -> Some infrs
              | None -> do_right (fun er -> [Auto.bop_commutative_rev scp er op2 a2 b2 sz2])
                                 (Expr.Coq_bop (op2, sz2, b2, a2)))
          | Expr.Coq_fbop (op1, fp1, a1, b1), Expr.Coq_fbop (op2, fp2, a2, b2)
               when LLVMinfra.fbop_dec op1 op2 && is_commutative_fbop op1 ->
             (match do_left (fun el -> [Auto.fbop_commutative scp el op1 a1 b1 fp1])
                            (Expr.Coq_fbop (op1, fp1, b1, a1)) with
              | Some infrs -> Some infrs
              | None -> do_right (fun er -> [Auto.fbop_commutative_rev scp er op2 a2 b2 fp2])
                                 (Expr.Coq_fbop (op2, fp2, b2, a2)))
          | Expr.Coq_icmp (c1, ty1, a1, b1), Expr.Coq_icmp (c2, ty2, a2, b2)
               when LLVMinfra.cond_dec (get_swapped_icmp_cond c1) c2 ->
             (match do_left (fun el -> [Auto.icmp_swap_operands scp c1 ty1 a1 b1 el])
                            (Expr.Coq_icmp (c2, ty1, b1, a1)) with
              | Some infrs -> Some infrs
              | None -> do_right (fun er -> [Auto.icmp_swap_operands_rev scp c2 ty2 a2 b2 er])
                                 (Expr.Coq_icmp (c1, ty2, b2, a2)))
          | Expr.Coq_fcmp (c1, ty1, a1, b1), Expr.Coq_fcmp (c2, ty2, a2, b2)
               when LLVMinfra.fcond_dec (get_swapped_fcmp_cond c1) c2 ->
             (match do_left (fun el -> [Auto.fcmp_swap_operands scp c1 ty1 a1 b1 el])
                            (Expr.Coq_fcmp (c2, ty1, b1, a1)) with
              | Some infrs -> Some infrs
              | None -> do_right (fun er -> [Auto.fcmp_swap_operands_rev scp c2 ty2 a2 b2 er])
                                 (Expr.Coq_fcmp (c1, ty2, b2, a2)))
          | _, _ -> None)
      in res_fin

    (* Generates [(bdd oel e1) >= (bdd oer e2)] by substitution *)
    and by_dest_intl depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      match e1, e2 with
      | Expr.Coq_value _, _
      | _, Expr.Coq_value _ -> None
      | _, _ ->
         match Auto.eq_exps_values e1 e2 with
         | None -> None
         | Some vpl ->
            match
              List.fold_left
                (fun a vp ->
                 match a with
                 | (None, _) -> a
                 | (Some acc_infrs, e_stk) ->
                    let (v1, v2) = vp in
                    if (ValueT.eq_dec v1 v2) then a else
                    let e_m = match e_stk with h::_ -> h | [] -> e1 in
                    let e_m_n = Auto.repl_value e_m v1 v2 in
                    let oinfrs = (run (depth+1) scp ld None (Expr.Coq_value v1) (Expr.Coq_value v2) None) in
                    (* let _ = match oinfrs with *)
                    (*   | Some _ -> print_endline "by_dest_intl Some" *)
                    (*   | None -> print_endline "by_dest_intl None" *)
                    (* in *)
                    let a_oinfrs = attach_oinfrs acc_infrs [] oinfrs in
                    (a_oinfrs, e_m_n::e_stk))
                (Some [], [e1]) vpl
            with
            | None, _ -> None
            | Some acc_infrs, e_stk ->
               let e_stk = match oel with Some e_l -> e_stk@[e_l] | _ -> e_stk in
               let e_stk = match oer with Some e_r -> e_r::e_stk | _ -> e_stk in
               attach_oinfrs acc_infrs (AutoTransHelper.make_trans_rev scp e_stk)
                             (do_subst scp e1 vpl [])

    and by_trans_left depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      (* let _ = print_endline "by_trans_left" in *)
      (* let _ = print_endline ("e1="^(Printer.ExprsToString.of_expr e1)) in *)
      (* let _ = print_endline ("e2="^(Printer.ExprsToString.of_expr e2)) in *)
      match Auto.find_first_match (fun e1_r ->
                                   run (depth+1) scp ld (Some e1) e1_r e2 oer)
                                  (Auto.get_rhs_list ld e1) with
      | None -> None
      | Some (_, infrs) ->
         (* let _ = print_endline "matched in left" in *)
         match oel with
         | Some el -> Some (infrs@[Auto.transitivity scp el e1 (bdd e2 oer)])
         | _ -> Some infrs

    and by_trans_right depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      match Auto.find_first_match (fun e2_l ->
                                   run (depth+1) scp ld oel e1 e2_l (Some e2))
                                  (Auto.get_lhs_list ld e2) with
      | None -> None
      | Some (_, infrs) ->
         (* let _ = print_endline "matched in right" in *)
         match oer with
         | Some er -> Some (infrs@[Auto.transitivity scp (bdd e1 oel) e2 er])
         | _ -> Some infrs

    let auto1_unary scp (inv_u:Invariant.unary) (inv_u_g:Invariant.unary)
        : (Infrule.t list) * Invariant.unary =
      let ld = inv_u.Invariant.lessdef in
      let ldl_g = ExprPairSet.elements inv_u_g.Invariant.lessdef in
      let (infrs, ld_g) =
        List.fold_left (fun (acc:(Infrule.t list) * ExprPairSet.t) (ep_g:ExprPair.t) ->
                        if ExprPairSet.mem ep_g ld then acc else
                          let infrs_acc, inv_acc = acc in
                          match run 0 scp ld None (fst ep_g) (snd ep_g) None with
                          | Some infrs -> (infrs_acc@infrs, inv_acc)
                          | None -> (infrs_acc, ExprPairSet.add ep_g inv_acc)) ([], ExprPairSet.empty) ldl_g
      in (infrs, Invariant.update_lessdef (fun _ -> ld_g) inv_u_g)

    let auto1 : Auto.t1 =
      fun b inv inv_g ->
      if b then ([], inv_g) else
      let (infrs1, inv_src_g) = auto1_unary Auto.Src inv.Invariant.src inv_g.Invariant.src in
      let (infrs2, inv_tgt_g) = auto1_unary Auto.Tgt inv.Invariant.tgt inv_g.Invariant.tgt in
      let inv_g = Invariant.update_src (fun _ -> inv_src_g) inv_g in
      let inv_g = Invariant.update_tgt (fun _ -> inv_tgt_g) inv_g in
      (infrs1@infrs2, inv_g)

  end

module IntroGhostHelper = struct
    let gather_ghost (inv:Invariant.t) : id list =
      let gather_ghost_ld (ld:ExprPairSet.t) : id list =
        List.fold_left (fun acc ep ->
                        let idts = (Expr.get_idTs (fst ep)) @ (Expr.get_idTs (snd ep)) in
                        (filter_map (fun idt -> if (fst idt = Tag.Coq_ghost) then Some (snd idt) else None) idts)
                        @acc) [] (ExprPairSet.elements ld) in
      let raw =(gather_ghost_ld inv.Invariant.src.Invariant.lessdef)
               @(gather_ghost_ld inv.Invariant.tgt.Invariant.lessdef) in
      List.sort_uniq compare raw

    let get_ghost_id e : id =
      match e with
      | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, x)) -> x
      | _ -> failwith "get_ghost_id applied to non-ghost expr"

    let find_non_value (is_src:bool) (epl : ExprPair.t list) : ExprPair.t option =
      let f = if is_src then fst else snd in
      Auto.find_first_matchb (fun ep -> match (f ep) with
                                        | Expr.Coq_value _ -> false
                                        | _ -> true) epl

    let find_unique_v (g:id) (is_src:bool) (ld:ExprPairSet.t) : Expr.t option =
      let filtered_ld =
        ExprPairSet.filter (fun (e1, e2) -> List.exists (fun idt -> IdT.eq_dec idt (Tag.Coq_ghost, g))
                                                        ((Expr.get_idTs e1)@(Expr.get_idTs e2))) ld in
      match (ExprPairSet.elements filtered_ld) with
      | (e1, e2)::[] ->
         let ge = Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, g)) in
         if Expr.eq_dec e1 ge then Some e2 else
           if Expr.eq_dec e2 ge then Some e1 else None
      | _ -> None

    let is_prev_pair (e:Expr.t) (inv:Invariant.t) : bool =
      (* let ld = inv.Invariant.src.Invariant.lessdef in *)
      let l = Auto.get_rhs_list inv.Invariant.src.Invariant.lessdef e in
      List.exists (fun e0 -> match e0 with Expr.Coq_value (ValueT.Coq_id (Tag.Coq_previous, _)) -> true | _ -> false) l

    let simple_phi (g:id) (inv:Invariant.t) (inv_g:Invariant.t) : Expr.t option =
      match find_unique_v g true inv_g.Invariant.src.Invariant.lessdef,
            find_unique_v g false inv_g.Invariant.tgt.Invariant.lessdef with
      | Some e1, Some e2 when Expr.eq_dec e1 e2 ->
         (* print_endline "simple_phi yes"; *)
         if (is_prev_pair e1 inv) then Some e1 else None
      | _ -> None

    let find_to_intro (inv:Invariant.t) (inv_g:Invariant.t) : (id * Expr.t) list =
      let check_intro_cand scp g ep: bool =
        match ((if scp = Auto.Src then snd else fst) ep) with
        | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, x)) -> x = g
        | _ -> false
      in
      let existing_ghosts : id list = gather_ghost inv in
      let ghosts_g : id list = gather_ghost inv_g in
      List.fold_left (fun intros_acc g ->
                      match simple_phi g inv inv_g with
                      | Some (e) -> (g, e)::intros_acc
                      | None ->
                         if (List.mem g existing_ghosts) then intros_acc else
                           let src_side = List.filter (check_intro_cand Auto.Src g)
                                                      (ExprPairSet.elements inv_g.Invariant.src.Invariant.lessdef) in
                           let tgt_side = List.filter (check_intro_cand Auto.Tgt g)
                                                      (ExprPairSet.elements inv_g.Invariant.tgt.Invariant.lessdef) in
                           match find_non_value true src_side with
                           (* | Some ep -> (get_ghost_id (snd ep), fst ep)::intros_acc *)
                           | Some ep -> (g, fst ep)::intros_acc
                           | None -> if List.length src_side > 0
                                     then let ep = List.nth src_side 0 in
                                          (g, fst ep)::intros_acc
                                     else
                                       match find_non_value false tgt_side with
                                       (* | Some ep -> (get_ghost_id (snd ep), fst ep)::intros_acc *)
                                       | Some ep -> (g, snd ep)::intros_acc
                                       | None -> if List.length tgt_side > 0
                                                 then let ep = List.nth tgt_side 0 in
                                                      (g, snd ep)::intros_acc
                                                 else intros_acc)

                     [] ghosts_g

    let gen_infrule (l: (id * Expr.t) list) : Infrule.t list =
      List.map (fun (g, e) -> Infrule.Coq_intro_ghost (e, g)) l
  end

module AutoGVNModule = struct
    let make_trunc scp ld ty1 s ty2 d : Infrule.t list =
      match Auto.find_first_match (fun ep -> match ep with
                                             | (Expr.Coq_trunc (top, tya, v1, tyb), Expr.Coq_value v2) when (LLVMinfra.typ_dec tya ty1) -> Some (v1, tyb, v2)
                                             | _ -> None) (ExprPairSet.elements ld) with
      | Some (_, (v1, tyb, v2)) ->
         (if (LLVMinfra.typ_dec tyb ty2) then [] else
            match Auto.find_first_match (fun ep -> match ep with
                                                   | (Expr.Coq_trunc (top, tya, v1, tyb), Expr.Coq_value v2) when (LLVMinfra.typ_dec tyb ty2) -> Some (v2)
                                                   | _ -> None) (ExprPairSet.elements ld) with
            | Some (_, v3) -> [Infrule.Coq_trunc_trunc_rev_tgt (v1, v2, v3, ty1, tyb, ty2)]
            | None -> [])
      | _ -> []

    let make_bc scp ld ty1 s ty2 d : Infrule.t list =
      match Auto.find_first_match (fun ep -> match ep with
                                             | (Expr.Coq_cast (cop, tya, v1, tyb), Expr.Coq_value v2) when (LLVMinfra.typ_dec tya ty1) -> Some (v1, tyb, v2)
                                             | _ -> None) (ExprPairSet.elements ld) with
      | Some (_, (v1, tyb, v2)) ->
         (if (LLVMinfra.typ_dec tyb ty2) then [] else
            match Auto.find_first_match (fun ep -> match ep with
                                                   | (Expr.Coq_cast (cop, tya, v1, tyb), Expr.Coq_value v2) when (LLVMinfra.typ_dec tyb ty2) -> Some (v2)
                                                   | _ -> None) (ExprPairSet.elements ld) with
            | Some (_, v3) -> [Infrule.Coq_bitcast_bitcast_rev_tgt (v1, v2, v3, ty1, tyb, ty2)]
            | None -> [])
      | _ -> []

    (* TODO: let [ g >= load ] => [ g >= tmp] *)
    let hintgenLoad scp ld oell el er : (Infrule.t list) option =
      match scp with
      | Auto.Src -> failwith "hintgenLoad src not implemented yet."
      | Auto.Tgt ->
         (* let _ = print_endline "hintgenload start" in *)
         match oell, el, er with
         | (e_g, Expr.Coq_load (v1, ty1, a), Expr.Coq_value y) ->
            (* let _ = print_endline "hintgenload start2" in *)
            (match Auto.find_first_match (fun ep -> match ep with
                                                    | (Expr.Coq_load (v, ty, a), Expr.Coq_value z) ->
                                                       (* let _ = print_endline "hintgenload found0" in *)
                                                       if (ValueT.eq_dec v1 v) then None
                                                       else Some(v, ty, z)
                                                    | _ -> None) (ExprPairSet.elements ld) with
             | Some (_, (v2, ty2, z)) ->
                (* let _ = print_endline "hintgenload found1" in *)
                let infrs1 = make_trunc scp ld ty2 z ty1 y in
                let infrs2 =
                  match v2 with
                  | ValueT.Coq_const (Coq_const_castop (_, c, _)) ->
                     [Infrule.Coq_trunc_load_const_bitcast_rev_tgt (c, z, y, ty1, ty2, a)]
                  | _ ->
                     (make_bc scp ld (Coq_typ_pointer ty1) v1 (Coq_typ_pointer ty2) v2)@
                       [Infrule.Coq_trunc_load_bitcast_rev_tgt (v1, v2, z, y, ty1, ty2, a)]
                in Some (infrs1@infrs2@(AutoTransHelper.gen_infrules scp [e_g; Expr.Coq_load (v1, ty1, a); er]))
             | _ -> None)
         | _, _, _ -> None

    (* let hintgenLoad scp ld oell el er oerr : (Infrule.t list) option = *)
    (*   match scp with *)
    (*   | Auto.Src -> failwith "hintgenLoad src not implemented yet." *)
    (*   | Auto.Tgt -> *)
    (*      match oell, el, er with *)
    (*      | (Some e_g), (Expr.Coq_value x), (Expr.Coq_value y) -> *)
    (*         (match Auto.find_first_match (fun e -> match e with *)
    (*                                                | Expr.Coq_load (v, ty, a) -> Some (v, ty, a) *)
    (*                                                | _ -> None) (Auto.get_rhs_list ld el) with *)
    (*          | Some (_, (v1, ty1, a)) -> *)
    (*             (match Auto.find_first_match (fun ep -> match ep with *)
    (*                                                     | (Expr.Coq_load (v, ty, a), Expr.Coq_value z) -> *)
    (*                                                        if (ValueT.eq_dec v1 v) then None *)
    (*                                                        else Some(v, ty, z) *)
    (*                                                     | _ -> None) (ExprPairSet.elements ld) with *)
    (*              | Some (_, (v2, ty2, z)) -> *)
    (*                 let infrs1 = make_trunc scp ld ty2 z ty1 y in *)
    (*                 let infrs2 = *)
    (*                   match v2 with *)
    (*                   | ValueT.Coq_const (Coq_const_castop (_, c, _)) -> *)
    (*                      [Infrule.Coq_trunc_load_const_bitcast_rev_tgt (c, z, y, ty1, ty2, a)] *)
    (*                   | _ -> *)
    (*                      (make_bc scp ld (Coq_typ_pointer ty1) v1 (Coq_typ_pointer ty2) v2)@ *)
    (*                        [Infrule.Coq_trunc_load_bitcast_rev_tgt (v1, v2, z, y, ty1, ty2, a)] *)
    (*                 in Some (infrs1@infrs2@(AutoTransHelper.gen_infrules scp [e_g; el; Expr.Coq_load (v1, ty1, a); er])) *)
    (*              | _ -> None) *)
    (*          | _ -> None) *)
    (*      | _, _, _ -> None *)

    (* let find_unique_v (g:id) (is_src:bool) (ld:ExprPairSet.t) : Expr.t option = *)
    (*   let filtered_ld = *)
    (*     ExprPairSet.filter (fun (e1, e2) -> List.exists (fun idt -> IdT.eq_dec idt (Tag.Coq_ghost, g)) *)
    (*                                                     ((Expr.get_idTs e1)@(Expr.get_idTs e2))) ld in *)
    (*   match (ExprPairSet.elements filtered_ld) with *)
    (*   | (e1, e2)::[] -> *)
    (*      let ge = Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, g)) in *)
    (*      if Expr.eq_dec e1 ge then Some e2 else *)
    (*        if Expr.eq_dec e2 ge then Some e1 else None *)
    (*   | _ -> None *)

    let process_load (ld_t:ExprPairSet.t) (ld_t_g:ExprPairSet.t) : Infrule.t list =
      let ld_t_l = (ExprPairSet.elements ld_t) in
      let ld_t_g_l = (ExprPairSet.elements ld_t_g) in
      let ores = Auto.find_first_match
                   (fun (e1, e2) -> match e1, e2 with
                                    | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, g)),
                                      Expr.Coq_load (_, _, _) ->
                                       (* let _ = print_endline ("first ghost:"^g) in *)
                                       let ores = Auto.find_first_match
                                                    (fun (ea, eb) -> if Expr.eq_dec e1 ea then
                                                                       (match eb with
                                                                        | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_physical, x)) ->
                                                                           (* let _ = print_endline ("find other:"^x) in *)
                                                                           hintgenLoad Auto.Tgt ld_t e1 e2 eb
                                                                        | _ -> None)
                                                                     else None) ld_t_g_l in ores
                                    | _, _ -> None) ld_t_l
      in match ores with
         | Some (_,(_, infrs)) -> infrs
         | None -> []

    let infrules_icmp_inverse (ld:ExprPairSet.t) : (Infrule.t list) * ExprPairSet.t  =
      List.fold_left (fun acc ep -> match ep with
                                    | (Expr.Coq_icmp (c, t, v1, v2),
                                       Expr.Coq_value (ValueT.Coq_const (Coq_const_int (sz, b)))) ->
                                       ((fst acc)@[Infrule.Coq_icmp_inverse_tgt (c, t, v1, v2, b)],
                                        ExprPairSet.add (Expr.Coq_icmp (get_inverse_icmp_cond c, t, v1, v2),
                                                         Expr.Coq_value (ValueT.Coq_const (Coq_const_int (sz, get_inverse_boolean_Int b)))) (snd acc))
                                    | _ -> acc) ([], ld) (ExprPairSet.elements ld)

    let new_auto1 : Auto.t1 =
      fun b inv inv_g ->
      if b then ([], inv_g) else
      let intros = IntroGhostHelper.find_to_intro inv inv_g in
      let infrs_intros = IntroGhostHelper.gen_infrule intros in
      let intros_e = List.map (fun (x, e) -> (Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, x)), e)) intros in
      let augment_ld f ld = List.fold_left (fun ld1 ep -> ExprPairSet.add (f ep) ld1) ld intros_e in
      let inv = Invariant.update_src (Invariant.update_lessdef (augment_ld (fun ep -> (snd ep, fst ep)))) inv in
      let inv = Invariant.update_tgt (Invariant.update_lessdef (augment_ld (fun ep -> ep))) inv in
      let infrs_ii, ld_t = infrules_icmp_inverse inv.Invariant.tgt.Invariant.lessdef in
      let inv = Invariant.update_tgt (Invariant.update_lessdef (fun _ -> ld_t)) inv in
      let infrs_load = process_load inv.Invariant.tgt.Invariant.lessdef inv_g.Invariant.tgt.Invariant.lessdef in
      (* let inv = Invariant.update_tgt (Invariant.update_lessdef (process_load inv_g.Invariant.tgt.Invariant.lessdef)) *)
      (*                                inv in *)
      let (infrs_st, inv_g) = AutoSubstTransHelper.auto1 b inv inv_g in
      (infrs_intros@infrs_ii@infrs_load@infrs_st, inv_g)
  end

(** Framework 1. AutoNextInvariant *)
module type AutoNextInv = sig
    val run : Auto.t1
  end

(** Framework 1-1. Removing Maydiff *)
module type InjectValueGenerator = sig
    val f : Invariant.t -> ValueT.t -> ValueT.t -> (Infrule.t list) option
  end

module AutoRemMD (GEN:InjectValueGenerator) : AutoNextInv = struct
    let find_inject (inv:Invariant.t) (x:IdT.t)
        : (Infrule.t list) option =
      GEN.f inv (ValueT.Coq_id x) (ValueT.Coq_id x)

    let rec run_intl (inv:Invariant.t) (inv_goal:Invariant.t)
                     (infrs_acc:Infrule.t list) (md:IdT.t list)
            : Infrule.t list * Invariant.t =
      match md with
      | [] -> (infrs_acc, inv_goal)
      | x::md_t ->
         (match find_inject inv x with
          | Some infrs ->
             let inv_goal_new =
               Invariant.update_maydiff (IdTSet.remove x) inv_goal
             in
             run_intl inv inv_goal_new (infrs_acc@infrs) md_t
          | None -> run_intl inv inv_goal infrs_acc md_t)

    let run (isfirst:bool) (inv:Invariant.t) (inv_goal:Invariant.t)
        : Infrule.t list * Invariant.t =
      let md : IdT.t list =
        IdTSet.elements inv.Invariant.maydiff in
      let md_goal : IdT.t list =
        IdTSet.elements inv_goal.Invariant.maydiff in
      let md_remain : IdT.t list =
        List.filter (fun x -> not (List.exists (IdT.eq_dec x) md_goal)) md in
      run_intl inv inv_goal [] md_remain
  end

(** Framework 1-2. Unary Invariants *)
module type UnaryLDGenerator = sig
    val f : Auto.scope_t -> Invariant.unary ->
            Expr.t -> Expr.t -> (Infrule.t list) option
  end

module AutoUnaryLD (ULDG:UnaryLDGenerator): AutoNextInv = struct
    let rec run_intl (scp:Auto.scope_t)
                     (inv_u:Invariant.unary) (inv_u_goal:Invariant.unary)
                     (infrs_acc:Infrule.t list) (ld:(Expr.t * Expr.t) list)
            : Infrule.t list * Invariant.unary =
      let res = match ld with
      | [] -> (infrs_acc, inv_u_goal)
      | (e_l, e_r)::ld_t ->
         (match ULDG.f scp inv_u e_l e_r with
          | Some infrs ->
             let inv_u_goal_new =
               Invariant.update_lessdef (ExprPairSet.remove (e_l, e_r)) inv_u_goal
             in
             run_intl scp inv_u inv_u_goal_new (infrs_acc@infrs) ld_t
          | None -> run_intl scp inv_u inv_u_goal infrs_acc ld_t)
      in res

    let run_unary (scp:Auto.scope_t)
                  (inv_u:Invariant.unary) (inv_u_goal:Invariant.unary)
        : Infrule.t list * Invariant.unary =
      let ld : ExprPair.t list =
        ExprPairSet.elements inv_u.Invariant.lessdef in
      let ld_goal : ExprPair.t list =
        ExprPairSet.elements inv_u_goal.Invariant.lessdef in
      let ld_remain : ExprPair.t list =
        List.filter (fun x -> not (List.exists (ExprPair.eq_dec x) ld)) ld_goal in
      run_intl scp inv_u inv_u_goal [] ld_remain

    let run (isfirst:bool) (inv:Invariant.t) (inv_goal:Invariant.t)
        : Infrule.t list * Invariant.t =
      if isfirst then
        ([], inv_goal)
      else (
        Printer.debug_print "AutoInfruleGen: AutoUnaryLD start";
        let (infrs_src, inv_src) =
          run_unary Auto.Src inv.Invariant.src inv_goal.Invariant.src in
        Printer.debug_print "AutoInfruleGen: AutoUnaryLD src end";
        let (infrs_tgt, inv_tgt) =
          run_unary Auto.Tgt inv.Invariant.tgt inv_goal.Invariant.tgt in
        Printer.debug_print "AutoInfruleGen: AutoUnaryLD tgt end";
        let new_goal = Invariant.update_tgt
                         (fun _ -> inv_tgt)
                         (Invariant.update_src (fun _ -> inv_src) inv_goal) in
        (infrs_src@infrs_tgt, new_goal)
      )
  end

(** 2. AutoInjectValues *)
module type AutoInjVal = sig
    val run : Auto.t2
  end

module AutoInjectValues (GEN:InjectValueGenerator): AutoInjVal = struct
    let rec run_intl (inv:Invariant.t) (vpl_acc:ValueTPair.t list)
                     (infrs_acc:Infrule.t list) (vpl:ValueTPair.t list)
            : Infrule.t list * (ValueTPair.t list) =
      match vpl with
      | [] -> (infrs_acc, vpl_acc)
      | (v_l, v_r)::vpl_t ->
         (match GEN.f inv v_l v_r with
          | Some infrs -> run_intl inv vpl_acc (infrs_acc@infrs) vpl_t
          | None -> run_intl inv ((v_l, v_r)::vpl_acc) infrs_acc vpl_t)

    let run (inv : Invariant.t) (vpl:(ValueT.t * ValueT.t) list)
        : Infrule.t list * (ValueT.t * ValueT.t) list =
      run_intl inv [] [] vpl
  end

module AutoUnaryLD_Trans : AutoNextInv =
  AutoUnaryLD
    (struct
        let f = AutoTransHelper.run_unary
      end)

module AutoInstCombineModule : AutoNextInv = struct
    let _apply_commutativities (scp:Auto.scope_t) (lessdefs:ExprPairSet.t)
        (finder: Auto.scope_t -> ExprPair.t -> (Infrule.t * ExprPair.t) option)
        : (Infrule.t list * ExprPairSet.t) =
      let generated_itms:((Infrule.t * ExprPair.t) option) list =
              List.map (fun lessdef -> finder scp lessdef) (ExprPairSet.elements lessdefs) in
      let (infrules, newlessdefs) = List.fold_left
              (fun (infrules, newlessdefs) pairopt ->
                  match pairopt with
                  | None -> (infrules, newlessdefs)
                  | Some (infr, newld) -> (infr::infrules, ExprPairSet.add newld newlessdefs)
              )
              ([], ExprPairSet.empty)
              generated_itms in
      (infrules, ExprPairSet.union lessdefs newlessdefs)

    let run : Auto.t1 = fun (isfirst:bool) (inv:Invariant.t) (inv_goal:Invariant.t) ->
      let lessdefs_src = inv.src.lessdef in
      let (infrules_src1, lessdefs_added) = _apply_commutativities
              Auto.Src lessdefs_src (AutoCommHelper.find_commrules_on_e1) in
      let lessdefs_src = ExprPairSet.union lessdefs_src lessdefs_added in
      let (infrules_src2, lessdefs_added) = _apply_commutativities
              Auto.Src lessdefs_src (AutoCommHelper.find_commrules_on_e2) in
      let lessdefs_src = ExprPairSet.union lessdefs_src lessdefs_added in

      let lessdefs_tgt = inv.tgt.lessdef in
      let (infrules_src3, lessdefs_added) = _apply_commutativities
              Auto.Tgt lessdefs_tgt (AutoCommHelper.find_commrules_on_e1) in
      let lessdefs_tgt = ExprPairSet.union lessdefs_tgt lessdefs_added in
      let (infrules_src4, lessdefs_added) = _apply_commutativities
              Auto.Tgt lessdefs_tgt (AutoCommHelper.find_commrules_on_e2) in
      let lessdefs_tgt = ExprPairSet.union lessdefs_tgt lessdefs_added in

      let newinv = Invariant.update_src
              (Invariant.update_lessdef (fun _ -> lessdefs_src))
                (Invariant.update_tgt
                  (Invariant.update_lessdef (fun _ -> lessdefs_tgt))
                  inv) in

      let (infrules_trans, inv_goal) = AutoUnaryLD_Trans.run false newinv inv_goal in
      (infrules_src1@infrules_src2@infrules_src3@infrules_src4@infrules_trans,
          inv_goal)
  end

module Auto_Default1 : AutoNextInv = struct
    let run : Auto.t1 = fun _ _ r -> ([], r)
  end

(** Instances of AutoInjectValues *)

module AutoInjectValues_Trans : AutoInjVal =
  AutoInjectValues
    (struct
        let f inv v1 v2 = AutoTransHelper.run_inj inv (Expr.Coq_value v1) (Expr.Coq_value v2)
      end)

module Auto_Default2 : AutoInjVal = struct
    let run : Auto.t2 = fun _ vp -> ([], vp)
  end

(*
let compose1 (a1:Auto.t1) (a2:Auto.t1) : Auto.t1 =
  fun inv0 invg ->
  let (infrs1, invg1) = a1 inv0 invg in
  let (infrs2, invg2) = a2 inv0 invg1 in
  (infrs1@infrs2, invg2)

let compose2 (a1:Auto.t2) (a2:Auto.t2) : Auto.t2 =
  fun inv0 vpl ->
  let (infrs1, vpl1) = a1 inv0 vpl in
  let (infrs2, vpl2) = a2 inv0 vpl1 in
  (infrs1@infrs2, vpl2)
*)

(** candidates *)

let autoGVN : Auto.t = (AutoGVNModule.new_auto1, Auto_Default2.run)
let autoSROA : Auto.t = (AutoUnaryLD_Trans.run, AutoInjectValues_Trans.run)
let autoLICM : Auto.t = (AutoUnaryLD_Trans.run, AutoInjectValues_Trans.run)
let autoInstCombine : Auto.t = (AutoInstCombineModule.run, Auto_Default2.run)
let autoDflt : Auto.t = (Auto_Default1.run, Auto_Default2.run)

(** interface *)

module AutoStrategy = struct
    let select : unit -> Auto.t =
      fun _ ->
      match !AutoOpt.pass_option with
      | AutoOpt.GVN -> autoGVN
      | AutoOpt.SROA -> autoSROA
      | AutoOpt.LICM -> autoLICM
      | AutoOpt.INSTCOMBINE -> autoInstCombine
      | _ -> autoDflt
  end

let gen_infrules_from_insns
      (insn_src : LLVMsyntax.insn)
      (insn_tgt : LLVMsyntax.insn)
      (inv : Invariant.t)
    : Infrule.t list =
  Printer.debug_print "AutoInfruleGen: gen_infrules_from_insns start";
  let run = snd (AutoStrategy.select ()) in
  let get_value_pairs_from_insns
        (insn_src : LLVMsyntax.insn)
        (insn_tgt : LLVMsyntax.insn)
      : ((ValueT.t * ValueT.t) list) option =
    let value2ValueT = ValueT.lift Tag.Coq_physical in
    match insn_src, insn_tgt with
    | Coq_insn_cmd cmd_src, Coq_insn_cmd cmd_tgt ->
       (match cmd_src, cmd_tgt with
        | Coq_insn_call (_, _, _, _, _, _, params1),
          Coq_insn_call (_, _, _, _, _, _, params2) ->
           let vl1 = List.map (fun vp -> value2ValueT (snd vp)) params1 in
           let vl2 = List.map (fun vp -> value2ValueT (snd vp)) params2 in
           Some (List.combine vl1 vl2)
        | _, _ -> None)
    | Coq_insn_terminator term_src,
      Coq_insn_terminator term_tgt ->
       (match term_src, term_tgt with
        | Coq_insn_return (_, _, v1), Coq_insn_return (_, _, v2)
        | Coq_insn_br (_, v1, _, _), Coq_insn_br (_, v2, _, _)
        | Coq_insn_switch (_, _, v1, _, _), Coq_insn_switch (_, _, v2, _, _) ->
           Some [(value2ValueT v1, value2ValueT v2)]
        | _, _ -> None)
    | _, _ -> None
  in
  let res = match get_value_pairs_from_insns insn_src insn_tgt with
  | Some vpl -> fst (run inv vpl)
  | None -> []
  in
  Printer.debug_print "AutoInfruleGen: gen_infrules_from_insns end";
  res

let gen_infrules_next_inv (isfirst:bool) (inv:Invariant.t) (inv_nxt:Invariant.t)
    : Infrule.t list =
  Printer.debug_print "AutoInfruleGen: gen_infrules_next_inv start";
  let run = fst (AutoStrategy.select ()) in
  let res = fst (run isfirst inv inv_nxt) in
  Printer.debug_print "AutoInfruleGen: gen_infrules_next_inv end";
  res
