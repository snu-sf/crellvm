open Hints
open Exprs
open Infrules
open Syntax
open MetatheoryAtom
open LLVMsyntax
open Infrastructure

module AutoOpt = struct
    type pass_t =
      GVN | SROA | INSTCOMBINE | TEST1 | TEST2 | TEST3 | TEST4 | DEFAULT
    let pass_option : pass_t ref = ref DEFAULT
  end

module Auto = struct
    type scope_t = Src | Tgt

    type t1 = Invariant.t -> Invariant.t -> (Infrule.t list * Invariant.t)
    type t2 = Invariant.t -> ValueTPair.t list -> (Infrule.t list * ValueTPair.t list)
    type t = t1 * t2

    (* Inference rules *)
    let transitivity (scp:scope_t) e1 e2 e3 : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_transitivity (e1, e2, e3)
      | Tgt -> Infrule.Coq_transitivity_tgt (e1, e2, e3)

    let substitute (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute (x, v, e)
      | Tgt -> Infrule.Coq_substitute_tgt (x, v, e)

    (* TODO: remove*)
    let substitute_rev (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute_rev (x, v, e)
      | Tgt -> Infrule.Coq_substitute_rev (x, v, e) (* TGT version not present *)

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

    (* TODO: remove this *)
    let intro_ghost_unary (scp:scope_t) e x : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_intro_ghost_src (e, x)
      | Tgt -> Infrule.Coq_intro_ghost_src (e, x) (* TGT version not present *)

    (* Unary invariant *)
    let inv_unary (scp:scope_t) : Invariant.t -> Invariant.unary =
      match scp with
      | Src -> Invariant.src
      | Tgt -> Invariant.tgt

    let update_unary (scp:scope_t)
        : (Invariant.unary -> Invariant.unary) ->
          Invariant.t -> Invariant.t =
      match scp with
      | Src -> Invariant.update_src
      | Tgt -> Invariant.update_tgt

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

    let expr_find_first_match (f:Expr.t -> 'a option)
                              (exp_list:Expr.t list)
        : (Expr.t * 'a) option = find_first_match f exp_list

    let find_first_match2 (f:'b -> 'b -> 'a option)
                          (b_list1:'b list) (b_list2:'b list)
        : ('b * 'b * 'a) option =
      let do_r e1 el2 =
        List.fold_left
          (fun acc e2 ->
           match acc with
           | Some res -> Some res
           | None -> (match f e1 e2 with
                      | Some r -> Some (e1, e2, r)
                      | None -> None))
          None el2
      in
      List.fold_left
        (fun acc el1 ->
         match acc with
         | Some res -> Some res
         | None -> do_r el1 b_list2)
        None b_list1

    let expr_find_first_match2 (f:Expr.t -> Expr.t -> 'a option)
                               (exp_list1:Expr.t list) (exp_list2:Expr.t list)
        : (Expr.t * Expr.t * 'a) option = find_first_match2 f exp_list1 exp_list2

    let substitute_expr x v e : Expr.t =
      let x_to_v w =
        match w with
        | ValueT.Coq_id y -> if IdT.eq_dec x y then v else w
        | ValueT.Coq_const _ -> w
      in (Expr.map_valueTs e x_to_v)

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

module NewAutoSubstTransHelper = struct
    let max_depth : int = 3

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
              | _ -> None

    (* Make [(bdd e1 oe1) >= (bdd e2 oe2)]. *)
    (* If e1 = e2 and oe1=oe2=None, do nothing. *)
    let rec run depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      print_endline ("NewAutoSubstTransHelper: run start with depth: "^(string_of_int depth));
      print_endline ("e1: "^(Printer.ExprsToString.of_expr e1));
      print_endline ("e2: "^(Printer.ExprsToString.of_expr e2));
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
      else match by_destruct depth scp ld oel e1 e2 oer with
           | Some infrs -> print_endline "run - by_destruct SUCCEEDED"; Some infrs
           | None ->
              print_endline "run - do trans";
              match by_trans_left depth scp ld oel e1 e2 oer with
                     | Some infrs -> Some infrs
                     | None -> by_trans_right depth scp ld oel e1 e2 oer

    (* Generates (bdd oe1 e1) >= (bdd oer e2) *)
    and by_destruct depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      print_endline "by_destruct";
      let do_left h e1_new : (Infrule.t list) option =
        print_endline "do_left";
        match oel with
        | Some el ->
           print_endline "left SUCCEEDED";
           attach_oinfrs (h el) [] (by_dest_intl depth scp ld oel e1_new e2 oer)
        | None -> None in
      let do_right h e2_new : (Infrule.t list) option =
        print_endline "do_right";
        match oer with
        | Some er ->
           print_endline "right SUCCEEDED";
           attach_oinfrs (h er) [] (by_dest_intl depth scp ld oel e1 e2_new oer)
        | None -> None in
      let res_fin = 
      match by_dest_intl depth scp ld oel e1 e2 oer with
      | Some infrs -> Some infrs
      | None ->
         (match e1, e2 with
          | Expr.Coq_gep (true, tya, v, lsv, tyb), Expr.Coq_gep (false, _, _, _, _) ->
             attach_oinfrs
               [Infrule.Coq_gep_inbounds_remove e1] (* assume this occurs only on SRC side *)
               (match oel with
                | Some el -> [Auto.transitivity scp el e1 (bdd e2 oer)]
                | _ -> [])
               (by_dest_intl depth scp ld (Some e1) (Expr.Coq_gep (false, tya, v, lsv, tyb)) e2 oer)
          | Expr.Coq_bop (op1, sz1, a1, b1), Expr.Coq_bop (op2, sz2, a2, b2)
               when LLVMinfra.bop_dec op1 op2 && is_commutative_bop op1 ->
             print_endline "BOP";
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
           in
           match res_fin with
           | Some _ -> print_endline "by_destruct SUCCEEDED"; res_fin
           | None -> print_endline "by_destruct FAILED"; res_fin

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
                    (attach_oinfrs acc_infrs [] (run (depth+1) scp ld None (Expr.Coq_value v1) (Expr.Coq_value v2) None), e_m_n::e_stk))
                (Some [], [e1]) vpl
            with
            | None, _ -> None
            | Some acc_infrs, e_stk ->
               print_endline "by_dest_intl SUCCEEDED";
               let e_stk = match oel with Some e_l -> e_stk@[e_l] | _ -> e_stk in
               let e_stk = match oer with Some e_r -> e_r::e_stk | _ -> e_stk in
               attach_oinfrs acc_infrs (AutoTransHelper.make_trans_rev scp e_stk)
                             (do_subst scp e1 vpl [])

    and by_trans_left depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      print_endline "by trans left";
      match Auto.find_first_match (fun e1_r ->
                                   run (depth+1) scp ld (Some e1) e1_r e2 oer)
                                  (Auto.get_rhs_list ld e1) with
      | None ->
         print_endline "by trans left FAILED";
         None
      | Some (_, infrs) ->
         print_endline "by trans left SUCCEEDED";
         match oel with
         | Some el -> Some (infrs@[Auto.transitivity scp el e1 (bdd e2 oer)])
         | _ -> Some infrs

    and by_trans_right depth scp ld oel e1 e2 oer : (Infrule.t list) option =
      print_endline "by trans right";
      match Auto.find_first_match (fun e2_l ->
                                   run (depth+1) scp ld oel e1 e2_l (Some e2))
                                  (Auto.get_lhs_list ld e2) with
      | None ->
         print_endline "by trans right FAILED";
         None
      | Some (_, infrs) ->
         print_endline "by trans right SUCCEEDED";
         match oer with
         | Some er -> Some (infrs@[Auto.transitivity scp (bdd e1 oel) e2 er])
         | _ -> Some infrs

  end


module AutoSubstTransHelper = struct
    let swap_expr_src (e_l:Expr.t) (e:Expr.t) : (Infrule.t list * Expr.t) option =
      match e with
      | Expr.Coq_bop (op, sz, v1, v2) ->
         if is_commutative_bop op then
           Some ([Infrule.Coq_bop_commutative (e_l, op, v1, v2, sz)],
                 Expr.Coq_bop (op, sz, v2, v1))
         else None
      | Expr.Coq_fbop (op, fp, v1, v2) ->
         if is_commutative_fbop op then
           Some ([Infrule.Coq_fbop_commutative (e_l, op, v1, v2, fp)],
                 Expr.Coq_fbop (op, fp, v2, v1))
         else None
      | Expr.Coq_icmp (c, ty, v1, v2) ->
         Some ([Infrule.Coq_icmp_swap_operands (c, ty, v1, v2, e_l)],
               Expr.Coq_icmp ((get_swapped_icmp_cond c), ty, v2, v1))
      | Expr.Coq_fcmp (c, fp, v1, v2) ->
         Some ([Infrule.Coq_fcmp_swap_operands (c, fp, v1, v2, e_l)],
               Expr.Coq_fcmp ((get_swapped_fcmp_cond c), fp, v2, v1))
      | _ -> None

    let drop_inbounds (e_l:Expr.t) (e:Expr.t) : (Infrule.t list * Expr.t) option =
      match e with
      | Expr.Coq_gep (true, ty1, t, svl, ty2) ->
         let e_noinb = Expr.Coq_gep (false, ty1, t, svl, ty2) in
         Some ([Infrule.Coq_gep_inbounds_remove e;
                Infrule.Coq_transitivity (e_l, e, e_noinb)], e_noinb)
      | _ -> None

    let try_modify (scp:Auto.scope_t) (e_l:Expr.t) (e:Expr.t)
        : (Infrule.t list * Expr.t) option =
      match scp with
      | Auto.Src ->
         (match swap_expr_src e_l e with
          | Some x -> Some x
          | None -> drop_inbounds e_l e)
      | _ -> None

    (* produce x >= v applying seq of subst-transitivity *)
    let rec try_trans (scp:Auto.scope_t) (inv_u : Invariant.unary)
                (x : IdT.t) (v : ValueT.t)
            : (Infrule.t list) option =
      if ValueT.eq_dec (ValueT.Coq_id x) v
      then Some [] else
        let exp_x = (Expr.Coq_value (ValueT.Coq_id x)) in
        let exp_v = (Expr.Coq_value v) in
        let e_l_cands = Auto.get_rhs_list inv_u.Invariant.lessdef exp_x in
        let e_r_cands = Auto.get_lhs_list inv_u.Invariant.lessdef exp_v in

        (* 1. Find direct application *)
        match Auto.expr_find_first_match2
                (fun e_l e_r ->
                 if Expr.eq_dec e_l e_r
                 then Some [Auto.transitivity scp exp_x e_l exp_v]
                 else match try_subst scp inv_u exp_x e_l e_r with
                      | Some infrs ->
                         Some (infrs@[Auto.transitivity scp exp_x e_r exp_v])
                      | None -> None)
                e_l_cands e_r_cands
        with
        | Some (_, _, infrs) -> Some infrs
        | None ->
           (* 2. Try applying one transitivity from v's side *)
           (match Auto.expr_find_first_match
                    (fun e -> match e with
                              | Expr.Coq_value nv ->
                                 (match try_trans scp inv_u x nv with
                                  | Some infrs -> Some (e, infrs)
                                  | None -> None)
                              | _ -> None) e_r_cands
            with
            | Some (_, (exp_m, infrs)) -> Some (infrs@[Auto.transitivity scp exp_x exp_m exp_v])
            | None -> None)

    (* generate e_ll >= e_r if possible *)
    (* when e_l = e_r, return (Some []) *)
    and try_subst (scp:Auto.scope_t) (inv_u:Invariant.unary) (e_ll:Expr.t)
                  (e_l:Expr.t) (e_r:Expr.t)
        : (Infrule.t list) option =
      match e_l, e_r with
      | Expr.Coq_value _, _
      | _, Expr.Coq_value _ -> None
      | _, _->
         let fst_result =
           match Auto.eq_exps_values e_l e_r with
           | Some vpl -> try_subst_intl scp inv_u e_l e_l vpl []
           | _ -> None
         in
         (match fst_result with
          | Some infrs -> Some (infrs@[Auto.transitivity scp e_ll e_l e_r])
          | None ->
             (* modify and try again *)
             (match try_modify scp e_ll e_l with
              | Some (infrs, e_l_sw) ->
                 (match Auto.eq_exps_values e_l_sw e_r with
                  | Some vpl ->
                     try_subst_intl scp inv_u e_l_sw e_l_sw vpl infrs
                  | _ -> None)
              | _ -> None))

    (* generate e_l >= e_l[rep vpl] *)
    (* when e_l = e_l[rep vpl], return (Some []) *)
    and try_subst_intl (scp:Auto.scope_t) (inv_u : Invariant.unary)
                       (e_l:Expr.t) (e_m:Expr.t) (* (e_r:Expr.t) *)
                       (vpl: (ValueT.t * ValueT.t) list) (infrs_acc:Infrule.t list)
        : (Infrule.t list) option =
      match vpl with
      | [] -> Some infrs_acc
      | (vl, vr)::vpl_t ->
         if ValueT.eq_dec vl vr
         then try_subst_intl scp inv_u e_l e_m (* e_r *) vpl_t infrs_acc
         else
           (match vl with
            | ValueT.Coq_id x ->
               (match try_trans scp inv_u x vr with
                | Some infrs_v ->
                   let e_m_new = Auto.substitute_expr x vr e_m in
                   let infrs_new =
                     infrs_acc@infrs_v@[Auto.substitute scp x vr e_m]@
                       if Expr.eq_dec e_l e_m then []
                       else [Auto.transitivity scp e_l e_m e_m_new]
                   in
                   try_subst_intl scp inv_u e_l e_m_new (* e_r *) vpl_t infrs_new
                | None -> None)
            | _ -> None)

  end

module AutoGVNModule = struct
    type ghost_intd_t = (id * Expr.t) list

    let find_ghost_pair scp ld (l:ghost_intd_t) (x:id) : Expr.t option =
      match List.filter (fun (a, b) -> AtomImpl.eq_atom_dec a x) l with
      | (_, b)::_ -> Some b
      | _ ->
         let get_list = match scp with Auto.Src -> Auto.get_lhs_list | _ -> Auto.get_rhs_list in
         match get_list ld (Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, x))) with
         | e::_ -> Some e
         | _ -> None

    let exp_phys x = Expr.Coq_value (ValueT.Coq_id (Tag.Coq_physical, x))
    let exp_ghost x = Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, x))

    let extract_ghostid e =
      match e with
      | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, g)) -> Some g
      | _ -> None

    let check_matched e ep : Expr.t option =
      let check_matched_one e1 e2 =
        Expr.same_modulo_value e1 e2 ||
        match e1, e2 with
        | Expr.Coq_gep _, Expr.Coq_gep _ -> true
        | _, _ -> false in
      let (e1, e2) = ep in
      if check_matched_one e e1 then Some e1
      else if check_matched_one e e2 then Some e2 else None

    let attach_oinfrs h t oinfrs =
      match oinfrs with
      | Some infrs -> Some (h@infrs@t)
      | _ -> None

    let try_resolve_icmp scp ld e1 e2 : (Infrule.t list) option =
      match e1, e2 with
      | Expr.Coq_icmp (c, ty, v1, v2),
        Expr.Coq_value (ValueT.Coq_const (LLVMsyntax.Coq_const_int (1, b))) ->
         let c_inv = get_inverse_icmp_cond c in
         let b_inv = get_inverse_boolean_Int b in
         let e1_new = Expr.Coq_icmp (c_inv, ty, v1, v2) in
         let e2_new = Expr.Coq_value (ValueT.Coq_const (LLVMsyntax.Coq_const_int (1, b_inv))) in
         attach_oinfrs [] [Auto.icmp_inverse scp c_inv ty v1 v2 b_inv]
                       (AutoTransHelper.run_unary_i scp ld e1_new e2_new)
      | Expr.Coq_value (ValueT.Coq_const (LLVMsyntax.Coq_const_int (1, b))),
        Expr.Coq_icmp (c, ty, v1, v2) ->
         let c_inv = get_inverse_icmp_cond c in
         let b_inv = get_inverse_boolean_Int b in
         let e2_new = Expr.Coq_icmp (c_inv, ty, v1, v2) in
         let e1_new = Expr.Coq_value (ValueT.Coq_const (LLVMsyntax.Coq_const_int (1, b_inv))) in
         attach_oinfrs [] [Auto.icmp_inverse_rhs scp c_inv ty v1 v2 b_inv]
                       (AutoTransHelper.run_unary_i scp ld e1_new e2_new)
      | _, _ -> None

    let resolve_one_ld scp ld ld_other acc_ghosts e1 e2 : (Infrule.t list * ghost_intd_t) option =
      print_endline "AutoGVNModule: resolve_one_ld start";
      if ExprPairSet.mem (e1, e2) ld then Some ([],[]) else
      let get_list = match scp with Auto.Src -> Auto.get_rhs_list | _ -> Auto.get_lhs_list in
      let get_cmpl_val scp ld x : ValueT.t option =
        let f = match scp with Auto.Src -> Auto.get_rhs_list | Auto.Tgt -> Auto.get_lhs_list in
        match Auto.find_first_match
                (fun e -> match e with Expr.Coq_value v -> Some v | _ -> None)
                (f ld (Expr.Coq_value (ValueT.Coq_id x))) with
        | Some (_, v) -> Some v
        | _ -> None
      in
      let (e_g, e_other) = match scp with Auto.Src -> (e2, e1) | _ -> (e1, e2) in
      match extract_ghostid e_g with
      | None ->
         let second_try =
           match NewAutoSubstTransHelper.run 0 scp ld None e1 e2 None with
           | Some infrs -> Some infrs
           | None -> try_resolve_icmp scp ld e1 e2
         in (match second_try with Some infrs -> Some (infrs, acc_ghosts) | None -> None)
      | Some g ->
         let resolve_ghost_result =
           match find_ghost_pair scp ld acc_ghosts g with
           | Some e -> Some (e, [], acc_ghosts)
           | None ->
              let e_cand_opts =
                match e_other with
                | Expr.Coq_value v ->
                   (match v with
                    | ValueT.Coq_id (Tag.Coq_physical, x) ->
                       List.filter
                         (fun e -> match e with Expr.Coq_value _ -> false | _ -> true)
                         (get_list ld e_other)
                    | _ -> [])
                | _ -> [e_other]
              in
              match e_cand_opts with
              | [] -> None
              | e_cand::_ -> 
                 (* let e_cand_gs = List.map *)
                 let e_cand_g =
                   List.fold_left
                     (fun e_acc v_op ->
                      match v_op with
                      | ValueT.Coq_id x ->
                         (match get_cmpl_val scp ld x with
                          | Some v -> Auto.substitute_expr x v e_acc
                          | None -> e_acc
                         )
                      | _ -> e_acc) e_cand (Expr.get_valueTs e_cand)
                 in
                 let process_gep_inbounds scp ld e : Expr.t =
                   match e with
                   | Expr.Coq_gep (inb, tya, v, lsv, tyb) ->
                      if (match scp with
                          | Auto.Src -> not inb
                          | Auto.Tgt -> inb)
                      then e
                      else
                        (match
                            Auto.find_first_match
                              (fun e ->
                               match e with
                               | Expr.Coq_gep (inb2, _, _, _, _) when inb2 <> inb -> Some e
                               | _ -> None)
                              (let lp = List.split (ExprPairSet.elements ld) in
                               (fst lp)@(snd lp))
                          with
                          | Some (_, _) -> Expr.Coq_gep (not inb, tya, v, lsv, tyb)
                          | None -> e)
                   | _ -> e
                 in
                 let e_cand_g = process_gep_inbounds scp ld e_cand_g in
                 Some (e_cand_g, [Infrule.Coq_intro_ghost (e_cand_g, g)], (g, e_cand_g)::acc_ghosts)
         in
         match resolve_ghost_result with
         | None -> None
         | Some (e_intr, infrs1, acc_ghosts2) ->
            let (oell, el, er, oerr) =
              match scp with
              | Auto.Src -> (None, e_other, e_intr, Some e_g)
              | Auto.Tgt -> (Some e_g, e_intr, e_other, None)
            in
            print_endline ("before calling SubstTrans: "^(Printer.ExprsToString.of_expr el)^(Printer.ExprsToString.of_expr er));
            match NewAutoSubstTransHelper.run 0 scp ld oell el er oerr with
            | None -> None
            | Some infrs2 -> Some (infrs1@infrs2, acc_ghosts2)

    let rec run_intl (scp:Auto.scope_t) (ld:ExprPairSet.t) (ld_other:ExprPairSet.t) (ldl_g:ExprPair.t list)
                     (acc_ghosts:ghost_intd_t) (acc_infrs:Infrule.t list) (acc_ld:ExprPairSet.t)
      : ghost_intd_t * (Infrule.t list) * ExprPairSet.t =
      print_endline "AutoGVNModule: run_intl start";
      match ldl_g with
      | (e1, e2)::ldl_g_t ->
         (match resolve_one_ld scp ld ld_other acc_ghosts e1 e2 with
          | None -> run_intl scp ld ld_other ldl_g_t acc_ghosts acc_infrs acc_ld
          | Some (infrs, gxl) ->
             run_intl scp ld ld_other ldl_g_t (gxl@acc_ghosts) (acc_infrs@infrs)
                      (ExprPairSet.remove (e1, e2) acc_ld))
      | [] -> (acc_ghosts, acc_infrs, acc_ld)
      
    let auto1 : Auto.t1 =
      fun inv inv_g ->
      (* let ghost_intd : ghost_intd_t = gather_ghost inv in *)
      let ghost_intd, infrs1, ld_src =
        print_endline "auto1 - run_intl src";
        run_intl Auto.Src inv.Invariant.src.Invariant.lessdef inv.Invariant.tgt.Invariant.lessdef
                 (ExprPairSet.elements inv_g.Invariant.src.Invariant.lessdef)
                 [] [] inv_g.Invariant.src.Invariant.lessdef
      in
      print_endline ("len infrs1:"^(string_of_int (List.length infrs1)));
      let _, infrs2, ld_tgt =
        print_endline "auto1 - run_intl tgt";
        run_intl Auto.Tgt inv.Invariant.tgt.Invariant.lessdef inv.Invariant.src.Invariant.lessdef
                 (ExprPairSet.elements inv_g.Invariant.tgt.Invariant.lessdef)
                 ghost_intd  [] inv_g.Invariant.tgt.Invariant.lessdef in
      print_endline ("len infrs2:"^(string_of_int (List.length infrs2)));
      print_endline "auto1 almost done";
      (infrs1@infrs2,
       Invariant.update_src
         (Invariant.update_lessdef (fun _ -> ld_src))
         (Invariant.update_tgt
            (Invariant.update_lessdef (fun _ -> ld_tgt)) inv_g))

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

    let run (inv:Invariant.t) (inv_goal:Invariant.t)
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

    let run (inv:Invariant.t) (inv_goal:Invariant.t)
        : Infrule.t list * Invariant.t =
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
  end

(** 2. AutoInjectValues *)
module type AutoInjVal = sig
    val run : Auto.t2
  end

(* module AutoInjectValues (GEN:InjectExprGenerator): AutoInjVal = struct *)
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

(** Instances of Resolving Next Invariant *)
module AutoRemMD_SubstTransSrc : AutoNextInv =
  AutoRemMD
    (struct
        let f = fun inv v1 v2 ->
          let exp1 = Expr.Coq_value v1 in
          let exp2 = Expr.Coq_value v2 in
          let e_src_cands =
            Auto.get_rhs_list inv.Invariant.src.Invariant.lessdef exp1 in
          let e_tgt_cands =
            Auto.get_lhs_list inv.Invariant.tgt.Invariant.lessdef exp2 in
          match 
            Auto.expr_find_first_match2
              (fun e1 e2 ->
               AutoSubstTransHelper.try_subst Auto.Src inv.Invariant.src exp1 e1 e2)
              e_src_cands e_tgt_cands
          with
          | Some (_, _, v) -> Some v
          | _ -> None
      end)

module AutoUnaryLD_SubstTrans : AutoNextInv =
  AutoUnaryLD
    (struct
        let f = fun scp inv_u e1 e2 ->
          match e1, e2 with
          | Expr.Coq_value (ValueT.Coq_id x), Expr.Coq_value v ->
             AutoSubstTransHelper.try_trans scp inv_u x v
          | _, _ -> None
      end)

module AutoUnaryLD_Trans : AutoNextInv =
  AutoUnaryLD
    (struct
        let f = AutoTransHelper.run_unary
      end)

(* module AutoUnaryLD_GVNModule : AutoNextInv = *)
(*   AutoUnaryLD *)
(*     (struct *)
(*         let f = AutoGVNModule.run_unary *)
(*       end) *)

module Auto_Default1 : AutoNextInv = struct
    let run : Auto.t1 = fun _ r -> ([], r)
  end

(** Instances of AutoInjectValues *)
module AutoInjectValues_SubstTransSrc : AutoInjVal =
  AutoInjectValues
    (struct
        let f = fun inv v1 v2 ->
          match v1 with
          | ValueT.Coq_id x ->
             if Invariant.not_in_maydiff inv v2
             then AutoSubstTransHelper.try_trans
                    Auto.Src inv.Invariant.src x v2
             else None
          | _ -> None
      end)

module AutoInjectValues_Trans : AutoInjVal =
  AutoInjectValues
    (struct
        let f inv v1 v2 = AutoTransHelper.run_inj inv (Expr.Coq_value v1) (Expr.Coq_value v2)
      end)

module Auto_Default2 : AutoInjVal = struct
    let run : Auto.t2 = fun _ vp -> ([], vp)
  end

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

(** candidates *)

let autoGVN : Auto.t = (AutoGVNModule.auto1, Auto_Default2.run)
let autoSROA : Auto.t = (AutoUnaryLD_Trans.run, AutoInjectValues_Trans.run)
let autoDflt : Auto.t = (Auto_Default1.run, Auto_Default2.run)

let autoTest1 : Auto.t = (AutoRemMD_SubstTransSrc.run, Auto_Default2.run)
let autoTest2 : Auto.t = (AutoUnaryLD_SubstTrans.run, Auto_Default2.run)
let autoTest3 : Auto.t = (AutoUnaryLD_Trans.run, Auto_Default2.run)
let autoTest4 : Auto.t = (Auto_Default1.run, AutoInjectValues_SubstTransSrc.run)

(** interface *)

module AutoStrategy = struct
    let select : unit -> Auto.t =
      fun _ ->
      match !AutoOpt.pass_option with
      | AutoOpt.GVN -> autoGVN
      | AutoOpt.SROA -> autoSROA
      | AutoOpt.TEST1 -> autoTest1
      | AutoOpt.TEST2 -> autoTest2
      | AutoOpt.TEST3 -> autoTest3
      | AutoOpt.TEST4 -> autoTest4
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

let gen_infrules_next_inv (inv:Invariant.t) (inv_nxt:Invariant.t)
    : Infrule.t list =
  Printer.debug_print "AutoInfruleGen: gen_infrules_next_inv start";
  let run = fst (AutoStrategy.select ()) in
  let res = fst (run inv inv_nxt) in
  Printer.debug_print "AutoInfruleGen: gen_infrules_next_inv end";
  res

(* module AutoTest = struct *)
(*     let empty_inv_unary : Invariant.unary = *)
(*        { Invariant.lessdef = ExprPairSet.empty; *)
(*          Invariant.alias = *)
(*            { Invariant.diffblock = ValueTPairSet.empty; *)
(*              Invariant.noalias = PtrPairSet.empty }; *)
(*          Invariant.unique = AtomSetImpl.empty; *)
(*          Invariant.coq_private = IdTSet.empty } *)

(*      let empty_inv : Invariant.t = *)
(*        { Invariant.src = empty_inv_unary; *)
(*          Invariant.tgt = empty_inv_unary; *)
(*          Invariant.maydiff = IdTSet.empty } *)

(*      let value_of_str (s:string) : ValueT.t = *)
(*        ValueT.Coq_id (Tag.Coq_physical, s) *)
(*      let gvalue_of_str (s:string) : ValueT.t = *)
(*        ValueT.Coq_id (Tag.Coq_ghost, s) *)

(*      let vx = value_of_str "x" *)
(*      let vA = value_of_str "A" *)
(*      let vB = value_of_str "B" *)
(*      let gA = gvalue_of_str "A" *)
(*      let gy = gvalue_of_str "y" *)

(*      let ex = Expr.Coq_value vx *)
(*      let eA = Expr.Coq_value vA *)
(*      let eB = Expr.Coq_value vB *)
(*      let egA = Expr.Coq_value gA *)
(*      let egy = Expr.Coq_value gy *)

(*      let gen_pair1 e v1 v2 : ExprPair.t = *)
(*        (e, Expr.Coq_bop (LLVMsyntax.Coq_bop_add, 1, v1, v2)) *)
(*      let gen_pair2 e v1 v2 : ExprPair.t = *)
(*        (Expr.Coq_bop (LLVMsyntax.Coq_bop_add, 1, v1, v2), e) *)

(*      let expr_pair_set_add_list (epl:ExprPair.t list) *)
(*          : ExprPairSet.t -> ExprPairSet.t = *)
(*        fun eps -> *)
(*        List.fold_left *)
(*          (fun s ep -> ExprPairSet.add ep s) *)
(*          eps epl *)

(*      let inv_precond1 : Invariant.t = *)
(*        Invariant.update_src *)
(*          (Invariant.update_lessdef *)
(*             (expr_pair_set_add_list *)
(*                [gen_pair1 ex vA vB; *)
(*                 gen_pair2 ex vA vB; *)
(*                 (eA, egA) *)
(*          ])) empty_inv *)

(*      let inv_precond2 : Invariant.t = *)
(*        Invariant.update_src *)
(*          (Invariant.update_lessdef *)
(*             (expr_pair_set_add_list *)
(*                [gen_pair1 ex vA vB; *)
(*                 gen_pair2 ex vA vB; *)
(*                 (eA, egA); *)
(*                 gen_pair1 egy gA vB; *)
(*                 gen_pair2 egy gA vB *)
(*          ])) empty_inv *)

(*      let inv_postcond : Invariant.t = *)
(*        Invariant.update_src *)
(*          (Invariant.update_lessdef *)
(*             (expr_pair_set_add_list *)
(*                [gen_pair1 ex vA vB; *)
(*                 gen_pair2 ex vA vB; *)
(*                 (eA, egA); *)
(*                 (egy, ex); *)
(*                 (ex, egy); *)
(*                 gen_pair1 egy gA vB; *)
(*                 gen_pair2 egy gA vB *)
(*          ])) empty_inv *)

(*      let print_string_list sl : unit = *)
(*        let size = List.length sl in *)
(*        print_endline ("length: "^(string_of_int size)); *)
(*        List.fold_left *)
(*          (fun _ s -> (print_endline "MID"); print_endline s) *)
(*          () sl *)

(*      let infrs1, _ = AutoUnaryLD_GVNModule.run inv_precond1 inv_postcond *)
(*      let infr_strs1 = List.map Printer.PrintHints.infrule_to_string infrs1 *)
(*      let _ = print_endline "GVNModule generated infrules:" *)
(*      let _ = print_string_list infr_strs1 *)

(*      let infrs2, _ = AutoUnaryLD_GVNModule.run inv_precond2 inv_postcond *)
(*      let infr_strs2 = List.map Printer.PrintHints.infrule_to_string infrs2 *)
(*      let _ = print_endline "GVNModule generated infrules:" *)
(*      let _ = print_string_list infr_strs2 *)

(*   end *)
