open Hints
open Exprs
open Infrules
open Syntax
open MetatheoryAtom
open LLVMsyntax

module AutoOpt = struct
    type pass_t =
      GVN | SROA | INSTCOMBINE | TEST1 | TEST2 | TEST3 | TEST4 | DEFAULT
    let pass_option : pass_t ref = ref DEFAULT
  end

module Auto = struct
    type scope_t = Src | Tgt

    let transitivity (scp:scope_t) e1 e2 e3 : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_transitivity (e1, e2, e3)
      | Tgt -> Infrule.Coq_transitivity_tgt (e1, e2, e3)

    let substitute (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute (x, v, e)
      | Tgt -> Infrule.Coq_substitute_tgt (x, v, e)

    let substitute_rev (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute_rev (x, v, e)
      | Tgt -> Infrule.Coq_substitute_rev (x, v, e) (* TGT version not present *)

    let intro_ghost_unary (scp:scope_t) e x : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_intro_ghost_src (e, x)
      | Tgt -> Infrule.Coq_intro_ghost_src (e, x) (* TGT version not present *)

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

    let expr_find_first_match (f:Expr.t -> 'a option)
                              (exp_list:Expr.t list)
        : 'a option =
      List.fold_left
        (fun acc e ->
         match acc with
         | Some res -> Some res
         | None -> f e)
        None exp_list

    let expr_find_first_match2 (f:Expr.t -> Expr.t -> 'a option)
                               (exp_list1:Expr.t list) (exp_list2:Expr.t list)
        : 'a option =
      let do_r e1 el2 =
        List.fold_left
          (fun acc e2 ->
           match acc with
           | Some res -> Some res
           | None -> f e1 e2)
          None el2
      in
      List.fold_left
        (fun acc el1 ->
         match acc with
         | Some res -> Some res
         | None -> do_r el1 exp_list2)
        None exp_list1

    let substitute_expr x v e : Expr.t =
      let x_to_v w =
        match w with
        | ValueT.Coq_id y -> if IdT.eq_dec x y then v else w
        | ValueT.Coq_const _ -> w
      in (Expr.map_valueTs e x_to_v)
  end

module AutoTransHelper = struct
    module ExprSet = FSetExtra.Make(Expr)

    let string_of_exprlist (el:Expr.t list): string =
      let sl = List.map (fun e -> Printer.ExprsToString.of_expr e) el in
      List.fold_left (fun ss s -> ss^"-"^s) "" sl

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

    let get_reachable_from_l (inv_u:Invariant.unary) (e:Expr.t)
        : ExprSet.t * ExprPairSet.t =
      get_reachable (Auto.get_rhs_list inv_u.Invariant.lessdef)
                    [e] (ExprSet.singleton e) ExprPairSet.empty

    let get_reachable_from_r (inv_u:Invariant.unary) (e:Expr.t)
        : ExprSet.t * ExprPairSet.t =
      get_reachable (Auto.get_lhs_list inv_u.Invariant.lessdef)
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
      let (rch_src, gr_src) = get_reachable_from_l inv.Invariant.src e1 in
      let (rch_tgt, gr_tgt) = get_reachable_from_r inv.Invariant.tgt e2 in
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

    let run_unary (scp:Auto.scope_t) (inv_u:Invariant.unary)
                  (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      Printer.debug_print "AutoInfruleGen: Transitivity-Unary start";
      let (rch, gr) = get_reachable_from_l inv_u e1 in
      let path = get_path [] gr e1 e2 in
      Some (gen_infrules scp path)
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
        | Some infrs -> Some infrs
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
            | Some (exp_m, infrs) -> Some (infrs@[Auto.transitivity scp exp_x exp_m exp_v])
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

module AutoNewGVN = struct
    let extract_target_pair e1 e2 : (Expr.t * Expr.t * id) option =
      (* find ghost and reorder exprs*)
      match e1, e2 with
      | Expr.Coq_value (ValueT.Coq_id x1), Expr.Coq_value (ValueT.Coq_id x2) ->
         (match fst x1, fst x2 with
          | Tag.Coq_ghost, Tag.Coq_physical -> Some (e2, e1, snd x1)
          | _, _ -> None)
      | _, _ -> None

    let exists_in_inv_u (inv_u:Invariant.unary) (e:Expr.t) : bool =
      ExprPairSet.exists_ (fun ep -> Expr.eq_dec e (fst ep) || Expr.eq_dec e (snd ep))
                          inv_u.Invariant.lessdef

    let lookup_ghost_of ld x : ValueT.t option =
      let e_v = Expr.Coq_value (ValueT.Coq_id x) in
      let exprs = Auto.get_rhs_list ld e_v in
      Auto.expr_find_first_match
        (fun e -> match e with
                  | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_ghost, g)) ->
                     Some (ValueT.Coq_id (Tag.Coq_ghost, g))
                  | _ -> None)
	      exprs

    let substitute_ghosts scp ld e_x e : Infrule.t list * Expr.t =
      let rec try_find_ghost e_prev v e_new_mkr : Infrule.t list * Expr.t * ValueT.t =
        match v with
        | ValueT.Coq_const _ -> ([], e_new_mkr v, v)
        | ValueT.Coq_id i ->
           match lookup_ghost_of ld i with
           | Some v_g -> ([Auto.substitute scp i v_g e_prev;
                           Auto.transitivity scp e_x e_prev (e_new_mkr v_g);
                           Auto.substitute_rev scp i v_g e_prev;
                           Auto.transitivity scp (e_new_mkr v_g) e_prev e_x
                          ],
                          e_new_mkr v_g, v_g)
           | None -> ([], e_new_mkr v, v)
      and try_find_ghost_l e_prev svl_prev svl_next e_new_mkr
          : Infrule.t list * Expr.t =
        match svl_next with
        | (sz, v1)::svl_next_t ->
           let infrs1, e1, nv1 =
             try_find_ghost e_prev v1 (fun v -> e_new_mkr (svl_prev@[(sz, v)]@svl_next_t)) in
           let infrs2, ef = try_find_ghost_l e1 (svl_prev@[(sz, nv1)]) svl_next_t e_new_mkr in
           (infrs1@infrs2, ef)
        | _ -> ([], e_prev)
      in
      match e with
      | Expr.Coq_bop (op, sz, v1, v2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_bop (op, sz, v, v2)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_bop (op, sz, nv1, v)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_fbop (op, fp, v1, v2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_fbop (op, fp, v, v2)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_fbop (op, fp, nv1, v)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_extractvalue (ty1, v1, cl, ty2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_extractvalue (ty1, v, cl, ty2)) in
         (infrs1, e1)
      | Expr.Coq_insertvalue (ty1, v1, ty2, v2, cl) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_insertvalue (ty1, v, ty2, v2, cl)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_insertvalue (ty1, nv1, ty2, v, cl)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_gep (inb, ty1, v1, svl, ty2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_gep (inb, ty1, v, svl, ty2)) in
         let infrs2, e2 = try_find_ghost_l e1 [] svl (fun vl -> Expr.Coq_gep (inb, ty1, nv1, vl, ty2)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_trunc (op, ty1, v1, ty2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_trunc (op, ty1, v, ty2)) in
         (infrs1, e1)
      | Expr.Coq_ext (op, ty1, v1, ty2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_ext (op, ty1, v, ty2)) in
         (infrs1, e1)
      | Expr.Coq_cast (op, ty1, v1, ty2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_cast (op, ty1, v, ty2)) in
         (infrs1, e1)
      | Expr.Coq_icmp (c, ty, v1, v2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_icmp (c, ty, v, v2)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_icmp (c, ty, nv1, v)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_fcmp (c, fp, v1, v2) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_fcmp (c, fp, v, v2)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_fcmp (c, fp, nv1, v)) in
         (infrs1@infrs2, e2)
      | Expr.Coq_select (v1, ty, v2, v3) ->
         let infrs1, e1, nv1 = try_find_ghost e v1 (fun v -> Expr.Coq_select (v, ty, v2, v3)) in
         let infrs2, e2, nv2 = try_find_ghost e1 v2 (fun v -> Expr.Coq_select (nv1, ty, v, v3)) in
         let infrs3, e3, _ = try_find_ghost e2 v3 (fun v -> Expr.Coq_select (nv1, ty, nv2, v)) in
         (infrs1@infrs2@infrs3, e3)
      | Expr.Coq_value v1 ->
         let infrs1, e1, _ = try_find_ghost e v1 (fun v -> Expr.Coq_value v) in
         (infrs1, e1)
      | Expr.Coq_load (v1, ty, a) ->
         let infrs1, e1, _ = try_find_ghost e v1 (fun v -> Expr.Coq_load (v, ty, a)) in
         (infrs1, e1)

    let substitute_expr_to_ghosts scp inv_u e_x: (Infrule.t list) * Expr.t =
      let rhs_l = Auto.get_rhs_list inv_u.Invariant.lessdef e_x in
      let lhs_l = Auto.get_lhs_list inv_u.Invariant.lessdef e_x in
      match List.filter (fun e -> List.exists (Expr.eq_dec e) rhs_l) lhs_l with
      | e::_ -> substitute_ghosts scp inv_u.Invariant.lessdef e_x e
      | _ -> ([], e_x) (* error *)

    let transitivity_duplex scp e1 e2 e3 : Infrule.t list =
      [Auto.transitivity scp e1 e2 e3;
       Auto.transitivity scp e3 e2 e1]

    let run_unary (scp:Auto.scope_t) (inv_u:Invariant.unary)
                  (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      Printer.debug_print "AutoInfruleGen: AutoNewGVN.run_unary start";
      match extract_target_pair e1 e2 with (* handling phys-ghost pair *)
      | Some (e_x, e_g, id_g) ->
         let infrs1, expr_x_gs = substitute_expr_to_ghosts scp inv_u e_x in
         if exists_in_inv_u inv_u e_g
         then
           let infrs2 = transitivity_duplex scp e_x expr_x_gs e_g in
           Some (infrs1@infrs2)
         else
           let infrs2 = transitivity_duplex scp e_g e_x expr_x_gs in
           Some ((Auto.intro_ghost_unary scp e_x id_g)::(infrs1@infrs2))
      | _ ->
         (match e1, e2 with (* handling repl_inv *)
          | Expr.Coq_value (ValueT.Coq_id (Tag.Coq_physical, id_rem)),
            Expr.Coq_value (ValueT.Coq_id (Tag.Coq_physical, id_repl)) ->
             (match lookup_ghost_of inv_u.Invariant.lessdef (Tag.Coq_physical, id_repl) with
              | Some v_g ->
                 let infrs1, expr_rem_gs = substitute_expr_to_ghosts scp inv_u e1 in
                 let infrs2 = [Auto.transitivity scp e1 expr_rem_gs (Expr.Coq_value v_g)] in
                 let infrs3 = [Auto.transitivity scp e1 (Expr.Coq_value v_g) e2] in
                 Some (infrs1@infrs2@infrs3)
              | None -> None)
          | _, _ -> None)
  end

(** AutoInfruleGenerator Framework *)
type auto1_t = Invariant.t -> Invariant.t -> (Infrule.t list * Invariant.t)
type auto2_t = Invariant.t -> ValueTPair.t list -> (Infrule.t list * ValueTPair.t list)
type auto_t = auto1_t * auto2_t

(** Framework 1. AutoNextInvariant *)
module type AutoNextInv = sig
    val run : auto1_t
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
    val run : auto2_t
  end

(* module AutoInjectValues (GEN:InjectExprGenerator): AutoInjVal = struct *)
module AutoInjectValues (GEN:InjectValueGenerator): AutoInjVal = struct
    let rec run_intl (inv:Invariant.t) (vpl_acc:ValueTPair.t list)
                     (infrs_acc:Infrule.t list) (vpl:ValueTPair.t list)
            : Infrule.t list * (ValueTPair.t list) =
      match vpl with
      | [] -> (infrs_acc, vpl_acc)
      | (v_l, v_r)::vpl_t ->
         (* (match GEN.f inv (Expr.Coq_value v_l) (Expr.Coq_value v_r) with *)
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
          Auto.expr_find_first_match2
            (fun e1 e2 ->
             AutoSubstTransHelper.try_subst Auto.Src inv.Invariant.src exp1 e1 e2)
             (* TODO: check e2 disjoint with MD *)
             (* match AutoSubstTransHelper.try_subst Auto.Src inv.Invariant.src exp1 e1 e2 with *)
             (* | Some infrs -> *)
             (*    Some (infrs@[Auto.transitivity Auto.Src exp1 e1 e2]) *)
             (* | None -> None) *)
            e_src_cands e_tgt_cands
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

module AutoUnaryLD_NewGVN : AutoNextInv =
  AutoUnaryLD
    (struct
        let f = AutoNewGVN.run_unary
      end)

module Auto_Default1 : AutoNextInv = struct
    let run : auto1_t = fun _ r -> ([], r)
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
    let run : auto2_t = fun _ vp -> ([], vp)
  end

(** candidates *)

let autoGVN : auto_t = (AutoUnaryLD_NewGVN.run, Auto_Default2.run)
let autoSROA : auto_t = (AutoUnaryLD_Trans.run, AutoInjectValues_Trans.run)
let autoDflt : auto_t = (Auto_Default1.run, Auto_Default2.run)

let autoTest1 : auto_t = (AutoRemMD_SubstTransSrc.run, Auto_Default2.run)
let autoTest2 : auto_t = (AutoUnaryLD_SubstTrans.run, Auto_Default2.run)
let autoTest3 : auto_t = (AutoUnaryLD_Trans.run, Auto_Default2.run)
let autoTest4 : auto_t = (Auto_Default1.run, AutoInjectValues_SubstTransSrc.run)

(** interface *)

module AutoStrategy = struct
    let select : unit -> auto_t =
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

(*      let infrs1, _ = AutoUnaryLD_NewGVN.run inv_precond1 inv_postcond *)
(*      let infr_strs1 = List.map Printer.PrintHints.infrule_to_string infrs1 *)
(*      let _ = print_endline "NewGVN generated infrules:" *)
(*      let _ = print_string_list infr_strs1 *)

(*      let infrs2, _ = AutoUnaryLD_NewGVN.run inv_precond2 inv_postcond *)
(*      let infr_strs2 = List.map Printer.PrintHints.infrule_to_string infrs2 *)
(*      let _ = print_endline "NewGVN generated infrules:" *)
(*      let _ = print_string_list infr_strs2 *)
 
(*   end *)
