open Hints
open Exprs
open Syntax
open MetatheoryAtom
open LLVMsyntax

(* flags for turning on/off certain automations *)
(* let flag_tran : bool ref = ref true *)
(* let flag_comm : bool ref = ref false *)

module AutoScope = struct
    type t = Src | Tgt

    let transitivity (scp:t) e1 e2 e3
        : Infrule.t =
      (* let transitivity (scp:t) e1 e2 e3: Infrule.t = *)
      match scp with
      | Src -> Infrule.Coq_transitivity (e1, e2, e3)
      | Tgt -> Infrule.Coq_transitivity_tgt (e1, e2, e3)

    let substitute (scp:t) x v e
        : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute (x, v, e)
      | Tgt -> Infrule.Coq_substitute_tgt (x, v, e)

    let inv_unary (scp:t) : Invariant.t -> Invariant.unary =
      match scp with
      | Src -> Invariant.src
      | Tgt -> Invariant.tgt

    let update_unary (scp:t)
        : (Invariant.unary -> Invariant.unary) ->
          Invariant.t -> Invariant.t =
      match scp with
      | Src -> Invariant.update_src
      | Tgt -> Invariant.update_tgt
  end

module AutoUtils = struct
    let eq_exp_pair_args (e1:Expr.t) (e2:Expr.t)
        : ((ValueT.t * ValueT.t) list) option =
      if Expr.same_modulo_value e1 e2
      then Some (List.combine (Expr.get_valueTs e1) (Expr.get_valueTs e2))
      else None

    (* let eq_exp_pair_args (e1:Expr.t) (e2:Expr.t) *)
    (*     : ((ValueT.t * ValueT.t) list) option = *)
    (*   match e_l, e_r with *)
    (*   | Expr.Coq_bop (bop1, sz1, va1, vb1), Expr.Coq_bop (bop2, sz2, va2, vb2) *)
    (*        when bop1 = bop2 && sz1 = sz2 -> *)
    (*      Some [(va1, va2); (vb1, vb2)] *)
    (*   | Expr.Coq_fbop (bop1, fp1, va1, vb1), Expr.Coq_fbop (bop2, fp2, va2, vb2) *)
    (*        when bop1 = bop2 && fp1 = fp2 -> *)
    (*      Some [(va1, va2); (vb1, vb2)] *)
    (*   | Expr.Coq_extractvalue (tya1, v1, cl1, tyb1), Expr.Coq_extractvalue (tya2, v2, cl2, tyb2) *)
    (*        when tya1 = tya2 && cl1 = cl2 && tyb1 = tyb2 -> *)
    (*      Some [(v1, v2)] *)
    (*   | Expr.Coq_insertvalue (tya1, va1, tyb1, vb1, cl1), Expr.Coq_insertvalue (tya2, va2, tyb2, vb2, cl2) *)
    (*        when tya1 = tya2 && tyb1 = tyb2 && cl1 = cl2 -> *)
    (*      Some [(va1, va2); (vb1, vb2)] *)
    (*   | Expr.Coq_gep (inb1, tya1, v1, svl1, tyb1), Expr.Coq_gep (inb2, tya2, v2, svl2, tyb2) *)
    (*        when inb1 = inb2 && tya1 = tya2 && tyb1 = tyb2 -> *)
    (*      (match svls2vpl with *)
    (*       | Some vpl -> (v1, v2)::vpl *)
    (*       | None -> None) *)
    (*   | Expr.Coq_trunc (op1, tya1, v1, tyb1), Expr.Coq_trunc (op2, tya2, v2, tyb2) *)
    (*        when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 -> *)
    (*      Some [(v1, v2)] *)
    (*   | Expr.Coq_ext (op1, tya1, v1, tyb1), Expr.Coq_ext (op2, tya2, v2, tyb2) *)
    (*        when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 -> *)
    (*      Some [(v1, v2)] *)
    (*   | Expr.Coq_cast (op1, tya1, v1, tyb1), Expr.Coq_cast (op2, tya2, v2, tyb2) *)
    (*        when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 -> *)
    (*      Some [(v1, v2)] *)
    (*   | Expr.Coq_icmp (c1, ty1, va1, vb1), Expr.Coq_icmp (c2, ty2, va2, vb2) *)
    (*        when c1 = c2 && ty1 = ty2 -> *)
    (*      Some [(va1, va2); (vb1, vb2)] *)
    (*   | Expr.Coq_fcmp (c1, fp1, va1, vb1), Expr.Coq_fcmp (c2, fp2, va2, vb2) *)
    (*        when c1 = c2 && fp1 = fp2 -> *)
    (*      Some [(va1, va2); (vb1, vb2)] *)
    (*   | Expr.Coq_select (va1, ty1, vb1, vc1), Expr.Coq_select (va2, ty2, vb2, vc2) *)
    (*        when ty1 = ty2 -> *)
    (*      Some [(va1, va2); (vb1, vb2); (vc1, vc2)] *)
    (*   | Expr.Coq_value v1, Expr.Coq_value v2 -> *)
    (*      Some [(v1, v2)] *)
    (*   | Expr.Coq_load (v1, ty1, a1), Expr.Coq_load (v2, ty2, a2) *)
    (*        when ty1 = ty2 -> (\* should we compare align? *\) *)
    (*      Some [(v1, v2)] *)
    (*   | _, _ -> None *)

    let get_rhs_list (lessdef:ExprPairSet.t) (e:Expr.t)
        : Expr.t list =
      let ep_set = Invariant.get_rhs lessdef e in
      List.map snd (ExprPairSet.elements ep_set)

    let get_lhs_list (lessdef:ExprPairSet.t) (e:Expr.t)
        : Expr.t list =
      let ep_set = Invariant.get_lhs lessdef e in
      List.map fst (ExprPairSet.elements ep_set)

    let try_expr2 (f:Expr.t -> Expr.t -> 'a option) (exp_list1:Expr.t list) (exp_list2:Expr.t list)
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

module AutoTransitivity = struct
    (* e_src <> e_dest *)
    (* e_src and e_dest are not in trace *)
    let rec find_chain (trace:Expr.t list) (lessdef:ExprPairSet.t)
                       (e_l:Expr.t) (e_r:Expr.t)
            : (Expr.t list) option =
      if ExprPairSet.mem (e_l, e_r) lessdef
      then Some (e_l::e_r::trace)
      else
        let cands = AutoUtils.get_lhs_list lessdef e_r in
        let cands_filtered : Expr.t list =
          List.filter (fun e -> List.mem e trace) cands in
        AutoUtils.try_expr2 (find_chain (e_r::trace) lessdef) [e_l] cands_filtered
        (* let rec search_cands cands = *)
        (*   match cands with *)
        (*   | [] -> None *)
        (*   | c::cands_t -> *)
        (*      (match find_chain e_l c (e_r::trace) lessdef with *)
        (*       | Some chain -> chain *)
        (*       | None -> search_cands cands_t) *)
        (* in search_cands cands_filtered *)

    let rec gen_infrules (scp:AutoScope.t) (chain:Expr.t list)
            : Infrule.t list =
      match chain with
      | e1::e2::e3::chain_t ->
         (AutoScope.transitivity scp e1 e2 e3)::
           (gen_infrules scp (e1::e3::chain_t))
      | _ -> []

    (* ep from ld_goal *)
    let run_each (scp:AutoScope.t) (ld:ExprPairSet.t)
                 (ep:Expr.t * Expr.t) (ld_goal:ExprPairSet.t)
        : Infrule.t list * ExprPairSet.t =
      if ExprPairSet.mem ep ld
      then ([], ExprPairSet.remove ep ld_goal)
      else
        match find_chain [] ld (fst ep) (snd ep) with
        | Some el ->
           (gen_infrules scp el, ExprPairSet.remove ep ld_goal)
        | None -> ([], ld_goal)

    let run (scp:AutoScope.t) (inv:Invariant.t) (inv_goal:Invariant.t)
        : Infrule.t list * Invariant.t =
      let inv_unary = AutoScope.inv_unary scp inv in
      let inv_unary_goal = AutoScope.inv_unary scp inv_goal in
      let ld = inv_unary.Invariant.lessdef in
      let ld_goal = inv_unary_goal.Invariant.lessdef in

      let (infrs_final, ld_final) =
        ExprPairSet.fold
          (fun ep (infrs_m, ld_m) ->
           let (infrs_r, ld_r) = run_each scp ld ep ld_m in
           (infrs_m@infrs_r, ld_r))
          ld_goal ([], ld_goal)
      in (infrs_final,
          AutoScope.update_unary
            scp (Invariant.update_lessdef (fun _ -> ld_final)) inv_goal)
  end

module AutoSubstTrans = struct
    (* produce x >= v applying seq of subst-transitivity *)
    let rec run (scp:AutoScope.t) (inv_u : Invariant.unary)
                (x : IdT.t) (v : ValueT.t)
            : (Infrule.t list) option =
      if ValueT.Coq_id x = v then Some [] else
        let exp_x = (Expr.Coq_value (ValueT.Coq_id x)) in
        let exp_v = (Expr.Coq_value v) in

        let e_l_cands = AutoUtils.get_rhs_list inv_u.Invariant.lessdef exp_x in
        let e_r_cands = AutoUtils.get_lhs_list inv_u.Invariant.lessdef exp_v in
        AutoUtils.try_expr2
          (fun e_l e_r ->
           if e_l = e_r
           then Some [AutoScope.transitivity scp exp_x e_l exp_v]
           else
             match try_subst scp inv_u e_l e_r with
             | Some infrs ->
                Some (infrs@[AutoScope.transitivity scp exp_x e_l e_r;
                             AutoScope.transitivity scp exp_x e_r exp_v])
             | None -> None)
          e_l_cands e_r_cands
        (* match AutoUtils.try_expr2 (try_subst scp inv_u) e_l_cands e_r_cands with *)
        (* | Some infrs -> *)
        (*    Some (infrs@[AutoScope.transitivity scp exp_x e_l e_r; *)
        (*                 AutoScope.transitivity scp exp_x e_r exp_v]) *)
        (* | None -> None *)

    (* generate e_l >= e_r if possible *)
    (* when e_l = e_r, return (Some []) *)
    and try_subst (scp:AutoScope.t) (inv_u:Invariant.unary)
                  (e_l:Expr.t) (e_r:Expr.t)
        : (Infrule.t list) option =
      match AutoUtils.eq_exp_pair_args e_l e_r with
      | Some vpl ->
         try_subst_intl scp inv_u e_l e_l vpl []
      | _ -> None

    (* generate e_l >= e_l[rep vpl] *)
    (* when e_l = e_l[rep vpl], return (Some []) *)
    and try_subst_intl (scp:AutoScope.t) (inv_u : Invariant.unary)
                       (e_l:Expr.t) (e_m:Expr.t) (* (e_r:Expr.t) *)
                       (vpl: (ValueT.t * ValueT.t) list) (infrs_acc:Infrule.t list)
        : (Infrule.t list) option =
      match vpl with
      | [] -> Some infrs_acc
      | (vl, vr)::vpl_t ->
         if vl = vr then try_subst_intl scp inv_u e_l e_m (* e_r *) vpl_t infrs_acc
         else
           (match vl with
            | ValueT.Coq_id x ->
               (match run scp inv_u x vr with
                | Some infrs_v ->
                   let e_m_new = AutoUtils.substitute_expr x vr e_m in
                   let infrs_new =
                     infrs_acc@infrs_v@[AutoScope.substitute scp x vr e_m]@
                       if e_l = e_m then []
                       else [AutoScope.transitivity scp e_l e_m e_m_new]
                   in
                   try_subst_intl scp inv_u e_l e_m_new (* e_r *) vpl_t infrs_new
                | None -> None)
            | _ -> None)

  end

(* TODO: make this to be functor? *)
(* TODO: remove_maydiff be unary infrule *)
module AutoRemMD = struct
    let find_inject (inv:Invariant.t) (x:IdT.t)
        : (Infrule.t list) option =
      let exp_x = Expr.Coq_value (ValueT.Coq_id x) in
      let e_src_cands = AutoUtils.get_rhs_list inv.Invariant.src.Invariant.lessdef exp_x in
      let e_tgt_cands = AutoUtils.get_lhs_list inv.Invariant.tgt.Invariant.lessdef exp_x in
      AutoUtils.try_expr2
        (fun e1 e2 ->
         match AutoSubstTrans.try_subst
                 AutoScope.Src inv.Invariant.src e1 e2 with
           | Some infrs ->
              Some (infrs@[AutoScope.transitivity
                             AutoScope.Src exp_x e1 e2])
           | None -> None)
        e_src_cands e_tgt_cands

    let rec run_intl (inv:Invariant.t) (inv_goal:Invariant.t)
                     (infrs_acc:Infrule.t list) (md:IdT.t list)
            : Infrule.t list * Invariant.t =
      match md with
      | [] -> (infrs_acc, inv_goal)
      | x::md_t ->
         (match find_inject inv x with
          | Some infrs ->
             let inv_goal_new =
               Invariant.update_maydiff
                 (IdTSet.remove x) inv_goal
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
        List.filter (fun x -> not (List.mem x md_goal)) md in
      let _ = print_endline ("len-md: " ^ string_of_int (List.length md_remain)) in
      run_intl inv inv_goal [] md_remain
  end

(* module AutoGVNInjEvt = struct *)
(*   let run (inv:Invariant.t) (inv_goal:Invariant.t) *)
(*       : Infrule.t list * Invariant.t = *)
(*     ([], inv_goal) *)
(* end *)

(* module InfrGenCmd = struct *)
(*     let params2values (ps:((typ*attributes)*value) list) *)
(*         : value list = *)
(*       List.map snd ps *)

(*     let gen (cmd_src : cmd) (cmd_tgt : cmd) (inv : Invariant.t) *)
(*         : Infrule.t list = *)
(*       match cmd_src, cmd_tgt with *)
(*       | Coq_insn_call (_, _, _, _, _, _, params1), *)
(*         Coq_insn_call (_, _, _, _, _, _, params2) -> *)
(*          let vl1 = params2values params1 in *)
(*          let vl2 = params2values params2 in *)
(*          if (List.length vl1 <> List.length vl2) then [] *)
(*          else *)
(*            let vpl = List.combine vl1 vl2 in *)
(*            List.fold_left *)
(*              (fun infr_acc (v1, v2) -> *)
(*               infr_acc @ (InfrGenUtil.gen_inject v1 v2 inv)) *)
(*              [] vpl *)
(*       | _, _ -> [] (\* implement if necessary *\) *)
(*   end *)

(* module InfrGenTerm = struct *)
(*     let gen (term_src : terminator) (term_tgt : terminator) (inv : Invariant.t) *)
(*         : Infrule.t list = *)
(*       match term_src, term_tgt with *)
(*       | Coq_insn_return (_, _, v1), Coq_insn_return (_, _, v2) *)
(*       | Coq_insn_br (_, v1, _, _), Coq_insn_br (_, v2, _, _) *)
(*       | Coq_insn_switch (_, _, v1, _, _), Coq_insn_switch (_, _, v2, _ _) -> *)
(*          InfrGenUtil.gen_inject v1 v2 inv *)
(*       | _, _ -> [] *)
(*   end *)

let gen_infrules_from_insns
      (insn_src : LLVMsyntax.insn)
      (insn_tgt : LLVMsyntax.insn)
      (inv : Invariant.t)
    : Infrule.t list =
  match insn_src, insn_tgt with
  | Coq_insn_cmd cmd_src, Coq_insn_cmd cmd_tgt ->
     (* InfrGenCmd.gen cmd_src cmd_tgt inv *)
     []
  | Coq_insn_terminator term_src, Coq_insn_terminator term_tgt ->
     (* InfrGenTerm.gen term_src term_tgt inv *)
     []
  | _, _ -> [] (* implement if necessary *)

let gen_infrules_gvn
      (inv : Invariant.t)
      (inv_nxt : Invariant.t)
    : Infrule.t list =
  let (infrs1, inv_goal1) = AutoRemMD.run inv inv_nxt in
  infrs1
  (* let (infrs2, _) = AutoTransitivity.run AutoScope.Src inv inv_goal1 in *)
  (* infrs1@infrs2 *)

let gen_infrules
    : Invariant.t -> Invariant.t -> Infrule.t list =
  gen_infrules_gvn (* TODO: add option *)

module AutoGenTest = struct
    let empty_inv_unary : Invariant.unary =
      { Invariant.lessdef = ExprPairSet.empty;
        Invariant.alias =
          { Invariant.diffblock = ValueTPairSet.empty;
            Invariant.noalias = PtrPairSet.empty };
        Invariant.unique = AtomSetImpl.empty;
        Invariant.coq_private = IdTSet.empty }

    let empty_inv : Invariant.t =
      { Invariant.src = empty_inv_unary;
        Invariant.tgt = empty_inv_unary;
        Invariant.maydiff = IdTSet.empty }

    let value_of_str (s:string) : ValueT.t =
      ValueT.Coq_id (Tag.Coq_physical, s)

    let vA = value_of_str "A"
    let vB = value_of_str "B"
    let vC = value_of_str "C"
    let va = value_of_str "a"
    let vb = value_of_str "b"
    let vc = value_of_str "c"
    let vd = value_of_str "d"
    let ve = value_of_str "e"
    let vf = value_of_str "f"
    let vone = value_of_str "one"
    (* Coq_const_int of sz * coq_Int *)
    let vz = value_of_str "z"

    let eA = Expr.Coq_value vA
    let eB = Expr.Coq_value vB
    let eC = Expr.Coq_value vC
    let ea = Expr.Coq_value va
    let eb = Expr.Coq_value vb
    let ec = Expr.Coq_value vc
    let ed = Expr.Coq_value vd
    let ee = Expr.Coq_value ve
    let ef = Expr.Coq_value vf
    let eone = Expr.Coq_value vone
    let ez = Expr.Coq_value vz

    let gen_pair1 e v1 v2 : ExprPair.t =
      (e, Expr.Coq_bop (LLVMsyntax.Coq_bop_add, 1, v1, v2))
    let gen_pair2 e v1 v2 : ExprPair.t =
      (Expr.Coq_bop (LLVMsyntax.Coq_bop_add, 1, v1, v2), e)

    let expr_pair_set_add_list (epl:ExprPair.t list)
        : ExprPairSet.t -> ExprPairSet.t =
      fun eps ->
      List.fold_left
        (fun s ep -> ExprPairSet.add ep s)
        eps epl

    let inv_precond : Invariant.t =
      Invariant.update_src
        (Invariant.update_lessdef
           (expr_pair_set_add_list
              [gen_pair1 ef vd vA;
               gen_pair1 ed vb vB;
               gen_pair1 eb vone vC;
               gen_pair1 ee vc vA;
               gen_pair1 ec va vB;
               gen_pair1 ea vone vC;
               gen_pair2 ef vd vA;
               gen_pair2 ed vb vB;
               gen_pair2 eb vone vC;
               gen_pair2 ee vc vA;
               gen_pair2 ec va vB;
               gen_pair2 ea vone vC
        ]))
        empty_inv

    let inv_postcond_src : Invariant.t =
      Invariant.update_src
        (Invariant.update_lessdef
           (expr_pair_set_add_list
              [gen_pair1 ez vf vone;
               gen_pair2 ez vf vone]))
        inv_precond

    let inv_postcond_tgt : Invariant.t =
      Invariant.update_tgt
        (Invariant.update_lessdef
           (expr_pair_set_add_list
              [gen_pair1 ez ve vone;
               gen_pair2 ez ve vone]))
        inv_postcond_src

    let inv_postcond : Invariant.t =
      Invariant.update_maydiff
        (fun s -> IdTSet.add (Tag.Coq_physical, "z") s)
        inv_postcond_tgt

    (* Test 1*)
    let gen_infrs = gen_infrules inv_postcond empty_inv

    let gen_infrs_str =
      List.map
         Printer.PrintHints.infrule_to_string gen_infrs

    let _ = print_endline "DSFSDF"

    let _ =
      let size = List.length gen_infrs_str in
      print_endline ("START "^(string_of_int size));
      List.fold_left
        (fun _ s -> (print_endline "MID"); print_endline s)
        () gen_infrs_str
  (* TODO: run remove-md on inv_postcond*)
  end
