open Hints
open Exprs
open Syntax

open LLVMsyntax

(* flags for turning on/off certain automations *)
(* let flag_tran : bool ref = ref true *)
(* let flag_comm : bool ref = ref false *)

module AutoScope = struct
  type t = Src | Tgt

  let transitivity (scp:t): Expr.t * Expr.t * Expr.t -> Infrule.t =
    (* let transitivity (scp:t) e1 e2 e3: Infrule.t = *)
    match scp with
    | Src -> Infrule.Coq_transitivity
    | Tgt -> Infrule.Coq_transitivity_tgt

  let substitute (scp:t): IdT.t * ValueT.t * Expr.t -> Infrule.t =
    match scp with
    | Src -> Infrule.Coq_substitute
    | Tgt -> Infrule.Coq_substitute_tgt

  let inv_unary (scp:t) : Invariant.t -> Invariant.t =
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
  (* TODO:
let eq_exp_pair_args e1 e2 =
if Expr.same_modulo_value e1 e2
then Some (List.combine (Expr.get_valueTs e1) (Expr.get_valueTs e2))
else None
   *)
  let eq_exp_pair_args (e1:Expr.t) (e2:Expr.t)
      : ((ValueT.t * ValueT.t) list) option =
    match e_l, e_r with
    | Expr.Coq_bop (bop1, sz1, va1, vb1), Expr.Coq_bop (bop2, sz2, va2, vb2)
         when bop1 = bop2 && sz1 = sz2 ->
       Some [(va1, va2); (vb1, vb2)]
    | Expr.Coq_fbop (bop1, fp1, va1, vb1), Expr.Coq_fbop (bop2, fp2, va2, vb2)
         when bop1 = bop2 && fp1 = fp2 ->
       Some [(va1, va2); (vb1, vb2)]
    | Expr.Coq_extractvalue (tya1, v1, cl1, tyb1), Expr.Coq_extractvalue (tya2, v2, cl2, tyb2)
         when tya1 = tya2 && cl1 = cl2 && tyb1 = tyb2 ->
       Some [(v1, v2)]
    | Expr.Coq_insertvalue (tya1, va1, tyb1, vb1, cl1), Expr.Coq_insertvalue (tya2, va2, tyb2, vb2, cl2)
         when tya1 = tya2 && tyb1 = tyb2 && cl1 = cl2 ->
       Some [(va1, va2); (vb1, vb2)]
    | Expr.Coq_gep (inb1, tya1, v1, svl1, tyb1), Expr.Coq_gep (inb2, tya2, v2, svl2, tyb2)
         when inb1 = inb2 && tya1 = tya2 && tyb1 = tyb2 ->
       (match svls2vpl with
        | Some vpl -> (v1, v2)::vpl
        | None -> None)
    | Expr.Coq_trunc (op1, tya1, v1, tyb1), Expr.Coq_trunc (op2, tya2, v2, tyb2)
         when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 ->
       Some [(v1, v2)]
    | Expr.Coq_ext (op1, tya1, v1, tyb1), Expr.Coq_ext (op2, tya2, v2, tyb2)
         when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 ->
       Some [(v1, v2)]
    | Expr.Coq_cast (op1, tya1, v1, tyb1), Expr.Coq_cast (op2, tya2, v2, tyb2)
         when op1 = op2 && tya1 = tya2 && tyb1 = tyb2 ->
       Some [(v1, v2)]
    | Expr.Coq_icmp (c1, ty1, va1, vb1), Expr.Coq_icmp (c2, ty2, va2, vb2)
         when c1 = c2 && ty1 = ty2 ->
       Some [(va1, va2); (vb1, vb2)]
    | Expr.Coq_fcmp (c1, fp1, va1, vb1), Expr.Coq_fcmp (c2, fp2, va2, vb2)
         when c1 = c2 && fp1 = fp2 ->
       Some [(va1, va2); (vb1, vb2)]
    | Expr.Coq_select (va1, ty1, vb1, vc1), Expr.Coq_select (va2, ty2, vb2, vc2)
         when ty1 = ty2 ->
       Some [(va1, va2); (vb1, vb2); (vc1, vc2)]
    | Expr.Coq_value v1, Expr.Coq_value v2 ->
       Some [(v1, v2)]
    | Expr.Coq_load (v1, ty1, a1), Expr.Coq_load (v2, ty2, a2)
         when ty1 = ty2 -> (* should we compare align? *)
       Some [(v1, v2)]
    | _, _ -> None

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

end

module AutoTransitivity = struct
  (* e_src <> e_dest *)
  (* e_src and e_dest are not in trace *)
  let rec find_chain (e_l:Expr.t) (e_r:Expr.t)
                     (trace:Expr.t list) (lessdef:ExprPairSet.t)
          : (Expr.t list) option =
    if ExprPairSet.mem (e_l, e_r) lessdef
    then Some (e_l::e_r::trace)
    else
      let cands = get_lhs_list lessdef e_r in
      let cands_filtered : Expr.t list =
        List.filter (fun e -> List.mem e trace) cands in
      let rec search_cands cands =
        match cands with
        | [] -> None
        | c::cands_t ->
           (match find_chain e_l c (e_r::trace) inv_unary with
            | Some chain -> chain
            | None -> search_cands cands_t)
      in search_cands cands_filtered

  let rec gen_infrules (scp:AutoScope.t) (chain:Expr.t list)
          : Infrule.t list =
    match chain with
    | e1::e2::e3::chain_t ->
       (AutoScope.transitivity scp (e1, e2, e3))::
         (gen_infrules scp (e1::e3::chain_t))
    | _ -> []

  (* ep from ld_goal *)
  let run_each (ld:ExprPairSet.t) (ep:Expr.t * Expr.t)
               (ld_goal:ExprPairSet.t)
      : Infrule.t list * ExprPairSet.t =
    if ExprPairSet.mem ep ld
    then ([], ExprPairSet.remove ep ld_goal)
    else
      match find_chain (fst ep) (snd ep) [] ld with
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
          let (infrs_r, ld_r) = run_each ld ep ld_m in
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
      let exp_x = (Expr.value (ValueT.Coq_id x)) in
      let exp_v = (Expr.value v) in

      let e_l_cands = AutoUtils.get_rhs_list inv.Invariant.lessdef exp_x in
      let e_r_cands = AutoUtils.get_lhs_list inv.Invariant.lessdef exp_v in
      match try_expr2 (try_subst scp inv_u) e_l_cands e_r_cands with
      | Some infrs ->
         Some (infrs@[AutoScope.transitivity scp (exp_x, e_l, e_r);
                      AutoScope.transitivity scp (exp_x, e_r, exp_v)])
      | None -> None

  (* generate e_l >= e_r if possible *)
  and try_subst (scp:AutoScope.t) (inv_u:Invariant.unary)
                (e_l:Expr.t) (e_r:Expr.t)
      : (Infrule.t list) option =
    match eq_exp_pair_args e_l e_r with
    | Some vpl ->
       try_subst_intl scp inv_u e_l e_l vpl
    | _ -> None

  (* (x) generate e_l >= e_r *)
  (* generate e_l >= e_l[rep vpl] *)
  and try_subst_intl (scp:AutoScope.t) (inv_u : Invariant.unary)
                (e_l:Expr.t) (e_m:Expr,t) (* (e_r:Expr.t) *)
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
                   infrs_acc@infrs_v@[AutoScope.substitute scp (x, vr, e_m)]@
                     if e_l = e_m then []
                     else [AutoScope.transitivity scp (e_l, e_m, e_m_new)]
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
    let e_src_cands = get_rhs_list inv.Invariant.src.Invariant.lessdef exp_x in
    let e_tgt_cands = get_lhs_list inv.Invariant.tgt.Invariant.lessdef exp_x in
    try_expr2 (try_subst AutoScope.Src inv.Invariant.src) e_src_cands e_tgt_cands

  let rec run_intl (inv:Invariant.t) (inv_goal:Invariant.t)
               (infrs_acc:Infrules.t list) (md:IdT.t list)
      : Infrule.t list * Invariant.t =
    match md with
    | [] -> (infrs_acc, inv_goal)
    | x::md_t ->
       (match find_inject inv x with
        | Some infrs ->
           let inv_goal_new = rem x inv_goal in
           run_intl inv inv_goal_new (infrs_acc@infrs) md_t
        | None -> run_intl inv inv_goal infrs_acc md_t)

  let run (inv:Invariant.t) (inv_goal:Invariant.t)
      : Infrule.t list * Invariant.t =
    let md : IdT.t list =
      IdTSet.elements inv_goal.Invariant.maydiff in
    run_intl inv inv_goal md
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

let gen_infrules
      (inv : Invariant.t)
      (inv_nxt : Invariant.t)
    : Infrule.t list =
  let (infrs1, inv_goal1) = AutoRemMD.run inv inv_nxt in
  let (infrs2, _) = AutoTransitivity.run inv inv_goal1 in
  infrs1@infrs2
