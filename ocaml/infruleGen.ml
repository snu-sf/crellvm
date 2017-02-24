open Hints
open Exprs
open Syntax
open MetatheoryAtom
open LLVMsyntax

(* TODO: add option *)

module AutoUtils = struct
    type pass_t =
      GVN | SROA | INSTCOMBINE
      | TEST1 | TEST2 | TEST3 | TEST4

    let pass_option : pass_t ref = ref GVN

    type scope_t = Src | Tgt

    let transitivity (scp:scope_t) e1 e2 e3 : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_transitivity (e1, e2, e3)
      | Tgt -> Infrule.Coq_transitivity_tgt (e1, e2, e3)

    let substitute (scp:scope_t) x v e : Infrule.t =
      match scp with
      | Src -> Infrule.Coq_substitute (x, v, e)
      | Tgt -> Infrule.Coq_substitute_tgt (x, v, e)

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
    (* e_src <> e_dest *)
    (* let rec print_trace (tr:Expr.t list) : unit = *)
    (*   match tr with *)
    (*   | h::t -> print_endline (Printer.ExprsToString.of_expr h); *)
    (*             print_trace t *)
    (*   | [] -> () *)

    (* e_src and e_dest are not in the trace *)
    let rec find_chain (trace:Expr.t list) (lessdef:ExprPairSet.t)
                       (e_l:Expr.t) (e_r:Expr.t)
            : (Expr.t list) option =
      if ExprPairSet.mem (e_l, e_r) lessdef
      then Some (e_l::e_r::trace)
      else
        let cands = AutoUtils.get_lhs_list lessdef e_r in
        let cands_filtered : Expr.t list =
          List.filter (fun e -> not (List.mem e trace)) cands in
        AutoUtils.expr_find_first_match2 (find_chain (e_r::trace) lessdef) [e_l] cands_filtered

    let rec gen_infrules (scp:AutoUtils.scope_t) (chain:Expr.t list)
            : Infrule.t list =
      match chain with
      | e1::e2::e3::chain_t ->
         (AutoUtils.transitivity scp e1 e2 e3)::
           (gen_infrules scp (e1::e3::chain_t))
      | _ -> []

    let run_unary (scp:AutoUtils.scope_t) (inv_u:Invariant.unary)
                  (e1:Expr.t) (e2:Expr.t)
        : (Infrule.t list) option =
      match find_chain [] inv_u.Invariant.lessdef e1 e2 with
      | Some el ->
         print_endline "found some";
         Some (gen_infrules scp el)
      | None -> print_endline "found none"; None
  end

module AutoSubstTransHelper = struct
    (* produce x >= v applying seq of subst-transitivity *)
    let rec try_trans (scp:AutoUtils.scope_t) (inv_u : Invariant.unary)
                (x : IdT.t) (v : ValueT.t)
            : (Infrule.t list) option =
      if ValueT.eq_dec (ValueT.Coq_id x) v
      then Some [] else
        let exp_x = (Expr.Coq_value (ValueT.Coq_id x)) in
        let exp_v = (Expr.Coq_value v) in

        let e_l_cands = AutoUtils.get_rhs_list inv_u.Invariant.lessdef exp_x in
        let e_r_cands = AutoUtils.get_lhs_list inv_u.Invariant.lessdef exp_v in
        AutoUtils.expr_find_first_match2
          (fun e_l e_r ->
           if Expr.eq_dec e_l e_r
           then Some [AutoUtils.transitivity scp exp_x e_l exp_v]
           else
             match try_subst scp inv_u e_l e_r with
             | Some infrs ->
                Some (infrs@[AutoUtils.transitivity scp exp_x e_l e_r;
                             AutoUtils.transitivity scp exp_x e_r exp_v])
             | None -> None)
          e_l_cands e_r_cands

    (* generate e_l >= e_r if possible *)
    (* when e_l = e_r, return (Some []) *)
    and try_subst (scp:AutoUtils.scope_t) (inv_u:Invariant.unary)
                  (e_l:Expr.t) (e_r:Expr.t)
        : (Infrule.t list) option =
      match e_l, e_r with
      | Expr.Coq_value _, _
      | _, Expr.Coq_value _ -> None
      | _, _->
         (match AutoUtils.eq_exps_values e_l e_r with
          | Some vpl ->
             try_subst_intl scp inv_u e_l e_l vpl []
          | _ -> None)

    (* generate e_l >= e_l[rep vpl] *)
    (* when e_l = e_l[rep vpl], return (Some []) *)
    and try_subst_intl (scp:AutoUtils.scope_t) (inv_u : Invariant.unary)
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
                   let e_m_new = AutoUtils.substitute_expr x vr e_m in
                   let infrs_new =
                     infrs_acc@infrs_v@[AutoUtils.substitute scp x vr e_m]@
                       if Expr.eq_dec e_l e_m then []
                       else [AutoUtils.transitivity scp e_l e_m e_m_new]
                   in
                   try_subst_intl scp inv_u e_l e_m_new (* e_r *) vpl_t infrs_new
                | None -> None)
            | _ -> None)

  end

module type InjectExprGenerator = sig
    val f : Invariant.t -> Expr.t -> Expr.t -> (Infrule.t list) option
  end

(** 1-1. Resolving Next-Precond: Removing Maydiff *)
module AutoRemMD (IEG:InjectExprGenerator)
  = struct
    let find_inject (inv:Invariant.t) (x:IdT.t)
        : (Infrule.t list) option =
      let exp_x = Expr.Coq_value (ValueT.Coq_id x) in
      let e_src_cands =
        AutoUtils.get_rhs_list inv.Invariant.src.Invariant.lessdef exp_x in
      let e_tgt_cands =
        AutoUtils.get_lhs_list inv.Invariant.tgt.Invariant.lessdef exp_x in
      AutoUtils.expr_find_first_match2
        (fun e1 e2 ->
         match IEG.f inv e1 e2 with
           | Some infrs ->
              Some (infrs@[AutoUtils.transitivity AutoUtils.Src exp_x e1 e2])
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
        List.filter (fun x -> not (List.mem x md_goal)) md in
      run_intl inv inv_goal [] md_remain
  end

module type UnaryLDGenerator = sig
    val f : AutoUtils.scope_t -> Invariant.unary ->
            Expr.t -> Expr.t -> (Infrule.t list) option
  end

(** 1-2. Resolving Next-Precond: Unary Conditions *)
module AutoUnary (ULDG:UnaryLDGenerator) = struct
    let rec run_intl (scp:AutoUtils.scope_t)
                     (inv_u:Invariant.unary) (inv_u_goal:Invariant.unary)
                     (infrs_acc:Infrule.t list) (ld:(Expr.t * Expr.t) list)
            : Infrule.t list * Invariant.unary =
      match ld with
      | [] -> (infrs_acc, inv_u_goal)
      | (e_l, e_r)::ld_t ->
         (match ULDG.f scp inv_u e_l e_r with
          | Some infrs ->
             let inv_u_goal_new =
               Invariant.update_lessdef
                 (ExprPairSet.remove (e_l, e_r)) inv_u_goal
             in
             run_intl scp inv_u inv_u_goal_new (infrs_acc@infrs) ld_t
          | None -> run_intl scp inv_u inv_u_goal infrs_acc ld_t)

    let run_unary (scp:AutoUtils.scope_t)
                  (inv_u:Invariant.unary) (inv_u_goal:Invariant.unary)
        : Infrule.t list * Invariant.unary =
      let ld : ExprPair.t list =
        ExprPairSet.elements inv_u.Invariant.lessdef in
      let ld_goal : ExprPair.t list =
        ExprPairSet.elements inv_u_goal.Invariant.lessdef in
      let ld_remain : ExprPair.t list =
        List.filter (fun x -> not (List.mem x ld)) ld_goal in
      run_intl scp inv_u inv_u_goal [] ld_remain

    let run (inv:Invariant.t) (inv_goal:Invariant.t)
        : Infrule.t list * Invariant.t =
      let (infrs, inv_src) =
        run_unary AutoUtils.Src inv.Invariant.src inv_goal.Invariant.src
      in
      (infrs, Invariant.update_src (fun _ -> inv_src) inv_goal)
  end

(** Instances of Resolving Next-Precond *)
module AutoRemMD_SubstTransSrc =
  AutoRemMD
    (struct
        let f = fun inv ->
          AutoSubstTransHelper.try_subst
            AutoUtils.Src inv.Invariant.src
    end)

module AutoUnary_SubstTransSrc =
  AutoUnary
    (struct
        let f = fun scp inv_u e1 e2 ->
          match e1, e2 with
          | Expr.Coq_value (ValueT.Coq_id x), Expr.Coq_value v ->
             AutoSubstTransHelper.try_trans scp inv_u x v
          | _, _ -> None
      end)

module AutoUnary_TransSrc =
  AutoUnary
    (struct
        let f = AutoTransHelper.run_unary
      end)

let default1 : Invariant.t -> Invariant.t -> (Infrule.t list * Invariant.t) =
  fun _ r -> ([], r)

(** 2. AutoInjectEvent *)

module AutoInjectEvent (IEG:InjectExprGenerator) = struct
    let rec run_intl (inv:Invariant.t) (vpl_acc:ValueTPair.t list)
                     (infrs_acc:Infrule.t list) (vpl:ValueTPair.t list)
            : Infrule.t list * (ValueTPair.t list) =
      match vpl with
      | [] -> (infrs_acc, vpl_acc)
      | (v_l, v_r)::vpl_t ->
         (match IEG.f inv (Expr.Coq_value v_l) (Expr.Coq_value v_r) with
          | Some infrs ->
             run_intl inv vpl_acc (infrs_acc@infrs) vpl_t
          | None ->
             run_intl inv ((v_l, v_r)::vpl_acc) infrs_acc vpl_t)

    let run (inv : Invariant.t) (vpl:(ValueT.t * ValueT.t) list)
        : Infrule.t list * (ValueT.t * ValueT.t) list =
      run_intl inv [] [] vpl
  end

(** Instances of AutoInjectEvent *)
module AutoInjectEvent_SubstTransSrc =
  AutoInjectEvent
    (struct
        let f = fun inv e1 e2 ->
          match e1, e2 with
          | Expr.Coq_value (ValueT.Coq_id x),
            Expr.Coq_value v ->
             if Invariant.not_in_maydiff inv v
             then
               AutoSubstTransHelper.try_trans
                 AutoUtils.Src inv.Invariant.src x v
             else None
          | _, _ -> None
      end)

let default2: Invariant.t -> ValueTPair.t list ->
              (Infrule.t list * ValueTPair.t list) =
  fun _ vp -> ([], vp)

(** candidates *)
module AutoGVN = struct
    let run1 = AutoUnary_SubstTransSrc.run
    let run2 = default2
  end

module AutoTest1 = struct
    let run1 = AutoRemMD_SubstTransSrc.run
    let run2 = default2
  end

module AutoTest2 = struct
    let run1 = AutoUnary_SubstTransSrc.run
    let run2 = default2
  end

module AutoTest3 = struct
    let run1 = AutoUnary_TransSrc.run
    let run2 = default2
  end

module AutoTest4 = struct
    let run1 = default1
    let run2 = AutoInjectEvent_SubstTransSrc.run
  end

(** interface *)
let gen_infrules_from_insns
      (insn_src : LLVMsyntax.insn)
      (insn_tgt : LLVMsyntax.insn)
      (inv : Invariant.t)
    : Infrule.t list =
  let run
      : Invariant.t -> ValueTPair.t list ->
        (Infrule.t list) * (ValueTPair.t list) =
    match !AutoUtils.pass_option with
    | AutoUtils.GVN -> AutoGVN.run2
    | AutoUtils.TEST1 -> AutoTest1.run2
    | AutoUtils.TEST2 -> AutoTest2.run2
    | AutoUtils.TEST3 -> AutoTest3.run2
    | AutoUtils.TEST4 -> AutoTest4.run2
    | _ -> default2
  in
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
  match get_value_pairs_from_insns insn_src insn_tgt with
  | Some vpl ->
     let (infrs, _) = run inv vpl in
     infrs
  | None -> []

let gen_infrules (inv:Invariant.t) (inv_nxt:Invariant.t)
    : Infrule.t list =
  let run
      : Invariant.t -> Invariant.t ->
        (Infrule.t list * Invariant.t) =
    match !AutoUtils.pass_option with
    | AutoUtils.GVN -> AutoGVN.run1
    | AutoUtils.TEST1 -> AutoTest1.run1
    | AutoUtils.TEST2 -> AutoTest2.run1
    | AutoUtils.TEST3 -> AutoTest3.run1
    | AutoUtils.TEST4 -> AutoTest4.run1
    | _ -> default1
  in
  let (infrs1, _) = run inv inv_nxt in
  infrs1

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

    let inv_ld_f_e : Invariant.t =
      Invariant.update_src
        (Invariant.update_lessdef
           (expr_pair_set_add_list
              [(ef, ee)]))
        empty_inv

    let inv_for_trans : Invariant.t =
      Invariant.update_src
        (Invariant.update_lessdef
           (expr_pair_set_add_list
              [(ef, ea);
               (ea, eb);
               (eb, ea);
               (ea, ef);
               (eb, ec);
               (ec, ea);
               (ec, ed);
               (ed, ee);
               (ee, eb);
               (ed, ec)
              ]
        ))
        empty_inv

    let print_string_list sl : unit =
      let size = List.length sl in
      print_endline ("length: "^(string_of_int size));
      List.fold_left
        (fun _ s -> (print_endline "MID"); print_endline s)
        () sl

    let string_of_terminator i : string =
      match i with
      | LLVMsyntax.Coq_insn_br (id, v, l1, l2) ->
         Printf.sprintf "  %s = br %s %s %s\n" id (Coq_pretty_printer.string_of_value v) l1 l2
      | LLVMsyntax.Coq_insn_br_uncond (id, l) ->
         Printf.sprintf "  %s = br %s \n" id l
      | LLVMsyntax.Coq_insn_switch (id, ty, v, dflt, cases) ->
         Printf.sprintf "  %s = switch %s %s, %s %s\n" id (Coq_pretty_printer.string_of_typ ty) (Coq_pretty_printer.string_of_value v) dflt
                 (List.fold_left (fun s (c, l) -> s ^ "[" ^ (Coq_pretty_printer.string_of_constant c) ^ ", " ^ l ^ "] ") "" cases)
      | LLVMsyntax.Coq_insn_return (id, t, v) ->
         Printf.sprintf "  %s = ret %s %s\n" id (Coq_pretty_printer.string_of_typ t) (Coq_pretty_printer.string_of_value v)
      | LLVMsyntax.Coq_insn_return_void id ->
         Printf.sprintf "  %s = ret void\n" id
      | LLVMsyntax.Coq_insn_unreachable id ->
         Printf.sprintf "  %s = unreachable\n" id

    let dv = !Globalstates.debug
    let _ = Globalstates.debug := true
    let ch = !Printer.out_channel
    let _ = Printer.out_channel := stdout
    let po = !AutoUtils.pass_option

    (* Test 1 *)
    let _ = AutoUtils.pass_option := AutoUtils.TEST1
    let _ = print_endline "Test 1: AutoRemMD_SubstTransSrc"
    let _ = print_endline "- inv:"
    let _ = Printer.PrintHints.invariant inv_postcond
    let _ = print_endline "- inv_goal:"
    let _ = Printer.PrintHints.invariant empty_inv

    let gen_infrs1 =
      gen_infrules inv_postcond empty_inv

    let gen_infrs_str1 =
      List.map Printer.PrintHints.infrule_to_string gen_infrs1

    let _ = print_endline "- generated infrules:"

    let _ = print_string_list gen_infrs_str1

    (* Test 2 *)
    let _ = AutoUtils.pass_option := AutoUtils.TEST2
    let _ = print_endline "Test 2: AutoUnary_SubstTransSrc"
    let _ = print_endline "- inv:"
    let _ = Printer.PrintHints.invariant inv_precond
    let _ = print_endline "- inv_goal:"
    let _ = Printer.PrintHints.invariant inv_ld_f_e

    let gen_infrs2 =
      gen_infrules inv_postcond_tgt inv_ld_f_e

    let gen_infrs_str2 =
      List.map
         Printer.PrintHints.infrule_to_string gen_infrs2

    let _ = print_endline "- generated infrules:"

    let _ = print_string_list gen_infrs_str2

    (* Test 3 *)
    let _ = AutoUtils.pass_option := AutoUtils.TEST3
    let _ = print_endline "Test 3: AutoUnary_TransSrc"
    let _ = print_endline "- inv:"
    let _ = Printer.PrintHints.invariant inv_for_trans
    let _ = print_endline "- inv_goal:"
    let _ = Printer.PrintHints.invariant inv_ld_f_e

    let gen_infrs3 =
      gen_infrules inv_for_trans inv_ld_f_e

    let gen_infrs_str3 =
      List.map
         Printer.PrintHints.infrule_to_string gen_infrs3

    let _ = print_endline "- generated infrules:"

    let _ = print_string_list gen_infrs_str3

    (* Test 4 *)
    let _ = AutoUtils.pass_option := AutoUtils.TEST4
    let _ = print_endline "Test 4: AutoInjectEvent_SubstTransSrc"
    let _ = print_endline "- inv:"
    let _ = Printer.PrintHints.invariant inv_precond
    let _ = print_endline "- insns:"

    let tmn1 : terminator =
      Coq_insn_return ("id1", Coq_typ_int 1, Coq_value_id "f")
    let ret_insn1 : insn = Coq_insn_terminator tmn1

    let tmn2 : terminator =
      Coq_insn_return ("id3", Coq_typ_int 1, Coq_value_id "e")
    let ret_insn2 : insn = Coq_insn_terminator tmn2

    let _ = print_endline (string_of_terminator tmn1)
    let _ = print_endline (string_of_terminator tmn2)

    let gen_infrs4 =
      gen_infrules_from_insns ret_insn1 ret_insn2 inv_precond

    let gen_infrs_str4 =
      List.map
         Printer.PrintHints.infrule_to_string gen_infrs4

    let _ = print_endline "- generated infrules:"

    let _ = print_string_list gen_infrs_str4


    (* Test end *)
    let _ = AutoUtils.pass_option := po
    let _ = Globalstates.debug := dv
    let _ = Printer.out_channel := ch

  end
