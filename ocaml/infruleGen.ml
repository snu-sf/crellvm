open Hints
open Exprs
open Syntax

open LLVMsyntax

(* flags for turning on/off certain automations *)
let flag_tran : bool ref = ref true
let flag_comm : bool ref = ref false

module InfrGenUtil = struct
    (* TODO: arg invariant.unary for checking maydiff *)
    let rec gen_inject_src (e1 : Expr.t) (e2 : Expr.t) (inv : Invariant.unary)
            : (Infrule.t list) option =
      if e1 = e2 then Some []
      else if ExprPairSet.mem (e1, e2) inv.Invariant.lessdef
      then Some []
      else
        let ep_set = Invariant.get_rhs inv.Invariant.lessdef e1 in
        let rhs_list = List.map snd (ExprPairSet.elements ep_set) in
        let rec _gen_inject_intl (el:Expr.t list)
          : (Infrule.t list) option=
          match el with
          | [] -> None
          | em::elt ->
              (match gen_inject_src em e2 inv with
               | Some infrs ->
                  Some (infrs@[Infrule.Coq_transitivity (e1, em, e2)])
               | None -> _gen_inject_intl elt)
        in
        _gen_inject_intl rhs_list

          (*                List.fold_left *)
          (* (fun acc em -> *)
          (*  match acc with *)
          (*  | Some infrs -> acc *)
          (*  | None -> *)
          (*     (match gen_inject_src em e2 inv with *)
          (*      | Some infrs -> *)
          (*         infrs@[Infrule.Coq_transitivity (e1, em, e2)] *)
          (*      | None -> None)) *)
          (* None rhs_of_e1 *)

    let gen_inject (v1 : value) (v2 : value) (inv : Invariant.t)
        : Infrule.t list =
      match v1, v2 with
      | Coq_value_id x1, Coq_value_id x2 ->
         let v1 = ValueT.Coq_id (Tag.Coq_physical, x1) in
         let v2 = ValueT.Coq_id (Tag.Coq_physical, x2) in
         (match gen_inject_src (Expr.Coq_value v1)
                               (Expr.Coq_value v2)
                               inv.Invariant.src with
          | Some infrs -> infrs
          | None -> [])
      | _, _ -> []
  end

module InfrGenCmd = struct
    let params2values (ps:((typ*attributes)*value) list)
        : value list =
      List.map snd ps

    let gen (cmd_src : cmd) (cmd_tgt : cmd) (inv : Invariant.t)
        : Infrule.t list =
      match cmd_src, cmd_tgt with
      | Coq_insn_call (_, _, _, _, _, _, params1),
        Coq_insn_call (_, _, _, _, _, _, params2) ->
         let vl1 = params2values params1 in
         let vl2 = params2values params2 in
         if (List.length vl1 <> List.length vl2) then []
         else
           let vpl = List.combine vl1 vl2 in
           List.fold_left
             (fun infr_acc (v1, v2) ->
              infr_acc @ (InfrGenUtil.gen_inject v1 v2 inv))
             [] vpl
      | _, _ -> [] (* implement if necessary *)
  end

(* TODO: for ret, (cond) br, switch *)
module InfrGenTerm = struct
    let gen (term_src : terminator) (term_tgt : terminator) (inv : Invariant.t)
        : Infrule.t list =
      []
  end

let gen_infrules_from_insns
      (insn_src : LLVMsyntax.insn)
      (insn_tgt : LLVMsyntax.insn)
      (inv : Invariant.t)
    : Infrule.t list
  =
  match insn_src, insn_tgt with
  | Coq_insn_cmd cmd_src, Coq_insn_cmd cmd_tgt ->
     InfrGenCmd.gen cmd_src cmd_tgt inv
  | Coq_insn_terminator term_src, Coq_insn_terminator term_tgt ->
     InfrGenTerm.gen term_src term_tgt inv
  | _, _ -> []

let gen_infrules
      (inv : Invariant.t)
      (inv_nxt : Invariant.t)
    : Infrule.t list
  = []
