open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open MetatheoryAtom
open MicroHints
open CommandArg
open Dom_list
open Dom_tree
open Maps
open CoreHint_t
open PropagateHints

open Hints
open Exprs

type atom = AtomSetImpl.t

let generate_nop (core_hint:CoreHint_t.hints) : int list = [] (* TODO *)

let insert_nop (m:LLVMsyntax.coq_module) (nops:int list) : LLVMsyntax.coq_module
  = m (* should be defined in Coq *)

(** generating empty hint structure **)

let empty_unary : Invariant.unary =
  { lessdef = ExprPairSet.empty;
    noalias = ValueTPairSet.empty;
    allocas = IdTSet.empty;
    coq_private = IdTSet.empty;
  }

let empty_invariant : Invariant.t =
  { src = empty_unary;
    tgt = empty_unary;
    maydiff = IdTSet.empty;
  }

(* TODO: check create_empty_hints_* again *)
let create_empty_hints_stmts (stmts: LLVMsyntax.stmts) : ValidationHint.stmts =
  match stmts with
  | Coq_stmts_intro (phinodes, cmds, _) ->
     let empty_hints_phinodes =
       List.fold_left
         (fun phi_hints phi ->
           match phi with
           | LLVMsyntax.Coq_insn_phi (_,_,vll) ->
              let empty_inf_l = List.map (fun (v,l) -> (l,[])) vll in
              Alist.updateAddALs phi_hints empty_inf_l
         )
         [] phinodes
     in
     let empty_hints_cmds =
       List.map (fun _ -> ([], empty_invariant)) cmd
     in
     Hints.mk_stmts (empty_hints_phinodes,
                     empty_invariant,
                     empty_hints_cmds)

let create_empty_hints_fdef (fdef:LLVMsyntax.fdef) : atom * ValidationHint.fdef =
  match fdef with
  | Coq_fdef_intro (Coq_fheader_intro (_,_,id,_,_), blks) ->
     (id, List.map (fun (bid, bstmts) ->
                     (bid, create_empty_hints_stmts bstmts))
                   blks)

let create_empty_hints_module (m:LLVMsyntax.coq_module) : ValidationHint.coq_module =
  match m with
  | Coq_module_intro (lo, nts, prods) ->
     List.fold_left
       (fun empty_hints_prods prod ->
         match prod with
         | Coq_product_fdef fd ->
            (create_empty_hints_fdef fd)::empty_hints_prods
         | _ -> empty_hints_prods)
       [] prods

(* TOOD: don't know yet *)
let noret (hints_m:Hints.module) : Hints.module = hints_m

(** Convert propagate object to coq-defined objs **)

let convert_propagate_value_to_Expr
      (pv:CoreHint_t.propagate_value) (fdef:LLVMsyntax.fdef)
    : Expr.t =
  match pv with
  | CoreHint_t.Var (var:CoreHint_t.variable) ->
     Expr.value (ValueT.id (convert_variable_to_IdT var))
  | CoreHint_t.Rhs (var:CoreHint_t.variable) ->
     let instr = find_instr_from_fdef var.name fdef in
     let rhs_exp = get_rhs instr in
     rhs_exp

let convert_propagate_object 
      (c_prop_obj:CoreHint_t.propagate_object) (fdef:LLVMsyntax.fdef)
    : propagate_object =
  match c_prop_obj with
  | CoreHint_t.Instr ld | CoreHint_t.Eq ld ->
     Lessdef_obj (convert_propagate_value_to_Expr ld.lhs fdef,
                  convert_propagate_value_to_Expr ld.lhs fdef)
  | CoreHint_t.Neq na ->
     Noalias_obj (convert_value_to_ValueT na.lhs,
                  convert_value_to_ValueT na.rhs)
     
(** execute corehint commands **)

let execute_corehint_cmd
      (hint_f:Hints.fdef) (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (cmd:CoreHint_t.command) (dom_tree:LLVMsyntax.l coq_DTree)
    : Hints.fdef =
  match cmd with
  | CoreHint_t.PropagateGlobal (options:CoreHint_t.propagate_global) ->
     let idt =
       match options.propagate with
       | MaydiffGlobal var ->
          convert_variable_to_IdT var.variable
     in
     propagate_maydiff_in_hints_fdef idt hint_f
  | CoreHint_t.Propagate (options:CoreHint_t.propagate) ->
     let fdef =
       match options.scope with
       | CoreHint_t.Source -> lfdef
       | CoreHint_t.Target -> rfdef
     in
     let scope =
       match options.scope with
       | CoreHint_t.Source -> Left_scope
       | CoreHint_t.Target -> Right_scope
     in
     let prop_expr = convert_propagate_object options.propagate_object fdef in
     let pos_from = convert_position options.propagate_from fdef in
     let pos_to = convert_position options.propagate_to fdef in
     propagate pos_from pos_to prop_expr fdef dom_tree hint_f
     
     
  | _ -> hints_fdef
  (* TODO: like propagate_micro *)

let execute_corehint_cmds
      (hints_fdef:Hints.fdef) (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (cmds:CoreHint_t.command list) (dom_tree:LLVMsyntax.l coq_DTree)
    : Hints.fdef =
  List.fold_left
    (fun hint_f cmd ->
      execute_corehint_cmd hint_f lfdef rfdef cmd dom_tree)
    hints_fdef cmds

let translate_corehint_to_hint
      (lm:LLVMsyntax.coq_module) (rm:LLVMsyntax.coq_module) (* assume nop-insertion is done *)
      (core_hint:CoreHint_t.hints)
    : LLVMsyntax.coq_module * LLVMsyntax.coq_module * Hints.module =

  let fid = core_hint.function_id in

  let (vhint_module:ValidationHint.coq_module) = create_empty_hints_module lm in
  let vhint_module = noret hints_module in (* TODO: noret? *)

  let (hints_fdef, lfdef, rfdef) =
    match Alist.lookupAL hints_module fid,
          LLVMinfra.lookupFdefViaIDFromModule lm fid,
          LLVMinfra.lookupFdefViaIDFromModule rm fid
    with
    | Some hint_f, Some lfdef, Some rfdef -> (hint_f, lfdef, rfdef)
    | p1, p2, p3 ->
    Printf.printf "translate_corehint_to_hint : fid : %s %d %d %d\n%!" fid
      (match p1 with | None -> 0 | _ -> 1) (match p2 with | None -> 0 | _ -> 1) (match p3 with | None -> 0 | _ -> 1);
    failwith ("translate_corehint_to_hint : fid : " ^ fid)
  in

  let dom_tree =
    match AlgDom.create_dom_tree lfdef with
    | Some dom_tree -> dom_tree
    | None -> failwith "translateHints create_dom_tree"
  in

  let hints_fdef = execute_corehint_cmds lfdef rfdef hints_fdef core_hint.commands dom_tree in
  let hints_module = Alist.updateAL hints_module fid hints_fdef in
  (lm, rm, hints_module)

