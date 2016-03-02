open Infrastructure
open Printf
open Llvm
open Arg
open Syntax
open MetatheoryAtom
open Dom_list
open Dom_tree
open Maps
open CoreHint_t
open PropagateHints
open ConvertInfrule
open Hints
open Exprs
open AddInfrule

type atom = AtomSetImpl.elt

let generate_nop (core_hint:CoreHint_t.hints) : int list = [] (* TODO *)

let insert_nop (m:LLVMsyntax.coq_module) (nops:int list) : LLVMsyntax.coq_module
  = m (* should be defined in Coq *)

(** generating empty hint structure **)

module EmptyHint = struct
  (* TODO: define in Coq *)
  let unary_hint : Invariant.unary =
    { lessdef = ExprPairSet.empty;
      noalias = ValueTPairSet.empty;
      allocas = IdTSet.empty;
      coq_private = IdTSet.empty;
    }

  let invariant_hint : Invariant.t =
    { src = unary_hint;
      tgt = unary_hint;
      maydiff = IdTSet.empty;
    }

  (* TODO: check create_empty_hint_* again *)
  let stmts_hint (stmts: LLVMsyntax.stmts) : ValidationHint.stmts =
    match stmts with
    | Coq_stmts_intro (phinodes, cmds, _) ->
       let empty_hint_phinodes =
         List.fold_left
           (fun phi_hint phi ->
             match phi with
             | LLVMsyntax.Coq_insn_phi (_,_,vll) ->
                let empty_inf_l = List.map (fun (v,l) -> (l,[])) vll in
                Alist.updateAddALs phi_hint empty_inf_l
           )
           [] phinodes
       in
       let empty_hint_cmds =
         List.map (fun _ -> ([], invariant_hint)) cmds
       in
       { phinodes = empty_hint_phinodes;
         invariant_after_phinodes = invariant_hint;
         cmds = empty_hint_cmds;
       }

  let fdef_hint (fdef:LLVMsyntax.fdef) : atom * ValidationHint.fdef =
    match fdef with
    | Coq_fdef_intro (Coq_fheader_intro (_,_,id,_,_), blks) ->
       (id, List.map (fun (bid, bstmts) ->
                       (bid, stmts_hint bstmts))
                     blks)

  let module_hint (m:LLVMsyntax.coq_module) : ValidationHint.coq_module =
    match m with
    | Coq_module_intro (lo, nts, prods) ->
       List.fold_left
         (fun empty_hint_prods prod ->
           match prod with
           | LLVMsyntax.Coq_product_fdef fd ->
              (fdef_hint fd)::empty_hint_prods
           | _ -> empty_hint_prods)
         [] prods
end

(* TOOD: don't know yet *)
let noret (vhint_module:ValidationHint.coq_module) : ValidationHint.coq_module = vhint_module

(** execute corehint commands **)

let execute_corehint_cmd
      (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (cmd:CoreHint_t.command) (dom_tree:LLVMsyntax.l coq_DTree)
      (vhint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  match cmd with
  | CoreHint_t.Propagate prop ->
     propagate_hint prop.propagate prop.propagate_range
                         lfdef rfdef dom_tree vhint_fdef
  | CoreHint_t.Infrule infr ->
      let coq_infrule = convert_infrule infr in
      add_infrule coq_infrule lfdef rfdef vhint_fdef

let translate_corehint_to_hint
      (lm:LLVMsyntax.coq_module) (rm:LLVMsyntax.coq_module) (* assume nop-insertion is done *)
      (core_hint:CoreHint_t.hints)
    : LLVMsyntax.coq_module * LLVMsyntax.coq_module * ValidationHint.coq_module =
  (* TODO: insert nops *)
  
  let fid = core_hint.function_id in

  let (vhint_module:ValidationHint.coq_module) = EmptyHint.module_hint lm in
  let vhint_module = noret vhint_module in (* TODO: noret? *)

  let (vhint_fdef, lfdef, rfdef) =
    match Alist.lookupAL vhint_module fid,
          LLVMinfra.lookupFdefViaIDFromModule lm fid,
          LLVMinfra.lookupFdefViaIDFromModule rm fid
    with
    | Some vhint_fdef, Some lfdef, Some rfdef -> (vhint_fdef, lfdef, rfdef)
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

  let vhint_fdef = List.fold_left
    (fun vhint_fdef core_cmd ->
      execute_corehint_cmd lfdef rfdef core_cmd dom_tree vhint_fdef)
    vhint_fdef core_hint.commands
  in
  let vhint_module = Alist.updateAL vhint_module fid vhint_fdef in
  (lm, rm, vhint_module)
