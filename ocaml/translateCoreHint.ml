open Infrastructure
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open MicroHints
open CommandArg
open Vars_aux
open Validator_aux
open Dom_list
open Dom_tree
open Maps
open CoreHint_t

type atom = AtomSetImpl.t

let generate_nop (core_hint:CoreHint_t.hints) : *

let insert_nop = 0 (* should be defined in Coq *)

let empty_unary : Invariant.unary =
  Invariant.mk_unary (empty_set, empty_set, empty_set, empty_set)

let empty_invariant : Invariant.t =
  Invariant.mk (empty_unary, empty_unary, empty_idt_set)

let create_empty_hints_stmts (stmts: LLVMsyntax.stmts) : Hints.stmts =
  match stmts with
  | Coq_stmts_intro (phinodes, cmds, _) ->
     let empty_hints_phinodes = 
       List.map (fun phi ->
                  match phi with
                  | LLVMsyntax.Coq_insn_phi (id,_,_) -> (id,[]))
                phinodes
     in
     let empty_hints_cmds =
       List.map (fun _ -> ([], empty_invariant)) cmd
     in
     Hints.mk_stmts (empty_hints_phinodes,
                     empty_invariant,
                     empty_hints_cmds)
     

let create_empty_hints_fdef (fdef:LLVMsyntax.fdef) : atom * Hints.fdef =
  match fdef with
  | Coq_fdef_intro (Coq_fheader_intro (_,_,id,_,_), blks) ->
     (id, List.map (fun (bid, bstmts) ->
                     (bid, create_empty_hints_stmts bstmts))
                   blks)

let create_empty_hints_module (m:LLVMsyntax.coq_module) : Hints.module =
  match m with
  | Coq_module_intro (lo, nts, prods) ->
     List.fold_left
       (fun empty_hints_prods prod ->
         match prod with
         | Coq_product_fdef fd ->
            (create_empty_hints_fdef fd)::empty_hints_prods
         | _ -> empty_hints_prods)
       [] prods

let noret = 0 (* don't know yet *)    

let execute_corehint_cmd
      (hints_fdef:Hints.fdef) (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (cmd:CoreHint_t.command) (dom_tree:LLVMsyntax.l coq_DTree)
    : Hints.fdef =
  match cmd with
  | CoreHint_t.Propagate prop -> 
  

let execute_corehint_cmds
      (hints_fdef:Hints.fdef) (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
      (cmds:CoreHint_t.command list) (dom_tree:LLVMsyntax.l coq_DTree)
    : Hints.fdef =
  List.fold_left
    (fun hint_f cmd ->
      execute_corehint_cmd hint_f lfdef rfdef cmd dom_tree)
    hints_fdef cmds
    
let translate_corehint_to_hint
      (lm_r:LLVMsyntax.coq_module) (rm_r:LLVMsyntax.coq_module)
      (core_hint:CoreHint_t.hints)
    : LLVMsyntax.coq_module * LLVMsyntax.coq_module * Hints.module =

  let fid = core_hint.function_id in
  
  let (lnop, rnop) = generate_nop core_hint in
  let lm = insert_nop lm_r lnop in
  let rm = insert_nop rm_r rnop in
  let hints_module = create_empty_hints_module lm in
  let hints_module = noret hints_module in (* TODO: noret? *)

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

  let hints_fdef = execute_corehint_cmds hints_fdef lfdef rfdef core_hint.commands dom_tree in
  let hints_module = Alist.updateAL hints_module fid hints_fdef in
  (lm, rm, hints_module)
  
