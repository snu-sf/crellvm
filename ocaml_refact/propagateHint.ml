(*********************************)
(* propagate information in hint *)
(*********************************)
(* refactoring *)
open Infrastructure
open Printf
open Llvm
open Arg
open Syntax
open MetatheoryAtom
open Extraction_defs
open Dom_list
open Dom_tree
open CoreHint_t
open ConvertUtil
open DomTreeUtil
open Hints
open Exprs

type atom = AtomImpl.atom

module Reachable = struct
  (* @arg f: block id
   @arg t: block id
   @arg succ: graph between block ids
   @return: set of block ids
     - reachable from f
     - without passing through t
   *)
  let _filtered (f:atom) (ids:AtomSetImpl.t) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : bool * AtomSetImpl.t =
    let visit_f = ref false in
    let rec r (worklist:atom list) (visit:AtomSetImpl.t) : bool * AtomSetImpl.t =
      match worklist with
      | [] -> (!visit_f, visit)
      | work::worklist ->
         let (worklist, visit) =
           (match Maps_ext.ATree.get work succs with
            | None -> (worklist, visit)
            | Some succs ->
               List.fold_left
                 (fun (worklist, visit) succ ->
                   let _ =
                     if succ = f
                     then
                       visit_f := true
                     else ()
                   in
                   if AtomSetImpl.mem succ visit || not (AtomSetImpl.mem succ ids)
                   then (worklist, visit)
                   else (succ::worklist, AtomSetImpl.add succ visit))
                 (worklist, visit)
                 succs)
         in
         r worklist visit
    in
    r [f] (AtomSetImpl.singleton f)

  (* @arg f: block id
   @arg succ: graph between block ids
   @return: set of block ids
     - reachable from f
   *)
  let _from (f:atom) (succs:LLVMsyntax.ls Maps_ext.ATree.t) : AtomSetImpl.t =
    let rec r (worklist:atom list) (reached:AtomSetImpl.t) : AtomSetImpl.t =
      match worklist with
      | [] -> reached
      | work::worklist ->
         let (worklist, reached) =
           match Maps_ext.ATree.get work succs with
           | None -> (worklist, reached)
           | Some succs ->
              List.fold_left
                (fun (worklist,reached) succ ->
                  if AtomSetImpl.mem succ reached
                  then (worklist, reached)
                  else (succ::worklist, AtomSetImpl.add succ reached)
                )
                (worklist, reached)
                succs
         in
         r worklist reached
    in
    r [f] AtomSetImpl.empty

  (* the set of nodes that is reachable to "t" without visiting "f" in "fd". *)
  let to_block (t:atom) (ids:AtomSetImpl.t) (fd:LLVMsyntax.fdef) : bool * AtomSetImpl.t =
        if not (AtomSetImpl.mem t ids)
        then (false, AtomSetImpl.empty)
        else
          let predecessors = Cfg.predecessors fd in
          _filtered t ids predecessors

  (* the set of nodes that is reachable from "f". *)
  let from_block (f:atom) (fd:LLVMsyntax.fdef) : AtomSetImpl.t =
    _from f (Cfg.successors fd)
end
(* object for propagation *)

type invariant_object =
  | Lessdef_obj of ExprPair.t
  | Noalias_obj of IdT.t * IdT.t
  | Allocas_obj of IdT.t
  | Private_obj of IdT.t

(** Convert propagate object to coq-defined objs **)

(* TODO: fix convert_propagate_*, current code is wrong *)
let convert_propagate_expr_to_Expr
      (pv:CoreHint_t.propagate_expr)
      (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
    : Expr.t =
  match pv with
  | CoreHint_t.Var (var:CoreHint_t.variable) ->
     Expr.Coq_value (ValueT.Coq_id (Convert.variable_to_IdT var))
  | CoreHint_t.Rhs (var:CoreHint_t.variable) ->
     failwith "TODO"
  | CoreHint_t.Const (c:CoreHint_t.constant) ->
     failwith "TODO"

let convert_propagate_object
      (c_prop_obj:CoreHint_t.propagate_object)
      (lfdef:LLVMsyntax.fdef) (rfdef:LLVMsyntax.fdef)
    : invariant_object =
  match c_prop_obj with
  | CoreHint_t.Lessdef prop_ld ->
     Lessdef_obj (convert_propagate_expr_to_Expr prop_ld.lhs lfdef rfdef,
                  convert_propagate_expr_to_Expr prop_ld.rhs lfdef rfdef)
  | CoreHint_t.Noalias na ->
     Noalias_obj (Convert.variable_to_IdT na.lhs,
                  Convert.variable_to_IdT na.rhs)
  | CoreHint_t.Maydiff v ->
     failwith "TODO"

let position_lt (p1:position) (p2:position): bool =
  failwith "TODO"
  (* let (bid1, pib1) = p1 in *)
  (* let (bid2, pib2) = p2 in *)
  (* if bid1 = bid2 then *)
  (*   match pib2 with *)
  (*   | Phinode _ -> false *)
  (*   | Command n2 -> *)
  (*      (match pib1 with *)
  (*       | Phinode _ -> true *)
  (*       | Command n1 -> n1 < n2) *)
  (* else false *)

let propagate_hint
      (lfdef:LLVMsyntax.fdef)
      (dtree_lfdef:atom coq_DTree)
      (invariant:invariant_object)
      (range:Position.range)
      (hint_fdef:ValidationHint.fdef)
    : ValidationHint.fdef =
  failwith "TODO"

(* TODO: find bids
     propagate_invariant inv_obj (pos_from=pos_from) (pos_to=pos_to)
                         lfdef rfdef bids
  | CoreHint_t.Global ->
       (* TODO: all labels *)
  in
  propagate_invariant
    inv_obj (
*)