open Printf
open Llvm
open Arg
open Yojson.Basic.Util
open MetatheoryAtom
open Syntax.LLVMsyntax
open CoreHint_t
open Infrastructure
open Syntax
open Exprs
open APInt
open Datatype_base

type atom = AtomImpl.atom

module Position = struct
  type idx =
    | Phinode of atom
    | Command of int

  type t = atom * idx

  type range =
    | Bounds of (t * t)
    | Global

  let convert (pos:CoreHint_t.position)
              (lfdef:LLVMsyntax.fdef)
              (rfdef:LLVMsyntax.fdef): t =
  match pos with
  | CoreHint_t.Phinode phinode ->
     (phinode.block_name, Phinode phinode.prev_block_name)
  | CoreHint_t.Command command ->
     let fdef =
       if command.scope = CoreHint_t.Source
       then lfdef
       else rfdef
     in
     let (l, Coq_stmts_intro (_, cmds, _)) =
       TODOCAML.get (LLVMinfra.lookupBlockViaIDFromFdef fdef command.var_name)
     in
     let (idx, _) =
       TODOCAML.findi
         (fun _ cmd -> LLVMinfra.getCmdLoc cmd = command.var_name)
         cmds
     in
     (l, Command idx)

  let convert_range (range:CoreHint_t.propagate_range) (lfdef:fdef) (rfdef:fdef) =
    match range with
    | CoreHint_t.Bounds (f, t) -> Bounds (convert f lfdef rfdef, convert t lfdef rfdef)
    | CoreHint_t.Global -> Global
end

module Convert = struct
  let variable_to_rhs_Expr (var:CoreHint_t.variable) (fdef:LLVMsyntax.fdef) : Expr.t =
    let var_id = var.name in
    match LLVMinfra.lookupInsnViaIDFromFdef fdef var_id with
    | Some insn ->
       (match insn with
        | LLVMsyntax.Coq_insn_phinode _ -> failwith "coreHintUtil: get_rhs_from_var phinode"
        | LLVMsyntax.Coq_insn_cmd c ->
           (match c with
            | LLVMsyntax.Coq_insn_bop (_, bop, sz, v1, v2) ->
               (* TODO *)
               failwith "TODO"
            | _ -> failwith "TODO"
           )
        | LLVMsyntax.Coq_insn_terminator _ -> failwith "coreHintUtil: get_rhs_from_var terminator"
       )
    | None -> failwith "coreHintUtil: get_rhs_from_var found no insn"

  let variable_to_IdT (var:CoreHint_t.variable) : IdT.t =
    let tag =
      match var.tag with
      | CoreHint_t.Physical -> Tag.Coq_physical
      | CoreHint_t.Previous -> Tag.Coq_previous
      | CoreHint_t.Ghost -> Tag.Coq_ghost
    in
    (tag, var.name)

  let const_int_to_INTEGER (const_int:CoreHint_t.const_int): INTEGER.t =
    let (is_signed, sz) =
      match const_int.int_type with
      | IntType (is_signed, sz) -> (is_signed, sz) in
    APInt.of_int64 sz (Int64.of_int const_int.int_value) is_signed

  let size_to_sz (sz:CoreHint_t.size): LLVMsyntax.sz =
    match sz with
    | Size sz -> sz
end
