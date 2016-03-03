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
  let tag (tag:CoreHint_t.tag): Tag.t =
    match tag with
    | CoreHint_t.Physical -> Tag.Coq_physical
    | CoreHint_t.Previous -> Tag.Coq_previous
    | CoreHint_t.Ghost -> Tag.Coq_ghost

  let register (var:CoreHint_t.register) : IdT.t =
    (tag var.tag, var.name)

  let const_int (const_int:CoreHint_t.const_int): INTEGER.t =
    let (is_signed, sz) =
      let (IntType (is_signed, sz)) = const_int.int_type in (is_signed, sz)
    in
    APInt.of_int64 sz (Int64.of_int const_int.int_value) is_signed

  let size (sz:CoreHint_t.size): LLVMsyntax.sz =
    let (Size sz) = sz in sz

  let value (value:LLVMsyntax.value): ValueT.t =
    match value with
    | Coq_value_id id -> ValueT.Coq_id (Tag.Coq_physical, id)
    | Coq_value_const const -> ValueT.Coq_const const

  let rhs_of (var:CoreHint_t.register) (fdef:LLVMsyntax.fdef) : Expr.t =
    let var_id = var.name in
    let insn = TODOCAML.get (LLVMinfra.lookupInsnViaIDFromFdef fdef var_id) in
      match insn with
      | LLVMsyntax.Coq_insn_cmd c ->
         (match c with
          | LLVMsyntax.Coq_insn_bop (_, bop, sz, v1, v2) ->
             Expr.Coq_bop (bop, sz, value v1, value v2)
          | LLVMsyntax.Coq_insn_fbop (_, fbop, fp, v1, v2) ->
             Expr.Coq_fbop (fbop, fp, value v1, value v2)
          | LLVMsyntax.Coq_insn_extractvalue (_, typ1, v, clist, typ2) ->
             Expr.Coq_extractvalue (typ1, value v, clist, typ2)
          | LLVMsyntax.Coq_insn_insertvalue (_, typ1, v1, typ2, v2, clist) ->
             Expr.Coq_insertvalue (typ1, value v1, typ2, value v2, clist)
          | LLVMsyntax.Coq_insn_gep (_, inbounds, typ1, v1, szv, typ2) ->
             Expr.Coq_gep (inbounds, typ1, value v1, List.map (fun szv -> (fst szv, value (snd szv))) szv, typ2)
          | LLVMsyntax.Coq_insn_trunc (_, truncop, typ1, v, typ2) ->
             Expr.Coq_trunc (truncop, typ1, value v, typ2)
          | LLVMsyntax.Coq_insn_ext (_, extop, typ1, v, typ2) ->
             Expr.Coq_ext (extop, typ1, value v, typ2)
          | LLVMsyntax.Coq_insn_cast (_, castop, typ1, v, typ2) ->
             Expr.Coq_cast (castop, typ1, value v, typ2)
          | LLVMsyntax.Coq_insn_icmp (_, cond, typ, v1, v2) ->
             Expr.Coq_icmp (cond, typ, value v1, value v2)
          | LLVMsyntax.Coq_insn_fcmp (_, fcond, fp, v1, v2) ->
             Expr.Coq_fcmp (fcond, fp, value v1, value v2)
          | LLVMsyntax.Coq_insn_select (_, v1, typ, v2, v3) ->
             Expr.Coq_select (value v1, typ, value v2, value v3)
          | LLVMsyntax.Coq_insn_load (_, typ, v, align) ->
             Expr.Coq_load (value v, typ, align)
          | _ -> failwith "convertUtil: rhs_of no matching cmd")
      | _ -> failwith "convertUtil: rhs_of find no insn"
end
