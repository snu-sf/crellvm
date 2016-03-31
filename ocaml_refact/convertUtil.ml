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

  let idx_any_phinode: idx = Phinode "any"

  let idx_lt (i:idx) (j:idx): bool =
    match i, j with
    | _, Phinode _ -> false
    | Phinode _, Command _ -> true
    | Command m, Command n -> m < n

  let idx_le (i:idx) (j:idx): bool =
    not (idx_lt j i)

  let idx_next (cur_idx:idx): idx =
    match cur_idx with
    | Phinode _ -> Command 0
    | Command n -> Command (n+1)

  let idx_final (bid:atom) (fdef:LLVMsyntax.fdef): idx =
    let _, LLVMsyntax.Coq_stmts_intro (_, cmds, _) =
      TODOCAML.get (LLVMinfra.lookupBlockViaIDFromFdef fdef bid)
    in
    Command (List.length cmds)

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
       TODOCAML.get (LLVMinfra.lookupBlockViaIDFromFdef fdef command.register_name)
     in
     let (idx, _) =
       TODOCAML.findi
         (fun _ cmd -> LLVMinfra.getCmdLoc cmd = command.register_name)
         cmds
     in
     (l, Command idx)

  let convert_to_id (pos : CoreHint_t.position)
              (fdef : LLVMsyntax.fdef)
              : Syntax.LLVMsyntax.id =
  match pos with
  | CoreHint_t.Phinode phinode ->
     let b = TODOCAML.get (LLVMinfra.lookupBlockViaLabelFromFdef fdef phinode.block_name) in
     let Coq_stmts_intro (ps, _, _) = b in
     let p : Syntax.LLVMsyntax.phinode =
       TODOCAML.get (LLVMinfra.lookupPhiNodeViaIDFromPhiNodes ps phinode.prev_block_name) in
     LLVMinfra.getPhiNodeID p
  | CoreHint_t.Command command ->
     let (l, Coq_stmts_intro (_, cmds, _)) =
       TODOCAML.get (LLVMinfra.lookupBlockViaIDFromFdef fdef command.register_name)
     in
     List.find (fun x -> x = command.register_name) (List.map LLVMinfra.getCmdLoc cmds)

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

  let register (register:CoreHint_t.register) : IdT.t =
    (tag register.tag, register.name)

  let const_int (const_int:CoreHint_t.const_int): INTEGER.t =
    let IntType sz = const_int.int_type in
    APInt.of_int64 sz (Int64.of_int const_int.int_value) true

  let const_float (const_float:CoreHint_t.const_float): FLOAT.t = 
    let cxt:Llvm.llcontext = Llvm.create_context () in 
    let ty:Llvm.lltype = 
        (fun (cxt:Llvm.llcontext) ->
        match const_float.float_type with
        | CoreHint_t.HalfType -> failwith "Llvm ocaml binding does not have half type."
        | CoreHint_t.FloatType -> Llvm.float_type cxt
        | CoreHint_t.DoubleType -> Llvm.double_type cxt
        | CoreHint_t.FP128Type -> Llvm.fp128_type cxt
        | CoreHint_t.PPC_FP128Type -> Llvm.ppc_fp128_type cxt
        | CoreHint_t.X86_FP80Type -> Llvm.x86fp80_type cxt)
        cxt in
    let _ = Llvm.dispose_context cxt in
    let lval:Llvm.llvalue = Llvm.const_float ty (const_float.float_value) in
    Llvm.APFloat.const_float_get_value lval

  let size (sz:CoreHint_t.size): LLVMsyntax.sz =
    let (Size sz) = sz in sz

  let llvmvalue (value:LLVMsyntax.value): ValueT.t =
    match value with
    | Coq_value_id id -> ValueT.Coq_id (Tag.Coq_physical, id)
    | Coq_value_const const -> ValueT.Coq_const const

  let constant (constval:CoreHint_t.constant): LLVMsyntax.const = 
    match constval with 
    | CoreHint_t.ConstInt ci -> 
       LLVMsyntax.Coq_const_int 
         ((match ci.int_type with 
            | CoreHint_t.IntType sz -> sz)
         , const_int ci)
    | CoreHint_t.ConstFloat cf ->
       LLVMsyntax.Coq_const_floatpoint (
         (match cf.float_type with
         | CoreHint_t.HalfType -> failwith "Vellvm has no Halftype" 
         | CoreHint_t.FloatType -> LLVMsyntax.Coq_fp_float
         | CoreHint_t.DoubleType -> LLVMsyntax.Coq_fp_double
         | CoreHint_t.FP128Type -> LLVMsyntax.Coq_fp_fp128
         | CoreHint_t.PPC_FP128Type -> LLVMsyntax.Coq_fp_ppc_fp128
         | CoreHint_t.X86_FP80Type -> LLVMsyntax.Coq_fp_x86_fp80)
         , const_float cf)
   

  let value (value:CoreHint_t.value): ValueT.t = 
    match value with
    | CoreHint_t.Id reg -> ValueT.Coq_id (register reg)
    | CoreHint_t.ConstVal constval -> ValueT.Coq_const (constant constval)

  let rhs_of (register:CoreHint_t.register) (fdef:LLVMsyntax.fdef) : Expr.t =
    let register_id = register.name in
    let insn = TODOCAML.get (LLVMinfra.lookupInsnViaIDFromFdef fdef register_id) in
      match insn with
      | LLVMsyntax.Coq_insn_cmd c ->
          let _ = print_endline(Coq_pretty_printer.string_of_cmd c) in
         (match c with
          | LLVMsyntax.Coq_insn_bop (_, bop, sz, v1, v2) ->
             Expr.Coq_bop (bop, sz, llvmvalue v1, llvmvalue v2)
          | LLVMsyntax.Coq_insn_fbop (_, fbop, fp, v1, v2) ->
             Expr.Coq_fbop (fbop, fp, llvmvalue v1, llvmvalue v2)
          | LLVMsyntax.Coq_insn_extractvalue (_, typ1, v, clist, typ2) ->
             Expr.Coq_extractvalue (typ1, llvmvalue v, clist, typ2)
          | LLVMsyntax.Coq_insn_insertvalue (_, typ1, v1, typ2, v2, clist) ->
             Expr.Coq_insertvalue (typ1, llvmvalue v1, typ2, llvmvalue v2, clist)
          | LLVMsyntax.Coq_insn_gep (_, inbounds, typ1, v1, szv, typ2) ->
             Expr.Coq_gep (inbounds, typ1, llvmvalue v1, List.map (fun szv -> (fst szv, llvmvalue (snd szv))) szv, typ2)
          | LLVMsyntax.Coq_insn_trunc (_, truncop, typ1, v, typ2) ->
             Expr.Coq_trunc (truncop, typ1, llvmvalue v, typ2)
          | LLVMsyntax.Coq_insn_ext (_, extop, typ1, v, typ2) ->
             Expr.Coq_ext (extop, typ1, llvmvalue v, typ2)
          | LLVMsyntax.Coq_insn_cast (_, castop, typ1, v, typ2) ->
             Expr.Coq_cast (castop, typ1, llvmvalue v, typ2)
          | LLVMsyntax.Coq_insn_icmp (_, cond, typ, v1, v2) ->
             Expr.Coq_icmp (cond, typ, llvmvalue v1, llvmvalue v2)
          | LLVMsyntax.Coq_insn_fcmp (_, fcond, fp, v1, v2) ->
             Expr.Coq_fcmp (fcond, fp, llvmvalue v1, llvmvalue v2)
          | LLVMsyntax.Coq_insn_select (_, v1, typ, v2, v3) ->
             Expr.Coq_select (llvmvalue v1, typ, llvmvalue v2, llvmvalue v3)
          | LLVMsyntax.Coq_insn_load (_, typ, v, align) ->
             Expr.Coq_load (llvmvalue v, typ, align)
          | _ -> failwith "convertUtil: rhs_of no matching cmd")
      | _ -> failwith "convertUtil: rhs_of find no insn"


  let expr (e:CoreHint_t.expr) (src_fdef:LLVMsyntax.fdef) (tgt_fdef:LLVMsyntax.fdef) : Expr.t = 
    match e with
    | CoreHint_t.Var reg ->
       Expr.Coq_value (ValueT.Coq_id (register reg))
    | CoreHint_t.Const constval ->
       Expr.Coq_value (ValueT.Coq_const (constant constval))
    | CoreHint_t.Rhs (reg,scope) ->
       rhs_of reg 
       (match scope with
       | CoreHint_t.Source -> src_fdef
       | CoreHint_t.Target -> tgt_fdef)


end
