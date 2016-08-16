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
    let LLVMsyntax.Coq_stmts_intro (_, cmds, _) =
      TODOCAML.get (LLVMinfra.lookupBlockViaLabelFromFdef fdef bid)
    in
    Command (List.length cmds)

  (* TODO: remove lfdef and rfdef *)
  let convert (pos:CoreHint_t.position)
              (nops:CoreHint_t.position list)
              (lfdef:LLVMsyntax.fdef)
              (rfdef:LLVMsyntax.fdef): t =
    match pos.CoreHint_t.instr_index with
    | CoreHint_t.Phinode phinode ->
       (pos.CoreHint_t.block_name,
        Phinode phinode.CoreHint_t.prev_block_name)
    | CoreHint_t.Command command ->
       let related_nops =
         List.filter (fun (p:CoreHint_t.position) ->
                      (p.CoreHint_t.scope = pos.CoreHint_t.scope) &&
                      (p.CoreHint_t.block_name = pos.CoreHint_t.block_name))
                     nops
       in
       let new_cmd_index =
         List.fold_left (fun idx nop ->
                         match nop.CoreHint_t.instr_index with
                         | Phinode _ -> idx + 1
                         | Command pos_cmd ->
                            if pos_cmd.CoreHint_t.index < idx
                            then idx + 1
                            else idx)
                        command.CoreHint_t.index related_nops
       in 
       (pos.CoreHint_t.block_name, Command new_cmd_index)

  (* let convert_to_id (pos : CoreHint_t.position) *)
  (*             (fdef : LLVMsyntax.fdef) *)
  (*             : Syntax.LLVMsyntax.id = *)
  (* match pos with *)
  (* | CoreHint_t.Phinode phinode -> *)
  (*    let b = TODOCAML.get (LLVMinfra.lookupBlockViaLabelFromFdef fdef phinode.block_name) in *)
  (*    let Coq_stmts_intro (ps, _, _) = b in *)
  (*    let p : Syntax.LLVMsyntax.phinode = *)
  (*      TODOCAML.get (LLVMinfra.lookupPhiNodeViaIDFromPhiNodes ps phinode.prev_block_name) in *)
  (*    LLVMinfra.getPhiNodeID p *)
  (* | CoreHint_t.Command command -> *)
  (*    let (l, Coq_stmts_intro (_, cmds, _)) = *)
  (*      TODOCAML.get (LLVMinfra.lookupBlockViaIDFromFdef fdef command.register_name) *)
  (*    in *)
  (*    List.find (fun x -> x = command.register_name) (List.map LLVMinfra.getCmdLoc cmds) *)

  let convert_range (range:CoreHint_t.propagate_range) (nops:CoreHint_t.position list) (lfdef:fdef) (rfdef:fdef) =
    match range with
    | CoreHint_t.Bounds (f, t) -> Bounds (convert f nops lfdef rfdef, convert t nops lfdef rfdef)
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

  let register (register:CoreHint_t.register) : IdT.t =
    (tag register.tag, register.name)
  
  let float_type (ft:CoreHint_t.float_type): LLVMsyntax.floating_point =
    match ft with
    | CoreHint_t.HalfType -> failwith "Vellvm has no Halftype" 
    | CoreHint_t.FloatType -> LLVMsyntax.Coq_fp_float
    | CoreHint_t.DoubleType -> LLVMsyntax.Coq_fp_double
    | CoreHint_t.FP128Type -> LLVMsyntax.Coq_fp_fp128
    | CoreHint_t.PPC_FP128Type -> LLVMsyntax.Coq_fp_ppc_fp128
    | CoreHint_t.X86_FP80Type -> LLVMsyntax.Coq_fp_x86_fp80

  let rec value_type (vt:CoreHint_t.value_type): LLVMsyntax.typ = 
    match vt with
    | CoreHint_t.VoidType -> LLVMsyntax.Coq_typ_void
    | CoreHint_t.IntValueType ciarg -> 
      (match ciarg with IntType sz -> LLVMsyntax.Coq_typ_int sz)
    | CoreHint_t.FloatValueType cfarg -> LLVMsyntax.Coq_typ_floatpoint (float_type cfarg)
    | CoreHint_t.NamedType typename -> LLVMsyntax.Coq_typ_namedt typename
    | CoreHint_t.PtrType (addrspace, ptrtype) -> 
        (match addrspace with
        | 0 -> LLVMsyntax.Coq_typ_pointer (value_type ptrtype)
        | _ -> failwith "Vellvm does not support pointer address with address space larger than 0")
    | CoreHint_t.ArrayType (arrsize, elemtype) ->
        LLVMsyntax.Coq_typ_array (arrsize, value_type elemtype)
    | CoreHint_t.FunctionType (retty, argtylist, isvararg, varargsize) ->
        LLVMsyntax.Coq_typ_function (value_type retty,
        List.map value_type argtylist,
        if isvararg then Some varargsize else None)
    | CoreHint_t.VectorType (arrsize, elemtype) ->
      failwith "Vellvm does not support vector type"
    | CoreHint_t.StructType (elemtylist) ->
        LLVMsyntax.Coq_typ_struct (List.map value_type elemtylist)
 
  let const_int (const_int:CoreHint_t.const_int): INTEGER.t =
    let IntType sz = const_int.int_type in
    APInt.of_int64 sz (Int64.of_string const_int.int_value) true

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
    let lval:Llvm.llvalue = Llvm.const_float ty (const_float.float_value) in
    Llvm.APFloat.const_float_get_value lval

  let size (sz:CoreHint_t.size): LLVMsyntax.sz =
    let (Size sz) = sz in sz

  let llvmvalue (value:LLVMsyntax.value): ValueT.t =
    match value with
    | Coq_value_id id -> ValueT.Coq_id (Tag.Coq_physical, id)
    | Coq_value_const const -> ValueT.Coq_const const

  let float_type (ft:CoreHint_t.float_type): LLVMsyntax.floating_point =
    match ft with
    | CoreHint_t.HalfType -> failwith "Vellvm has no Halftype" 
    | CoreHint_t.FloatType -> LLVMsyntax.Coq_fp_float
    | CoreHint_t.DoubleType -> LLVMsyntax.Coq_fp_double
    | CoreHint_t.FP128Type -> LLVMsyntax.Coq_fp_fp128
    | CoreHint_t.PPC_FP128Type -> LLVMsyntax.Coq_fp_ppc_fp128
    | CoreHint_t.X86_FP80Type -> LLVMsyntax.Coq_fp_x86_fp80


  let rec constant (constval:CoreHint_t.constant): LLVMsyntax.const = 
    match constval with 
    | CoreHint_t.ConstInt ci -> 
       LLVMsyntax.Coq_const_int 
         ((match ci.int_type with 
            | CoreHint_t.IntType sz -> sz)
         , const_int ci)
    | CoreHint_t.ConstFloat cf ->
       LLVMsyntax.Coq_const_floatpoint (float_type cf.float_type, const_float cf)
    | CoreHint_t.ConstGlobalVarAddr cgva ->
       LLVMsyntax.Coq_const_gid (value_type cgva.var_type, cgva.var_id)
    | CoreHint_t.ConstUndef vt ->
       LLVMsyntax.Coq_const_undef (value_type vt)
    | CoreHint_t.ConstNull (addrspace, vt) ->
       (match addrspace with
        | 0 -> LLVMsyntax.Coq_const_null (value_type vt)
        | _ -> failwith "Vellvm does not support pointer address with address space larger than 0")
    | CoreHint_t.ConstDataVector (elemty, elements) ->
       failwith "Vellvm does not support vector type"
    | CoreHint_t.ConstExpr ce ->
       constant_expr ce
  
  and constant_expr (ce:CoreHint_t.constant_expr) : LLVMsyntax.const = 
    match ce with
    | CoreHint_t.ConstExprGetElementPtr cegep ->
       LLVMsyntax.Coq_const_gep (cegep.is_inbounds, 
                constant cegep.v, 
                List.map (fun v -> constant v) cegep.idxlist)
    | CoreHint_t.ConstExprBitcast ceb ->
       LLVMsyntax.Coq_const_castop (LLVMsyntax.Coq_castop_bitcast, (constant ceb.v), (value_type ceb.dstty))
    | CoreHint_t.ConstExprInttoptr cei ->
       LLVMsyntax.Coq_const_castop (LLVMsyntax.Coq_castop_inttoptr, (constant cei.v), (value_type cei.dstty))
    | CoreHint_t.ConstExprPtrtoint cep ->
       LLVMsyntax.Coq_const_castop (LLVMsyntax.Coq_castop_ptrtoint, (constant cep.v), (value_type cep.dstty))
    | _ -> failwith "convertUtil.constant_expr : Unknown constant expression"

  let value (value:CoreHint_t.value): ValueT.t = 
    match value with
    | CoreHint_t.Id reg -> ValueT.Coq_id (register reg)
    | CoreHint_t.ConstVal constval -> ValueT.Coq_const (constant constval)

  let pointer (ptr:CoreHint_t.pointer) : Ptr.t = 
    (value ptr.v, value_type ptr.ty)

  let rhs_of (register:CoreHint_t.register) (fdef:LLVMsyntax.fdef) : Expr.t =
    let register_id = register.name in
    let insn = TODOCAML.get (LLVMinfra.lookupInsnViaIDFromFdef fdef register_id) in
      match insn with
      | LLVMsyntax.Coq_insn_cmd c ->
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
          | _ -> failwith ("convertUtil: rhs_of no matching cmd: " ^ (Coq_pretty_printer.string_of_cmd c)))
      | _ -> failwith "convertUtil: rhs_of find no insn"

  let fbop (b:CoreHint_t.fbop) : LLVMsyntax.fbop = 
    match b with
    | CoreHint_t.BopFadd -> LLVMsyntax.Coq_fbop_fadd
    | CoreHint_t.BopFsub -> LLVMsyntax.Coq_fbop_fsub
    | CoreHint_t.BopFmul -> LLVMsyntax.Coq_fbop_fmul
    | CoreHint_t.BopFdiv -> LLVMsyntax.Coq_fbop_fdiv
    | CoreHint_t.BopFrem -> LLVMsyntax.Coq_fbop_frem
    | _ -> failwith "In ConvertUtil.fbop : unknown fbop"

  let bop (b:CoreHint_t.bop) : LLVMsyntax.bop = 
    match b with
    | CoreHint_t.BopAdd -> LLVMsyntax.Coq_bop_add
    | CoreHint_t.BopSub -> LLVMsyntax.Coq_bop_sub
    | CoreHint_t.BopMul -> LLVMsyntax.Coq_bop_mul
    | CoreHint_t.BopUdiv -> LLVMsyntax.Coq_bop_udiv
    | CoreHint_t.BopSdiv -> LLVMsyntax.Coq_bop_sdiv
    | CoreHint_t.BopUrem -> LLVMsyntax.Coq_bop_urem
    | CoreHint_t.BopSrem -> LLVMsyntax.Coq_bop_srem
    | CoreHint_t.BopShl -> LLVMsyntax.Coq_bop_shl
    | CoreHint_t.BopLshr -> LLVMsyntax.Coq_bop_lshr
    | CoreHint_t.BopAshr -> LLVMsyntax.Coq_bop_ashr
    | CoreHint_t.BopAnd -> LLVMsyntax.Coq_bop_and
    | CoreHint_t.BopOr -> LLVMsyntax.Coq_bop_or
    | CoreHint_t.BopXor -> LLVMsyntax.Coq_bop_xor
    | _ -> failwith "In ConvertUtil.bop : Unknown bop"
 
 let fcond (c:CoreHint_t.fcmp_pred) : LLVMsyntax.fcond = 
    match c with
    | CoreHint_t.CondFfalse -> LLVMsyntax.Coq_fcond_false
    | CoreHint_t.CondFoeq -> LLVMsyntax.Coq_fcond_oeq
    | CoreHint_t.CondFogt -> LLVMsyntax.Coq_fcond_ogt
    | CoreHint_t.CondFoge -> LLVMsyntax.Coq_fcond_oge
    | CoreHint_t.CondFolt -> LLVMsyntax.Coq_fcond_olt
    | CoreHint_t.CondFole -> LLVMsyntax.Coq_fcond_ole
    | CoreHint_t.CondFone -> LLVMsyntax.Coq_fcond_one
    | CoreHint_t.CondFord -> LLVMsyntax.Coq_fcond_ord
    | CoreHint_t.CondFuno -> LLVMsyntax.Coq_fcond_uno    
    | CoreHint_t.CondFueq -> LLVMsyntax.Coq_fcond_ueq
    | CoreHint_t.CondFugt -> LLVMsyntax.Coq_fcond_ugt
    | CoreHint_t.CondFuge -> LLVMsyntax.Coq_fcond_uge
    | CoreHint_t.CondFult -> LLVMsyntax.Coq_fcond_ult
    | CoreHint_t.CondFule -> LLVMsyntax.Coq_fcond_ule
    | CoreHint_t.CondFune -> LLVMsyntax.Coq_fcond_une
    | CoreHint_t.CondFtrue -> LLVMsyntax.Coq_fcond_true
    | _ -> failwith "In ConvertUtil. fcond : Unknown fcond"

 let cond (c:CoreHint_t.icmp_pred) : LLVMsyntax.cond = 
   match c with
   | CoreHint_t.CondEq -> LLVMsyntax.Coq_cond_eq
   | CoreHint_t.CondNe -> LLVMsyntax.Coq_cond_ne
   | CoreHint_t.CondUgt -> LLVMsyntax.Coq_cond_ugt
   | CoreHint_t.CondUge -> LLVMsyntax.Coq_cond_uge
   | CoreHint_t.CondUlt -> LLVMsyntax.Coq_cond_ult
   | CoreHint_t.CondUle -> LLVMsyntax.Coq_cond_ule
   | CoreHint_t.CondSgt -> LLVMsyntax.Coq_cond_sgt
   | CoreHint_t.CondSge -> LLVMsyntax.Coq_cond_sge
   | CoreHint_t.CondSlt -> LLVMsyntax.Coq_cond_slt
   | CoreHint_t.CondSle -> LLVMsyntax.Coq_cond_sle
   | _ -> failwith "In ConvertUtil. cond : Unknown cond"

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
    | CoreHint_t.Insn instr ->
       (match instr with
       | CoreHint_t.BinaryOp bop_arg ->
         let vellvmbop = bop bop_arg.opcode in
         (match bop_arg.operandtype with
         | IntValueType ivt ->
           (match ivt with IntType sz ->
           Expr.Coq_bop (vellvmbop, sz, value bop_arg.operand1, value bop_arg.operand2))
         | _ -> failwith "Only integer type is allowed")
       | CoreHint_t.FloatBinaryOp fbop_arg ->
         let vellvmfbop = fbop fbop_arg.opcode in
         (match value_type fbop_arg.operandtype with
         | LLVMsyntax.Coq_typ_floatpoint fptype ->
           Expr.Coq_fbop (vellvmfbop, fptype, 
                      value fbop_arg.operand1, value fbop_arg.operand2)
         | _ -> failwith "Only floating type is allowed")
      | CoreHint_t.ICmpInst icmp_arg ->
          let vellvmicmp = cond icmp_arg.predicate in
          (match icmp_arg.operandtype with
          | IntValueType ivt ->
            Expr.Coq_icmp (vellvmicmp, value_type (IntValueType ivt), value icmp_arg.operand1, value icmp_arg.operand2)
          | PtrType pt ->
            Expr.Coq_icmp (vellvmicmp, value_type (PtrType pt), value icmp_arg.operand1, value icmp_arg.operand2)  
          | _ -> failwith "Only integer type is allowed")
      | CoreHint_t.FCmpInst fcmp_arg ->
          let vellvmfcmp = fcond fcmp_arg.predicate in 
          (match value_type fcmp_arg.operandtype with
          | LLVMsyntax.Coq_typ_floatpoint fptype ->
            Expr.Coq_fcmp (vellvmfcmp, fptype, 
                       value fcmp_arg.operand1, value fcmp_arg.operand2)
          | _ -> failwith "Only floating type is allowed")
       | CoreHint_t.LoadInst li_arg ->
         Expr.Coq_load (value li_arg.ptrvalue, value_type li_arg.valtype, li_arg.align)
       | CoreHint_t.BitCastInst arg ->
         Expr.Coq_cast (LLVMsyntax.Coq_castop_bitcast, value_type arg.fromty, 
                value arg.v, value_type arg.toty)
       | CoreHint_t.IntToPtrInst arg ->
         Expr.Coq_cast (LLVMsyntax.Coq_castop_inttoptr, value_type arg.fromty, 
                value arg.v, value_type arg.toty)
       | CoreHint_t.PtrToIntInst arg ->
         Expr.Coq_cast (LLVMsyntax.Coq_castop_ptrtoint, value_type arg.fromty, 
                value arg.v, value_type arg.toty)
       | CoreHint_t.GetElementPtrInst gepi_arg ->
         Expr.Coq_gep (gepi_arg.is_inbounds, 
                value_type gepi_arg.ty, 
                value gepi_arg.ptr,
                List.map (fun szv -> (size (fst szv), value (snd szv))) gepi_arg.indexes,
                value_type gepi_arg.retty)
       | CoreHint_t.SelectInst arg ->
         Expr.Coq_select (value arg.cond, value_type arg.valty,
                value arg.trueval, value arg.falseval)
       | CoreHint_t.FpextInst arg ->
         Expr.Coq_ext (LLVMsyntax.Coq_extop_fp, value_type arg.fromty, 
                value arg.v, value_type arg.toty)
       | CoreHint_t.FptruncInst arg ->
         Expr.Coq_trunc (LLVMsyntax.Coq_truncop_fp, value_type arg.fromty, 
                value arg.v, value_type arg.toty)
       | CoreHint_t.ZextInst arg ->
         Expr.Coq_ext (LLVMsyntax.Coq_extop_z, value_type arg.fromty,
                value arg.v, value_type arg.toty)
       | CoreHint_t.SextInst arg ->
         Expr.Coq_ext (LLVMsyntax.Coq_extop_s, value_type arg.fromty,
                value arg.v, value_type arg.toty)
       | CoreHint_t.TruncInst arg ->
         Expr.Coq_trunc (LLVMsyntax.Coq_truncop_int, value_type arg.fromty,
                value arg.v, value_type arg.toty)
       | CoreHint_t.SitofpInst arg ->
         Expr.Coq_cast (LLVMsyntax.Coq_castop_sitofp, value_type arg.fromty,
                value arg.v, value_type arg.toty)
       | CoreHint_t.UitofpInst arg ->
         Expr.Coq_cast (LLVMsyntax.Coq_castop_uitofp, value_type arg.fromty,
                value arg.v, value_type arg.toty)
       | _ -> failwith "Unknown instruction type"
       )
end
