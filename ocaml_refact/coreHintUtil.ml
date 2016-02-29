(* open Interpreter *)
open Printf
open Llvm
open Arg

open Yojson.Basic.Util
open Syntax.LLVMsyntax
open CoreHint_t

open Exprs

(* line number starts from 0 *)
let rec get_pos_in_cmds (id:string) (cmds:LLVMsyntax.cmds) (n:int) : int =
  match cmds with
  | [] -> failwith "translateCoreHint: get_pos_in_cmds"
  | cmd::cmds ->
     let cmd_id = LLVMinfra.getCmdLoc cmd in (* getCmdID? *)
     if (id = cmd_id) then n
     else find_position_in_cmds id cmds (n+1)

(* TODO: name get_pos? *)
let get_pos_from_command (pos_cmd:CoreHint_t.pos_command)
                         (lfdef:LLVMsyntax.fdef)
                         (rfdef:LLVMsyntax.fdef)
    : string * int =
  let fdef =
    match pos_cmd.scope with
    | CoreHint_t.Source -> lfdef
    | CoreHint_t.Target -> rfdef
  in
  let var_id = pos_cmd.var_name in
  match (LLVMinfra.lookupBlockViaIDFromFdef fdef var_id) with
  | Some (l, Coq_stmts_intro (_, cmds, _)) ->
     (l, get_pos_in_cmds var_id cmds 0)
  | None -> failwith "translateCoreHint: position_of_var"


let convert_value_to_ValueT (v:LLVMsyntax.value): ValueT.t =
  0 (* TODO *)

let get_rhs_from_var (var_id:string) (fdef:LLVMsyntax.fdef) : Expr.t =
  match LLVMinfra.lookupInsnViaIDFromFdef fdef var_id with
  | Some insn ->
     (match insn with
      | LLVMsyntax.Coq_insn_phinode _ -> failwith "coreHintUtil: get_rhs_from_var phinode"
      | LLVMsyntax.Coq_insn_cmd c ->
         (match c with
          | LLVMsyntax.Coq_insn_bop (_, bop, sz, v1, v2) ->
             ..
         )
      | LLVMsyntax.Coq_insn_terminator _ -> failwith "coreHintUtil: get_rhs_from_var terminator"
     )
  | None -> failwith "coreHintUtil: get_rhs_from_var found no insn"

let convert_variable_to_IdT (var:CoreHint_t.variable) : IdT.t =
  let tag =
    match var.tag with
    | CoreHint_t.Physical -> Tag.physical
    | CoreHint_t.Previous -> Tag.previous
    | CoreHint_t.Ghost -> Tag.ghost
  in
  (tag,var. name)

(* currently not used *)
(* let convert_value_to_ValueT (core_value:CoreHint_t.value) : ValueT.t = *)
(*   match core_value with *)
(*   | CoreHint_t.VarValue (var : CoreHint_t.variable) -> *)
(*       ValueT.id (convert_variable_to_IdT var) *)
(*   | CoreHint_t.ConstValue (cv : CoreHint_t.const_value) -> *)
(*       match cv with *)
(*       | CoreHint_t.IntVal (iv : CoreHint_t.int_value) -> *)
(*         let (issigned : bool), (bitsize : int) = *)
(*         match iv.mytype with *)
(* 	| CoreHint_t.IntType (issigned, bitsize) -> *)
(* 	  issigned, bitsize *)
(* 	in *)
(* 	let api = Llvm.APInt.of_int64 bitsize (Int64.of_int iv.myvalue) issigned in *)
(* 	ValueT.const (LLVMsyntax.Coq_const_int (bitsize, api)) *)

(*       | CoreHint_t.FloatVal (fv : CoreHint_t.float_value) -> *)
(*         let (fptype : LLVMsyntax.floating_point) =  *)
(* 	  (match fv.mytype with *)
(* 	    | CoreHint_t.FloatType -> LLVMsyntax.Coq_fp_float *)
(* 	    | CoreHint_t.DoubleType -> LLVMsyntax.Coq_fp_double *)
(* 	    | CoreHint_t.FP128Type -> LLVMsyntax.Coq_fp_fp128 *)
(* 	    | CoreHint_t.X86_FP80Type -> LLVMsyntax.Coq_fp_ppc_fp128) *)
(* 	in *)
(* 	let ctx = Llvm.global_context () in *)
(* 	let llvalue = Llvm.const_float (Coq2llvm.translate_floating_point ctx fptype) fv.myvalue in *)
(* 	let apfloat = Llvm.APFloat.const_float_get_value llvalue in *)
(* 	ValueT.const (LLVMsyntax.Coq_const_floatpoint (fptype, apfloat)) *)


(* old functions *)

let corehint_block_pos_prev (pos : CoreHint_t.position) : CoreHint_t.position =
  match pos.instr_index with
    CoreHint_t.Command 0 -> {block_name = pos.block_name; instr_index = CoreHint_t.Phinode}
  | CoreHint_t.Command i -> {block_name = pos.block_name; instr_index = CoreHint_t.Command (i-1)}
  | _ -> failwith "corehint_block_pos_prev : juneyoung lee : ill-defined case.."

let corehint_block_pos_next (pos : CoreHint_t.position) : CoreHint_t.position =
  match pos.instr_index with
    CoreHint_t.Phinode -> {block_name = pos.block_name; instr_index = CoreHint_t.Command 0}
  | CoreHint_t.Command i -> {block_name = pos.block_name ; instr_index = CoreHint_t.Command (i+1)}
  | CoreHint_t.Terminator -> {block_name = pos.block_name ; instr_index = CoreHint_t.Terminator}

let corehint_block_pos_lt (lhs : CoreHint_t.instr_index) (rhs : CoreHint_t.instr_index) =
  match lhs, rhs with
    | CoreHint_t.Phinode, CoreHint_t.Phinode -> false
    | CoreHint_t.Phinode, _ -> true
    | _, CoreHint_t.Phinode -> false
    | CoreHint_t.Command i, CoreHint_t.Command j -> i < j
    | CoreHint_t.Command _, _ -> true
    | _, CoreHint_t.Command _ -> false
    | CoreHint_t.Terminator, CoreHint_t.Terminator -> false

let rec string_of_list_endline ?(indent=0) s l =
  let rec r l =
    match l with
    | [] -> ""
    | hd::tl ->
       (String.make indent ' ') ^ (s hd) ^ "\n"
       ^ (r tl)
  in
  r l

let rec string_of_alist_endline ?(indent=0) s l =
  let rec r l =
    match l with
    | [] -> ""
    | (label,hd)::tl ->
       (String.make indent ' ') ^ label ^ " ->\n"
       ^ (s hd)
       ^ (r tl)
  in
  r l

let rec string_of_list s l =
  let rec r l =
    match l with
    | [] -> ")"
    | hd::tl -> (s hd) ^ ", " ^ (r tl)
  in
  "(" ^ (r l)

let rec string_of_alist s l =
  let rec r l =
    match l with
    | [] -> ")"
    | (label,hd)::tl -> label ^ "=>" ^ (s hd) ^ ", " ^ (r tl)
  in
  "(" ^ (r l)
