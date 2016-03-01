(* open Interpreter *)
open Printf
open Llvm
open Arg

open Yojson.Basic.Util
open Syntax.LLVMsyntax
open CoreHint_t

open Exprs

module Position = struct
  (* line number starts from 0 *)
  let rec get_pos_in_cmds (id:string) (cmds:LLVMsyntax.cmds) (n:int) : int =
  match cmds with
  | [] -> failwith "translateCoreHint: get_pos_in_cmds"
  | cmd::cmds ->
     let cmd_id = LLVMinfra.getCmdLoc cmd in (* getCmdID? *)
     if (id = cmd_id) then n
     else find_position_in_cmds id cmds (n+1)

  (* TODO: name get_pos? *)
  let get_pos_from_command (pos_cmd:CoreHint_t.position_command)
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

  let get_block_name_from_position (pos:CoreHint_t.position)
                                 (lfdef:LLVMsyntax.fdef)
                                 (rfdef:LLVMsyntax.fdef) : string =
  match pos with
  | CoreHint_t.Phinode phinode -> phinode.block_name
  | CoreHint_t.Command command ->
      let (bid, _) = get pos_from_command command lfdef rfdef in
      bid
end

module Convert = struct
  let var_to_rhs_Expr (var_id:string) (fdef:LLVMsyntax.fdef) : Expr.t =
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

  let variable_to_IdT (var:CoreHint_t.variable) : IdT.t =
    let tag =
      match var.tag with
      | CoreHint_t.Physical -> Tag.physical
      | CoreHint_t.Previous -> Tag.previous
      | CoreHint_t.Ghost -> Tag.ghost
    in
    (tag, var.name)

  let const_int_to_INTEGER (v:CoreHint_t.const_int): INTEGER.t =
    0 (* TODO *)

  let size_to_sz (sz:CoreHint_t.size): LLVMsyntax.sz =
    0 (* TODO *)
end

(* old functions *)

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
