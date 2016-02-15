(* open Interpreter *)
open Printf
open Llvm
open Arg

open Yojson.Basic.Util
open Syntax.LLVMsyntax
open CoreHint_t


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


