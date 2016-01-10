(* open Interpreter *)
open Printf
open Llvm
open Arg

open Yojson.Basic.Util
open Syntax.LLVMsyntax
open HintParser_t


let rhint_block_pos_prev (pos : HintParser_t.position) : HintParser_t.position =
  match pos.instr_type with
    HintParser_t.Command 0 -> {block_index = pos.block_index; instr_type = HintParser_t.Phinode}
  | HintParser_t.Command i -> {block_index = pos.block_index; instr_type = HintParser_t.Command (i-1)}
  | _ -> failwith "rhint_block_pos_prev : juneyoung lee : ill-defined case.."

let rhint_block_pos_next (pos : HintParser_t.position) : HintParser_t.position =
  match pos.instr_type with
    HintParser_t.Phinode -> {block_index = pos.block_index; instr_type = HintParser_t.Command 0}
  | HintParser_t.Command i -> {block_index = pos.block_index ; instr_type = HintParser_t.Command (i+1)}
  | HintParser_t.Terminator -> {block_index = pos.block_index ; instr_type = HintParser_t.Terminator}

let rhint_block_pos_lt (lhs : HintParser_t.instr_type) (rhs : HintParser_t.instr_type) =
  match lhs, rhs with
    | HintParser_t.Phinode, HintParser_t.Phinode -> false
    | HintParser_t.Phinode, _ -> true
    | _, HintParser_t.Phinode -> false
    | HintParser_t.Command i, HintParser_t.Command j -> i < j
    | HintParser_t.Command _, _ -> true
    | _, HintParser_t.Command _ -> false
    | HintParser_t.Terminator, HintParser_t.Terminator -> false

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


