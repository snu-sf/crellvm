open Interpreter
open Printf
open Llvm
open Arg

exception Error

let llapint_add x y = 
  let x_bw = Llvm.APInt.get_bitwidth x in
  let y_bw = Llvm.APInt.get_bitwidth y in
  if x_bw <> y_bw then raise Error
  else Llvm.APInt.of_int64
    x_bw
    (Int64.add
       (Llvm.APInt.get_sext_value x)
       (Llvm.APInt.get_sext_value y))
    true

let llapint_sub x y = 
  let x_bw = Llvm.APInt.get_bitwidth x in
  let y_bw = Llvm.APInt.get_bitwidth y in
  if x_bw <> y_bw then raise Error
  else Llvm.APInt.of_int64
    x_bw
    (Int64.sub
       (Llvm.APInt.get_sext_value x)
       (Llvm.APInt.get_sext_value y))
    true
