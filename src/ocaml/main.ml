(* open Interpreter *)
open Printf
open Llvm
open Llvm_executionengine
open Arg
open Syntax.LLVMsyntax

let out_file = ref stdout

let debug_print s = if !Globalstates.debug then print_endline ("DEBUG: "^s^"...") else ()

let main original_filename optimized_filename hint_filename =
  (* main1.native: let _ = read_line () in *)

  (* Read bitcode [*_filename] into LLVM module [im1] and [im2] *)
  (* Translate LLVM module [im] to Coq module [coqim] *)
  let _ = debug_print "create_context" in
  let ic1 = create_context () in
  let _ = debug_print "imbuf1" in
  let imbuf1 = MemoryBuffer.of_file original_filename in
  let _ = debug_print "im1" in
  let im1 = Llvm_bitreader.parse_bitcode ic1 imbuf1 in
  let _ = debug_print "ist1" in
  let ist1 = SlotTracker.create_of_module im1 in
  (* let _ = Gc.full_major () in *)
  let _ = debug_print "coqim1" in
  let coqim1 = 
    try Tt.translate_module (*true*) !Globalstates.debug ist1 im1 with 
    | Failure ("InlineAsmVal: Not_Supported.") -> 
      (print_endline "Validation aborted: InlineAsmVal"; exit 0)
    | Failure ("BlockAddress isnt Constant") ->
      (print_endline "Validation aborted: BlockAddress"; exit 0)
  in
  let _ = debug_print "something big" in
  let _ = 
    (if !Globalstates.debug then dump_module im1);
    (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist1 im1);
    (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim1);
    () in
  
  (* main2.native: let _ = read_line () in *)

  let _ = debug_print "ic2 create_context" in
  let ic2 = create_context () in
  let _ = debug_print "imbuf2" in
  let imbuf2 = MemoryBuffer.of_file optimized_filename in
  let _ = debug_print "im2" in
  let im2 = Llvm_bitreader.parse_bitcode ic2 imbuf2 in
  let _ = debug_print "ist2" in
  let ist2 = SlotTracker.create_of_module im2 in
  (* let _ = Gc.full_major () in *)
  let _ = debug_print "coqim2" in
  let coqim2 = 
    try Tt.translate_module (*true*) !Globalstates.debug ist2 im2 with 
    | Failure ("InlineAsmVal: Not_Supported.") -> 
      (print_endline "Validation aborted: InlineAsmVal"; exit 0)
    | Failure ("BlockAddress isnt Constant") ->
      (print_endline "Validation aborted: BlockAddress"; exit 0)
  in
  (* let _ = print_endline "original rm" in *)
  (* let _ = Llvm_pretty_printer.travel_module ist2 im2 in *)
  (* let _ = print_endline "translated rm" in *)
  (* let _ = Coq_pretty_printer.travel_module coqim2 in *)
  let _ = debug_print "something big2" in
  let _ = 
    (if !Globalstates.debug then dump_module im2);
    (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist2 im2);
    (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim2);

    (* SlotTracker.dispose ist1; *)
    (* dispose_module im1; *)
    (* dispose_context ic1; *)

    (* SlotTracker.dispose ist2; *)
    (* dispose_module im2; *)
    (* dispose_context ic2; *)
    () in

  (*let _ = print_endline "lm" in
  let _ = Coq_pretty_printer.travel_module coqim1 in
  let _ = print_endline "rm" in
  let _ = Coq_pretty_printer.travel_module coqim2 in*)

  (* read hint *)
  let _ = debug_print "yojson read hint" in
  let raw_hint_json = Yojson.Basic.from_file hint_filename in
  (* let _ = print_endline "printing json hint" in *)
  (* let _ = Yojson.Basic.pretty_to_channel stdout raw_hint_json in *)
  (* let _ = print_endline "" in *)

  let _ = debug_print "parse hint" in
  let raw_hint = ParseHints.parse_hints raw_hint_json in
  (* let _ = print_endline "printing parsed hint" in *)
  (* let _ = print_endline (ParseHints.string_of_rhints raw_hint) in *)

  (* translate hint *)
  let _ = debug_print "translate hint" in
  let (hint,noop1,noop2) = TranslateHints.translate_hint_module coqim1 coqim2 raw_hint in
  (*let _ = print_endline "hint translated" in
  let _ = print_endline (PrintHints.string_of_module_hint hint) in
  let _ = print_endline "noop1" in 
  let _ = print_endline (TranslateHints.string_of_product_noop noop1) in
  let _ = print_endline "noop2" in 
  let _ = print_endline (TranslateHints.string_of_product_noop noop2) in*)


  (* validation *)
  let _ = debug_print "validation" in
  let validation_result = Validator.valid_module coqim1 coqim2 noop1 noop2 hint in
  let _ = if validation_result 
    then print_endline "Validation succeeded."
    else (prerr_endline "Validation failed."; exit 1)
  in

  (* Translate [coqom] to a *.ll file *)
  (* Coq2ll.travel_module !out_file coqom; *)

  ()

let argspec = [
  ("-d", Set Globalstates.debug, "debug");
  ("-o", String (fun s -> 
                 try out_file := open_out s
                 with Sys_error _ -> failwith ("cannot open " ^ s)), 
   "output file")
]

let () = 
  let worklist = ref [] in
  Arg.parse argspec (fun f -> worklist := f :: !worklist) "Validation \n";
  match !worklist with
  | hint_filename::optimized_filename::original_filename::[] -> main original_filename optimized_filename hint_filename
  | _ -> print_endline "input filenames. ex) ./main.native file1.bc file2.bc hint.json"; exit 1
