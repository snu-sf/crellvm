open Printf
open Llvm
open Arg
open Syntax.LLVMsyntax
open Printer

let out_channel = ref stdout

let debug_run f =
  if !Globalstates.debug
  then f ()
  else ()

let debug_print s =
  debug_run (fun _ -> Printf.fprintf !out_channel "DEBUG: %s" s)

let read_im filename =
  let _ = debug_print "read_im.." in

  let _ = debug_print "  context.." in
  let ic = create_context () in

  let _ = debug_print "  imbuf.." in
  let imbuf = MemoryBuffer.of_file filename in

  let _ = debug_print "  im.." in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let _ = debug_run (fun _ -> dump_module im) in

  let _ = debug_print "  slottracker.." in
  let ist = SlotTracker.create_of_module im in
  let _ = debug_run (fun _ -> Llvm_pretty_printer.travel_module ist im) in

  (* let _ = Gc.full_major () in *)

  let _ = debug_print "  coqim.." in
  let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
  let _ = debug_run (fun _ -> Coq_pretty_printer.travel_module coqim) in

  (* TODO: we commented the following out in order to prevent segfaults. *)
  (* let _ = SlotTracker.dispose ist in *)
  (* let _ = dispose_module im in *)
  (* let _ = dispose_context ic in *)

  coqim

let read_hint filename =
  let _ = debug_print "read hint json.." in

  let hint = Ag_util.Json.from_file CoreHint_j.read_hints filename in
  let _ =
    debug_run
      (fun _ ->
        let json = Yojson.Safe.prettify ~std:true (CoreHint_j.string_of_hints hint) in
        let _ = output_string !out_channel json in
        let _ = output_char !out_channel '\n' in
        ())
  in
  hint

let main filename_src filename_tgt filename_hint =
  let coq_im_src = read_im filename_src in
  let coq_im_tgt = read_im filename_tgt in
  let hint = read_hint filename_hint in

  let coq_im_src = ConvertHint.insert_nop coq_im_src (ConvertHint.generate_nop hint) in
  let coq_im_tgt = ConvertHint.insert_nop coq_im_tgt (ConvertHint.generate_nop hint) in
  let coq_hint = ConvertHint.convert coq_im_src coq_im_tgt hint in

  let _ = debug_print "validation.." in
  let validation_result = Validator.valid_module coq_hint coq_im_src coq_im_tgt in
  let _ =
    if validation_result
    then prerr_endline "Validation succeeded."
    else (prerr_endline "Validation failed."; exit 1)
  in

  ()

let argspec = [
  ("-d", Set Globalstates.debug, "debug");
  ("-o", String (fun s -> out_channel := open_out s), "output file");
]

let args = ref []
let argfun f = args := f::!args

let argmsg = "Usage: ./main.native file1.bc file2.bc hint.json"

let () =
  let _ = Arg.parse argspec argfun argmsg in

  match !args with
  | [filename_hint; filename_tgt; filename_src] ->
     main filename_src filename_tgt filename_hint
  | _ ->
     let _ = print_endline "input filenames. ex) ./main.native file1.bc file2.bc hint.json" in
     exit 1
