open Printf
open Llvm
open Arg
open Syntax.LLVMsyntax
open Printer
open CoreHint_j

let measure_time = ref false

let prev_time = ref 0.0

let print_time msg =
  if !measure_time
  then
    let cur_time = Sys.time() in
    Printf.fprintf stderr
                   "MEASURE_TIME\t%s\t%s\t%s\n"
                   (string_of_float (cur_time -. !prev_time))
                   (string_of_float cur_time)
                   msg;
    prev_time := cur_time
  else ()

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

  let hint = Ag_util.Json.from_file read_hints filename in
  let _ =
    debug_run
      (fun _ ->
        let json = Yojson.Safe.prettify ~std:true (string_of_hints hint) in
        let _ = output_string !out_channel json in
        let _ = output_char !out_channel '\n' in
        ())
  in
  hint

let get_last_sentence s =
  if String.contains s '\n' then
    let i = String.rindex s '\n' in
    String.sub s (i+1) (String.length s - i - 1)
  else s

let main filename_src filename_tgt filename_hint =
  let _ = print_time "start" in
  let coq_im_src = read_im filename_src in
  let coq_im_tgt = read_im filename_tgt in
  let hint = read_hint filename_hint in

  let _ = print_time "read-done" in

  let _ = debug_print "description for this VU.." in
  let _ = debug_print hint.CoreHint_t.description in
  let _ =
    match hint.CoreHint_t.return_code with
    | ADMITTED -> print_endline "Set to admitted."; print_endline (get_last_sentence hint.CoreHint_t.description)
    | FAIL -> print_endline "Set to fail."
    | ACTUAL ->
       let (src_nop_positions, tgt_nop_positions) =
         List.partition
           (fun (nop:CoreHint_t.position) -> nop.CoreHint_t.scope = CoreHint_t.Source)
           hint.CoreHint_t.nop_positions in

       let coq_im_src = ConvertHint.insert_nop hint.function_id
                                               coq_im_src src_nop_positions in
       let coq_im_tgt = ConvertHint.insert_nop hint.function_id
                                               coq_im_tgt tgt_nop_positions in

       let _ = print_time "insert-nop-done" in

       let coq_hint = ConvertHint.convert coq_im_src coq_im_tgt hint in

       let _ = print_time "convert-hint-done" in

       let _ = debug_print "validation.." in
       let validation_result =
         Validator.valid_module coq_hint coq_im_src coq_im_tgt in
       let _ = print_time "validation-done" in
       match validation_result with
       | Some true -> print_endline "Validation succeeded."
       | Some false -> print_endline "Set to admitted."; print_endline "Named-types differ."
       | None -> (print_endline "Validation failed."; exit 1)
  in

  ()

let argspec = [
  ("-d", Set Globalstates.debug, "debug");
  ("-o", String (fun s -> out_channel := open_out s), "output file");
  ("-t", Set measure_time, "time");
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
