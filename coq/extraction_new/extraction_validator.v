Require Import syntax.
Require Import extraction_defs.
Require Import Validator.
Require Import Infrules.
Require Import Hints.
Require Import Exprs.
Require Import Postcond.
Require Import TODO.
Require Import Decs.
Require Import Nop.
Require Import Debug.

Require Import extraction_core.
Require Import extraction_dom.

Require Import ExtrOcamlString.

Extract Constant INTEGER_OPERATION.add => "Coq2ml.llapint_add".
Extract Constant INTEGER_OPERATION.sub => "Coq2ml.llapint_sub".

Extract Constant next_nop_id => "fun _ -> ""%""^(string_of_int (Llvm2coq.get_fake_name ()))".
Extract Constant failwith_false => "(fun cl ls -> let _ = Printer.debug_print ((TODOCAML.list_to_string cl)^"" ""^(String.concat "" "" ls)) in false)".
Extract Constant failwith_None => "(fun cl ls -> let _ = Printer.debug_print ((TODOCAML.list_to_string cl)^"" ""^(String.concat "" "" ls)) in None)".
Extract Constant debug_print_validation_process => "Printer.debug_print_validation_process".
Extract Constant debug_print => "fun (printer: 'a -> unit) (x: 'a) -> let _ = printer x in x".
Extract Constant debug_string => "Printer.debug_string".
Extract Constant cmd_printer => "Printer.cmd_printer".
Extract Constant atom_printer => "Printer.atom_printer".
Extract Constant idT_printer => "Printer.idT_printer".

Extraction Library FMapWeakList.
Extraction Library extraction_defs.
Extraction Library TODO.
Extraction Library Exprs.
Extraction Library Hints.
Extraction Library Postcond.
Extraction Library Infrules.
Extraction Library Decs.
Extraction Library Validator.
Extraction Library Nop.
Extraction Library Debug.