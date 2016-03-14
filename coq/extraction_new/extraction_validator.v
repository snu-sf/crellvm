Require Import syntax.
Require Import extraction_defs.
Require Import Validator.
Require Import Infrules.
Require Import Hints.
Require Import Exprs.
Require Import Postcond.
Require Import TODO.
Require Import Decs.

Require Import extraction_core.
Require Import extraction_dom.

Require Import ExtrOcamlString.

Extract Constant INTEGER_OPERATION.add => "Coq2ml.llapint_add".
Extract Constant INTEGER_OPERATION.sub => "Coq2ml.llapint_sub".

Extract Constant debug_print_bool => "(fun cl b -> Printer.debug_bool b (TODOCAML.list_to_string cl))".
Extract Constant debug_print_option => "(fun cl o -> Printer.debug_option o (TODOCAML.list_to_string cl))".
Extract Constant debug_print_validation_process => "Printer.debug_print_validation_process".
                                         
Extraction Library FMapWeakList.
Extraction Library extraction_defs.
Extraction Library TODO.
Extraction Library Exprs.
Extraction Library Hints.
Extraction Library Postcond.
Extraction Library Infrules.
Extraction Library Decs.
Extraction Library Validator.
