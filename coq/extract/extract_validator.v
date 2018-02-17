Require Import syntax.
Require Import extract_defs.
Require Import Ords.
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

Extract Constant wrap_compare => "fun f x y ->
  if (x == y)
  then Eq
  else (f x y)
".

Extract Constant OrdIdx.t => "int".
Extract Constant OrdIdx.zero => "0".
Extract Constant OrdIdx.one => "1".
Extract Constant OrdIdx.two => "2".
Extract Constant OrdIdx.three => "3".
Extract Constant OrdIdx.four => "4".
Extract Constant OrdIdx.five => "5".
Extract Constant OrdIdx.six => "6".
Extract Constant OrdIdx.seven => "7".
Extract Constant OrdIdx.eight => "8".
Extract Constant OrdIdx.nine => "9".
Extract Constant OrdIdx.onezero => "10".
Extract Constant OrdIdx.oneone => "11".
Extract Constant OrdIdx.onetwo => "12".
Extract Constant OrdIdx.onethree => "13".
Extract Constant OrdIdx.onefour => "14".
Extract Constant OrdIdx.onefive => "15".
Extract Constant OrdIdx.onesix => "16".
Extract Constant OrdIdx.oneseven => "17".
Extract Constant OrdIdx.oneeight => "18".
Extract Constant OrdIdx.onenine => "19".
Extract Constant OrdIdx.compare => "fun x y ->
    let comp = x - y in
    if(comp < 0) then Lt
    else if (comp > 0) then Gt
    else Eq".

Extract Constant INTEGER_OPERATION.add => "Coq2ml.llapint_add".
Extract Constant INTEGER_OPERATION.sub => "Coq2ml.llapint_sub".

Extract Constant next_nop_id => "fun _ -> ""%""^(string_of_int (Llvm2coq.get_fake_name ()))".
Extract Constant failwith_false => "(fun cl ls -> let _ = Printer.debug_print ((TODOCAML.list_to_string cl)^"" ""^(String.concat "" "" ls)) in false)".
Extract Constant failwith_None => "(fun cl ls -> let _ = Printer.debug_print ((TODOCAML.list_to_string cl)^"" ""^(String.concat "" "" ls)) in None)".
Extract Constant debug_print_validation_process => "Printer.debug_print_validation_process".
Extract Constant debug_print => "fun (printer: 'a -> unit) (x: 'a) -> let _ = printer x in x".
Extract Constant debug_print2 => "fun (printer: 'a -> unit) (content: 'a) (host: 'b) -> let _ = printer content in host".
Extract Constant debug_string => "Printer.debug_string".
Extract Constant cmd_printer => "Printer.cmd_printer".
Extract Constant cmd_pair_printer => "Printer.cmd_pair_printer".
Extract Constant atom_printer => "Printer.atom_printer".
Extract Constant idT_printer => "Printer.idT_printer".
Extract Constant infrule_printer => "Printer.infrule_printer".
Extract Constant assertion_printer => "Printer.PrintHints.assertion".
Extract Constant expr_printer => "Printer.expr_printer".
Extract Constant debug_print_auto => "Printer.debug_print_auto".

Extract Constant gen_infrules_from_insns =>
"InfruleGen.gen_infrules_from_insns".
Extract Constant gen_infrules_next_inv =>
"InfruleGen.gen_infrules_next_inv".

Extract Constant sz.compare => "fun x y ->
    let comp = x - y in
    if(comp < 0) then Lt
    else if (comp > 0) then Gt
    else Eq".
Extract Constant Int.compare =>
"fun x y ->
let res = Llvm.APInt.compare_ord x y in
if res < 0 then Lt else if res > 0 then Gt else Eq".

Extract Constant power_sz => "(fun x ->
  if x = 0 then Coq_xH else Coq_xO (power_sz (x-1)))".
Extract Constant signbit_of => "(fun x ->
  let rec positive_of_int = fun x ->
    if x = 1 then Coq_xH
    else if x mod 2 = 0 then Coq_xO (positive_of_int (x/2))
    else Coq_xI (positive_of_int (x/2))
  in
  let coq_Z_of_int = fun x ->
    if x = 0 then Z0
    else if x > 0 then Zpos (positive_of_int x)
    else Zneg (positive_of_int (-x))
  in
  if x = 0
  then None
  else Some (Camlcoq.z2llapint (coq_Z_of_int x) (Zneg (power_sz (x-1))) true))".


Extraction Library FMapWeakList.
Extraction Library extract_defs.
Extraction Library TODO.
Extraction Library Ords.
Extraction Library Exprs.
Extraction Library Hints.
Extraction Library Postcond.
Extraction Library Infrules.
Extraction Library Decs.
Extraction Library Validator.
Extraction Library Nop.
Extraction Library Debug.
