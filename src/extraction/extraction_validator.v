Require Import vellvm.
Require Import extraction_defs.
Require Import validator.
Require Import infrules.

Require Import extraction_core.
Require Import extraction_dom.
Require Import syntax_ext.
Require Import basic_aux.
Require Import vars_aux.
Require Import validator_aux.

Extract Constant INTEGER_OPERATION.add => "Coq2ml.llapint_add".
Extract Constant INTEGER_OPERATION.sub => "Coq2ml.llapint_sub".

Extract Constant my_nat => "int".
Extract Constant my_O => "0".
Extract Constant my_S => "(fun x -> x + 1)".
Extract Constant my_beq_nat => "( = )".
Extract Constant my_pred => "(fun x -> if x <= 0 then 0 else x-1)".

Extract Constant power_sz => "(fun x ->
  if x = 0 then Coq_xH else Coq_xO (power_sz (x-1)))".
Extract Constant signbit_of => "(fun x ->
  let rec positive_of_int = fun x ->
    if x = 1 then Coq_xH
    else if x mod 2 = 0 then Coq_xO (positive_of_int (x/2))
    else Coq_xI (positive_of_int (x/2))
  in
  let coq_Z_of_int = fun x ->
    if x = 0 then BinInt.Z0 
    else if x > 0 then BinInt.Zpos (positive_of_int x)
    else BinInt.Zneg (positive_of_int (-x))
  in
  if x = 0
  then None
  else Some (Camlcoq.z2llapint (coq_Z_of_int x) (BinInt.Zneg (power_sz (x-1))) true))".

Extract Constant my_Zsucc => "(fun x -> Llvm.APInt.inc x)".

Extract Constant is_even => "(fun x -> not (Llvm.APInt.array_index x 0 ))".

Extract Constant float_zero_rhs => "(fun coq_fp ->
let llc = Llvm.create_context () in
let fp =
match coq_fp with
| LLVMsyntax.Coq_fp_float -> Llvm.float_type llc
| LLVMsyntax.Coq_fp_double -> Llvm.double_type llc
| LLVMsyntax.Coq_fp_fp128 -> Llvm.fp128_type llc
| LLVMsyntax.Coq_fp_x86_fp80 -> Llvm.x86fp80_type llc
| LLVMsyntax.Coq_fp_ppc_fp128 -> Llvm.ppc_fp128_type llc
in
Coq_rhs_ext_value (Coq_value_ext_const (LLVMsyntax.Coq_const_floatpoint (coq_fp, (Llvm.APFloat.const_float_get_value (Llvm.const_float fp (Floats.Float.floatofint (Int.one (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))) 
)".

Extraction Library FMapWeakList.
Extraction Library extraction_defs.
Extraction Library decs.
Extraction Library syntax_ext.
Extraction Library hints.
Extraction Library basic_aux.
Extraction Library vars_aux.
Extraction Library infrules.
Extraction Library my_gvar_dec.
Extraction Library validator_aux.
Extraction Library validator.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
