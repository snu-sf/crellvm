(* open Interpreter *)
open Printf
open Llvm
open Arg

open Yojson.Basic.Util
open Syntax.LLVMsyntax

type rhints_t = {
  rhint_fid: string;
  rhint_mid: string;
  rhint_block_separations: string list;
  rhint_instr_add_removes: rhint_indices_t list;
  rhint_micros: rhint_micro_t list;
}

 and rhint_indices_t = {
   rhint_bb_index: string;
   rhint_indices: int list;
   }

 and rhint_micro_t = {
   rhint_type: rhint_type_t;
   rhint_args: rhint_atom_t list list;
 }
 and rhint_type_t =
   | InstrPropagate
   | Instr2Propagate
   | EqPropagate
   | NeqPropagate
   | StoreEqPropagate
   | AllocaPropagate
   | MaydiffPropagate
   | MaydiffGlobal
   | IsoPropagate1
   | IsoPropagate2

   | AddAssoc
   | ReplaceRhs
   | ReplaceRhsOpt
   | ReplaceLhs
   | RemoveMaydiff
   | EqGenerateSame
   | EqGenerateSameHeap
   | EqGenerateSameHeapValue
   | NeqGenerateGM
   | AddSignbit
   | AddZextBool
   | PtrTrans
   | AddOnebit
   | StashVariable
   | AddShift
   | AddSub
   | AddCommutative
   | SubAdd
   | SubOnebit
   | SubMone
   | SubConstNot
   | AddMulFold
   | AddConstNot
   | AddSelectZero
   | AddSelectZero2
   | SubZextBool
   | SubConstAdd
   | SubRemove
   | SubRemove2
   | SubSdiv
   | SubShl
   | SubMul
   | SubMul2
   | MulMone
   | MulNeg
   | MulBool
   | MulCommutative
   | MulShl
   | DivSubSrem
   | DivSubUrem
   | DivZext
   | DivMone
   | RemZext
   | RemNeg
   | RemNeg2
   | InboundRemove
   | InboundRemove2
   | SelectTrunc
   | SelectAdd
   | SelectConstGt
   | OrXor
   | OrCommutative
   | TruncOnebit
   | CmpOnebit
   | CmpEq
   | CmpUlt
   | ShiftUndef
   | AndSame
   | AndZero
   | AndMone
   | AddMask
   | AndUndef
   | AndNot
   | AndCommutative
   | AndOr
   | AndDemorgan
   | AndNotOr
   | OrUndef
   | OrSame
   | OrZero
   | OrMone
   | OrNot
   | OrAnd
   | XorZero
   | XorSame
   | XorCommutative
   | XorNot
   | ZextTruncAnd
   | ZextTruncAndXor
   | ZextXor
   | SextTrunc
   | TruncTrunc
   | TruncZext1
   | TruncZext2
   | TruncZext3
   | TruncSext1
   | TruncSext2
   | TruncSext3
   | ZextZext
   | SextZext
   | SextSext
   | FptouiFpext
   | FptosiFpext
   | UitofpZext
   | SitofpSext
   | FptruncFptrunc
   | FptruncFpext
   | FpextFpext
   | CmpSwapUlt
   | CmpSwapUgt
   | CmpSwapUle
   | CmpSwapUge
   | CmpSwapSlt
   | CmpSwapSgt
   | CmpSwapSle
   | CmpSwapSge
   | CmpSwapEq
   | CmpSwapNe
   | CmpSltOnebit
   | CmpSgtOnebit
   | CmpUgtOnebit
   | CmpUleOnebit
   | CmpUgeOnebit
   | CmpSleOnebit
   | CmpSgeOnebit
   | CmpEqSub
   | CmpNeSub
   | CmpEqSrem
   | CmpEqSrem2
   | CmpNeSrem
   | CmpNeSrem2
   | CmpEqXor
   | CmpNeXor
(* NOTE: Add here to add a new rule *)

 and rhint_instrtype_t =
   | Phinode
   | Command
   | Terminator

 and rhint_block_pos_t =
   | PhinodePos
   | CommandPos of int
   | TerminatorPos
   | UnspecifiedPos

 and rhint_pos_t = string * rhint_block_pos_t

 and rhint_which_prog_t =
   | Original
   | Optimized
                              
 and rhint_atom_t =
   | AtomVar of rhint_pos_t * rhint_which_prog_t * string * typ
   | AtomFpConst of rhint_pos_t * float * typ
   | AtomIntConst of rhint_pos_t * int * typ
   | AtomPos of rhint_pos_t

exception ParseError of string

let rhint_block_pos_prev pos =
  match pos with
  | CommandPos 0 -> PhinodePos
  | CommandPos i -> CommandPos (i-1)
  | _ -> pos

let rhint_block_pos_next pos =
  match pos with
  | PhinodePos -> CommandPos 0
  | CommandPos i -> CommandPos (i+1)
  | TerminatorPos -> TerminatorPos
  | _ -> failwith "rhint_block_pos_next: no match"

let rhint_block_pos_lt lhs rhs =
  match lhs, rhs with
  | UnspecifiedPos, _ -> false
  | _, UnspecifiedPos -> false

  | PhinodePos, PhinodePos -> false
  | PhinodePos, _ -> true
  | _, PhinodePos -> false

  | CommandPos i, CommandPos j -> i < j
  | CommandPos _, _ -> true
  | _, CommandPos _ -> false

  | TerminatorPos, TerminatorPos -> false

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

let rec string_of_rhints hint =
  "mid: " ^ hint.rhint_mid ^ "\n"
  ^ "fid: " ^ hint.rhint_fid ^ "\n"
  ^ "block_separations: " ^ (string_of_list (fun x -> x) hint.rhint_block_separations) ^ "\n"
  ^ "instr_add_removes: " ^ (string_of_list string_of_indices hint.rhint_instr_add_removes) ^ "\n"
  ^ "micros:\n" ^ (string_of_list_endline string_of_micro hint.rhint_micros)

  and string_of_indices hint =
    let acc =
      ".bid:" ^ (hint.rhint_bb_index)
      ^ ".["
    in
    let acc =
      List.fold_left
        (fun acc i -> acc ^ (string_of_int i) ^ ",")
        acc
        (hint.rhint_indices)
    in
    acc ^ "]"

  and string_of_micro hint =
    "type: " ^ (string_of_rhint_type hint.rhint_type) ^ "\n"
    ^ (string_of_list (string_of_list string_of_rhint_atom) hint.rhint_args)

  and string_of_rhint_type hint =
    match hint with
    | InstrPropagate -> "instr_propagate"
    | Instr2Propagate -> "instr2_propagate"
    | EqPropagate -> "eq_propagate"
    | StoreEqPropagate -> "store_eq_propagate"
    | NeqPropagate -> "neq_propagate"
    | AllocaPropagate -> "alloca_propagate"
    | MaydiffPropagate -> "maydiff_propagate"
    | MaydiffGlobal -> "maydiff_global"
    | IsoPropagate1 -> "iso_propagate1"
    | IsoPropagate2 -> "iso_propagate2"

    | AddAssoc -> "add_assoc"
    | ReplaceRhs -> "replace_rhs"
    | ReplaceRhsOpt -> "replace_rhs_opt"
    | ReplaceLhs -> "replace_lhs"
    | RemoveMaydiff -> "remove_maydiff"
    | EqGenerateSame -> "eq_generate_same"
    | EqGenerateSameHeap -> "eq_generate_same_heap"
    | EqGenerateSameHeapValue -> "eq_generate_same_heap_value"
    | NeqGenerateGM -> "neq_generate_gm"
    | AddSignbit -> "add_signbit"
    | AddZextBool -> "add_zext_bool"
    | PtrTrans -> "ptr_trans"
    | AddOnebit -> "add_onebit"
    | StashVariable -> "stash_variable"
    | AddShift -> "add_shift"
    | AddSub -> "add_sub"
    | AddCommutative -> "add_commutative"
    | SubAdd -> "sub_add"
    | SubOnebit -> "sub_onebit"
    | SubMone -> "sub_mone"
    | SubConstNot -> "sub_const_not"
    | AddMulFold -> "add_mul_fold"
    | AddConstNot -> "add_const_not"
    | AddSelectZero -> "add_select_zero"
    | AddSelectZero2 -> "add_select_zero2"
    | SubZextBool -> "sub_zext_bool"
    | SubConstAdd -> "sub_const_add"
    | SubRemove -> "sub_remove"
    | SubRemove2 -> "sub_remove2"
    | SubSdiv -> "sub_sdiv"
    | SubShl -> "sub_shl"
    | SubMul -> "sub_mul"
    | SubMul2 -> "sub_mul2"
    | MulMone -> "mul_mone"
    | MulNeg -> "mul_neg"
    | MulBool -> "mul_bool"
    | MulCommutative -> "mul_commutative"
    | MulShl -> "mul_shl"
    | DivSubSrem -> "div_sub_srem"
    | DivSubUrem -> "div_sub_urem"
    | DivZext -> "div_zext"
    | DivMone -> "div_mone"
    | RemZext -> "rem_zext"
    | RemNeg -> "rem_neg"
    | RemNeg2 -> "rem_neg2"
    | InboundRemove -> "inbound_remove"
    | InboundRemove2 -> "inbound_remove2"
    | SelectTrunc -> "select_trunc"
    | SelectAdd -> "select_add"
    | SelectConstGt -> "select_const_gt"
    | OrXor -> "or_xor"
    | OrCommutative -> "or_commutative"
    | TruncOnebit -> "trunc_onebit"
    | CmpOnebit -> "cmp_onebit"
    | CmpEq -> "cmp_eq"
    | CmpUlt -> "cmp_ult"
    | ShiftUndef -> "shift_undef"
    | AndSame -> "and_same"
    | AndZero -> "and_zero"
    | AndMone -> "and_mone"
    | AddMask -> "add_mask"
    | AndUndef -> "and_undef"
    | AndNot -> "and_not"
    | AndCommutative -> "and_commutative"
    | AndOr -> "and_or"
    | AndDemorgan -> "and_demorgan"
    | AndNotOr -> "and_not_or"
    | OrUndef -> "or_undef"
    | OrSame -> "or_same"
    | OrZero -> "or_zero"
    | OrMone -> "or_mone"
    | OrNot -> "or_not"
    | OrAnd -> "or_and"
    | XorZero -> "xor_zero"
    | XorSame -> "xor_same"
    | XorCommutative -> "xor_commutative"
    | XorNot -> "xor_not"
    | ZextTruncAnd -> "zext_trunc_and"
    | ZextTruncAndXor -> "zext_trunc_and_xor"
    | ZextXor -> "zext_xor"
    | SextTrunc -> "sext_trunc"
    | TruncTrunc -> "trunc_trunc"
    | TruncZext1 -> "trunc_zext1"
    | TruncZext2 -> "trunc_zext2"
    | TruncZext3 -> "trunc_zext3"
    | TruncSext1 -> "trunc_sext1"
    | TruncSext2 -> "trunc_sext2"
    | TruncSext3 -> "trunc_sext3"
    | ZextZext -> "zext_zext"
    | SextZext -> "sext_zext"
    | SextSext -> "sext_sext"
    | FptouiFpext -> "fptoui_fpext"
    | FptosiFpext -> "fptosi_fpext"
    | UitofpZext -> "uitofp_zext"
    | SitofpSext -> "sitofp_sext"
    | FptruncFptrunc -> "fptrunc_fptrunc"
    | FptruncFpext -> "fptrunc_fpext"
    | FpextFpext -> "fpext_fpext"
    | CmpSwapUlt -> "cmp_swap_ult"
    | CmpSwapUgt -> "cmp_swap_ugt"
    | CmpSwapUle -> "cmp_swap_ule"
    | CmpSwapUge -> "cmp_swap_uge"
    | CmpSwapSlt -> "cmp_swap_slt"
    | CmpSwapSgt -> "cmp_swap_sgt"
    | CmpSwapSle -> "cmp_swap_sle"
    | CmpSwapSge -> "cmp_swap_sge"
    | CmpSwapEq -> "cmp_swap_eq"
    | CmpSwapNe -> "cmp_swap_ne"
    | CmpSltOnebit -> "cmp_slt_onebit"
    | CmpSgtOnebit -> "cmp_sgt_onebit"
    | CmpUgtOnebit -> "cmp_ugt_onebit"
    | CmpUleOnebit -> "cmp_ule_onebit"
    | CmpUgeOnebit -> "cmp_uge_onebit"
    | CmpSleOnebit -> "cmp_sle_onebit"
    | CmpSgeOnebit -> "cmp_sge_onebit"
    | CmpEqSub -> "cmp_eq_sub"
    | CmpNeSub -> "cmp_ne_sub"
    | CmpEqSrem -> "cmp_eq_srem"
    | CmpEqSrem2 -> "cmp_eq_srem2"
    | CmpNeSrem -> "cmp_ne_srem"
    | CmpNeSrem2 -> "cmp_ne_srem2"
    | CmpEqXor -> "cmp_eq_xor"
    | CmpNeXor -> "cmp_ne_xor"
(* NOTE: Add here to add a new rule *)

  and string_of_rhint_which_prog hint =
    match hint with
    | Original -> "orig"
    | Optimized -> "opt"

  and string_of_rhint_atom hint =
    match hint with
    | AtomVar (pos, lr, v, typ) -> v ^ "_" ^ (string_of_rhint_which_prog lr) ^ ":" ^ (Coq_pretty_printer.string_of_typ typ) ^ "@" ^ (string_of_pos pos)
    | AtomFpConst (pos, v, typ) -> (string_of_float v) ^ "@" ^ (string_of_pos pos)
    | AtomIntConst (pos, v, typ) -> (string_of_int v) ^ "@" ^ (string_of_pos pos)
    | AtomPos pos -> string_of_pos pos

  and string_of_pos (bbidx,bpos) =
    match bpos with
    | PhinodePos -> bbidx ^ ".phi"
    | CommandPos i -> bbidx ^ ".cmd." ^ (string_of_int i)
    | TerminatorPos -> bbidx ^ ".term"
    | UnspecifiedPos -> bbidx

let parse_list f json =
  match json |> (to_option to_list) with
  | Some l -> List.map f l
  | _ -> []

let parse_valuetype ?(int_size=32) str =
  if str = "Pointer"
  then Coq_typ_pointer Coq_typ_void

  else if str = "Integer"
  then (Coq_typ_int int_size)

  else if str = "Float"
  then (Coq_typ_floatpoint (Coq_fp_float))

  else if str = "Double"
  then (Coq_typ_floatpoint (Coq_fp_double))

  else if str = "FP128"
  then (Coq_typ_floatpoint (Coq_fp_fp128))

  else if str = "Void"
  then Coq_typ_void

  else if str = "Struct"
  then Coq_typ_struct []

  else if str = "X86_FP80"
  then (Coq_typ_floatpoint Coq_fp_x86_fp80)

  else raise (ParseError "parse_valuetype")

let rec parse_hints json =
  {rhint_mid = json |> member "mid" |> to_string;
   rhint_fid = "@" ^ (json |> member "fid" |> to_string);
   rhint_block_separations = json |> member "block_separations" |> (parse_list to_string);
   rhint_instr_add_removes = json |> member "instr_add_removes" |> (parse_list parse_indices);
   rhint_micros = json |> member "micro_hints" |> (parse_list parse_micro);
  }

  and parse_instrtype json =
    let str = json |> to_string in

    if str = "phinode"
    then Phinode
    else if str = "command"
    then Command
    else if str = "terminator"
    then Terminator

    else failwith ("parse_instr_type: " ^ str)

  and parse_indices json = {
    rhint_bb_index = json |> member "bb_index" |> to_string;
    rhint_indices = json |> member "instr_indices" |> (parse_list parse_index);
  }

  and parse_index json = json |> member "instr_index" |> to_int

  and parse_micro json =
    let result = 
      {rhint_type = json |> member "hint_type" |> parse_type;
       rhint_args = json |> member "hint_args" |> (parse_list (parse_list parse_atom));
      }
    in
    result

  and parse_type json =
    let hint = json |> to_string in
    if hint = "instr_propagate" then InstrPropagate
    else if hint = "instr2_propagate" then Instr2Propagate
    else if hint = "eq_propagate" then EqPropagate
    else if hint = "neq_propagate" then NeqPropagate
    else if hint = "store_eq_propagate" then StoreEqPropagate
    else if hint = "alloca_propagate" then AllocaPropagate
    else if hint = "maydiff_propagate" then MaydiffPropagate
    else if hint = "maydiff_global" then MaydiffGlobal
    else if hint = "iso_propagate1" then IsoPropagate1
    else if hint = "iso_propagate2" then IsoPropagate2

    else if hint = "add_assoc" then AddAssoc
    else if hint = "replace_rhs" then ReplaceRhs
    else if hint = "replace_rhs_opt" then ReplaceRhsOpt
    else if hint = "replace_lhs" then ReplaceLhs
    else if hint = "remove_maydiff" then RemoveMaydiff
    else if hint = "eq_generate_same" then EqGenerateSame
    else if hint = "eq_generate_same_heap" then EqGenerateSameHeap
    else if hint = "eq_generate_same_heap_value" then EqGenerateSameHeapValue
    else if hint = "neq_generate_gm" then NeqGenerateGM
    else if hint = "add_signbit" then AddSignbit
    else if hint = "add_zext_bool" then AddZextBool
    else if hint = "ptr_trans" then PtrTrans
    else if hint = "add_onebit" then AddOnebit
    else if hint = "stash_variable" then StashVariable
    else if hint = "add_shift" then AddShift
    else if hint = "add_sub" then AddSub
    else if hint = "add_commutative" then AddCommutative
    else if hint = "sub_add" then SubAdd
    else if hint = "sub_onebit" then SubOnebit
    else if hint = "sub_mone" then SubMone
    else if hint = "sub_const_not" then SubConstNot
    else if hint = "add_mul_fold" then AddMulFold
    else if hint = "add_const_not" then AddConstNot
    else if hint = "add_select_zero" then AddSelectZero
    else if hint = "add_select_zero2" then AddSelectZero2
    else if hint = "sub_zext_bool" then SubZextBool
    else if hint = "sub_const_add" then SubConstAdd
    else if hint = "sub_remove" then SubRemove
    else if hint = "sub_remove2" then SubRemove2
    else if hint = "sub_sdiv" then SubSdiv
    else if hint = "sub_shl" then SubShl
    else if hint = "sub_mul" then SubMul
    else if hint = "sub_mul2" then SubMul2
    else if hint = "mul_mone" then MulMone
    else if hint = "mul_neg" then MulNeg
    else if hint = "mul_bool" then MulBool
    else if hint = "mul_commutative" then MulCommutative
    else if hint = "mul_shl" then MulShl
    else if hint = "div_sub_srem" then DivSubSrem
    else if hint = "div_sub_urem" then DivSubUrem
    else if hint = "div_zext" then DivZext
    else if hint = "div_mone" then DivMone
    else if hint = "rem_zext" then RemZext
    else if hint = "rem_neg" then RemNeg
    else if hint = "rem_neg2" then RemNeg2
    else if hint = "inbound_remove" then InboundRemove
    else if hint = "inbound_remove2" then InboundRemove2
    else if hint = "select_trunc" then SelectTrunc
    else if hint = "select_add" then SelectAdd
    else if hint = "select_const_gt" then SelectConstGt
    else if hint = "or_xor" then OrXor
    else if hint = "or_commutative" then OrCommutative
    else if hint = "trunc_onebit" then TruncOnebit
    else if hint = "cmp_onebit" then CmpOnebit
    else if hint = "cmp_eq" then CmpEq
    else if hint = "cmp_ult" then CmpUlt
    else if hint = "shift_undef" then ShiftUndef
    else if hint = "and_same" then AndSame
    else if hint = "and_zero" then AndZero
    else if hint = "and_mone" then AndMone
    else if hint = "add_mask" then AddMask
    else if hint = "and_undef" then AndUndef
    else if hint = "and_not" then AndNot
    else if hint = "and_commutative" then AndCommutative
    else if hint = "and_or" then AndOr
    else if hint = "and_demorgan" then AndDemorgan
    else if hint = "and_not_or" then AndNotOr
    else if hint = "or_undef" then OrUndef
    else if hint = "or_same" then OrSame
    else if hint = "or_zero" then OrZero
    else if hint = "or_mone" then OrMone
    else if hint = "or_not" then OrNot
    else if hint = "or_and" then OrAnd
    else if hint = "xor_zero" then XorZero
    else if hint = "xor_same" then XorSame
    else if hint = "xor_commutative" then XorCommutative
    else if hint = "xor_not" then XorNot
    else if hint = "zext_trunc_and" then ZextTruncAnd
    else if hint = "zext_trunc_and_xor" then ZextTruncAndXor
    else if hint = "zext_xor" then ZextXor
    else if hint = "sext_trunc" then SextTrunc
    else if hint = "trunc_trunc" then TruncTrunc
    else if hint = "trunc_zext1" then TruncZext1
    else if hint = "trunc_zext2" then TruncZext2
    else if hint = "trunc_zext3" then TruncZext3
    else if hint = "trunc_sext1" then TruncSext1
    else if hint = "trunc_sext2" then TruncSext2
    else if hint = "trunc_sext3" then TruncSext3
    else if hint = "zext_zext" then ZextZext
    else if hint = "sext_zext" then SextZext
    else if hint = "sext_sext" then SextSext
    else if hint = "fptoui_fpext" then FptouiFpext
    else if hint = "fptosi_fpext" then FptosiFpext
    else if hint = "uitofp_zext" then UitofpZext
    else if hint = "sitofp_sext" then SitofpSext
    else if hint = "fptrunc_fptrunc" then FptruncFptrunc
    else if hint = "fptrunc_fpext" then FptruncFpext
    else if hint = "fpext_fpext" then FpextFpext
    else if hint = "cmp_swap_ult" then CmpSwapUlt
    else if hint = "cmp_swap_ugt" then CmpSwapUgt
    else if hint = "cmp_swap_ule" then CmpSwapUle
    else if hint = "cmp_swap_uge" then CmpSwapUge
    else if hint = "cmp_swap_slt" then CmpSwapSlt
    else if hint = "cmp_swap_sgt" then CmpSwapSgt
    else if hint = "cmp_swap_sle" then CmpSwapSle
    else if hint = "cmp_swap_sge" then CmpSwapSge
    else if hint = "cmp_swap_eq" then CmpSwapEq
    else if hint = "cmp_swap_ne" then CmpSwapNe
    else if hint = "cmp_slt_onebit" then CmpSltOnebit
    else if hint = "cmp_sgt_onebit" then CmpSgtOnebit
    else if hint = "cmp_ugt_onebit" then CmpUgtOnebit
    else if hint = "cmp_ule_onebit" then CmpUleOnebit
    else if hint = "cmp_uge_onebit" then CmpUgeOnebit
    else if hint = "cmp_sle_onebit" then CmpSleOnebit
    else if hint = "cmp_sge_onebit" then CmpSgeOnebit
    else if hint = "cmp_eq_sub" then CmpEqSub
    else if hint = "cmp_ne_sub" then CmpNeSub
    else if hint = "cmp_eq_srem" then CmpEqSrem
    else if hint = "cmp_eq_srem2" then CmpEqSrem2
    else if hint = "cmp_ne_srem" then CmpNeSrem
    else if hint = "cmp_ne_srem2" then CmpNeSrem2
    else if hint = "cmp_eq_xor" then CmpEqXor
    else if hint = "cmp_ne_xor" then CmpNeXor
(* NOTE: Add here to add a new rule *)

    else raise (ParseError ("parse_type: " ^ hint))
               
  and parse_atom json =
    let str = json |> member "atom_type" |> to_string in

    if str = "variable"
    then AtomVar (json |> parse_pos,
                  json |> member "atom_value" |> parse_variable_pos,
                  json |> member "atom_value" |> parse_variable,
                  json |> member "atom_valuetype" |> to_string |> parse_valuetype)

    else if str = "fp_constant"
    then AtomFpConst (json |> parse_pos,
                      json |> member "atom_value" |> to_float,
                      json |> member "atom_valuetype" |> to_string |> parse_valuetype)

    else if str = "int_constant"
    then AtomIntConst (json |> parse_pos,
                      json |> member "atom_value" |> to_int,
                       let width = json |> member "atom_intwidth" |> to_int in
                       let valuetype = json |> member "atom_valuetype" |> to_string in
                       parse_valuetype ~int_size:width valuetype)

    else if str = "index_instr_block"
    then AtomPos (json |> parse_pos)

    else if str = "index_block"
    then AtomPos (parse_blockid json, UnspecifiedPos)

    else raise (ParseError ("parse_atom: " ^ (Yojson.Basic.to_string json)))

  and parse_pos json =
    (json |> parse_blockid,
     let instrtype = json |> member "atom_instrtype" |> to_string in

     if instrtype = "phinode"
     then PhinodePos

     else if instrtype = "command"
     then CommandPos (json |> member "atom_instrindex" |> to_int)

     else if instrtype = "none"
     then UnspecifiedPos

     else if instrtype = "terminator"
     then TerminatorPos

     else failwith "parse_pos")

  and parse_blockid json =
    (json |> member "atom_bbindex" |> to_string)

  and parse_variable json =
    json |> member "var_value" |> to_string

  and parse_variable_pos json =
    let hint = json |> member "var_pos" |> to_string in
    if hint = "left" then Original
    else if hint = "right" then Optimized
    else failwith "parse_variable_pos"
