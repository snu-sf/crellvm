(* Auto-generated from "coreHint.atd" *)


type age =  Old | New 

type variable = { name: string; age: age }

type int_type =  IntType of (bool * int) 

type int_value = { myvalue: int; mytype: int_type }

type float_type =  FloatType | DoubleType | FP128Type | X86_FP80Type 

type float_value = { myvalue: float; mytype: float_type }

type const_value =  IntVal of int_value | FloatVal of float_value 

type value =  VarValue of variable | ConstValue of const_value 

type scope =  Source | Target 

type instr_type =  Command of int | Phinode | Terminator 

type position = { block_index: string; instr_type: instr_type }

type remove_maydiff = { position: position; variable: variable }

type propagate_instr = { lhs: variable; rhs: position }

type propagate_eq = { lhs: value; rhs: value }

type propagate_object =  Instr of propagate_instr | Eq of propagate_eq 

type propagate = {
  propagate: propagate_object;
  propagate_from: position;
  propagate_to: position;
  scope: scope
}

type infrule_base = { position: position }

type add_assoc = { position: position; lhs: variable; rhs: variable }

type command = 
    Propagate of propagate
  | AddAssoc of add_assoc
  | RemoveMaydiff of remove_maydiff


type hints = {
  module_id: string;
  function_id: string;
  opt_name: string;
  commands: command list
}
