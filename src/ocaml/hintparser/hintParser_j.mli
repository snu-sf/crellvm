(* Auto-generated from "hintParser.atd" *)


type age = HintParser_t.age =  Old | New 

type variable = HintParser_t.variable = { name: string; age: age }

type int_type = HintParser_t.int_type =  IntType of (bool * int) 

type int_value = HintParser_t.int_value = { myvalue: int; mytype: int_type }

type float_type = HintParser_t.float_type = 
    FloatType | DoubleType | FP128Type | X86_FP80Type


type float_value = HintParser_t.float_value = {
  myvalue: float;
  mytype: float_type
}

type const_value = HintParser_t.const_value = 
    IntVal of int_value
  | FloatVal of float_value


type value = HintParser_t.value = 
    VarValue of variable
  | ConstValue of const_value


type scope = HintParser_t.scope =  Source | Target 

type instr_type = HintParser_t.instr_type = 
    Command of int
  | Phinode
  | Terminator


type position = HintParser_t.position = {
  block_index: string;
  instr_type: instr_type
}

type remove_maydiff = HintParser_t.remove_maydiff = {
  position: position;
  variable: variable
}

type propagate_instr = HintParser_t.propagate_instr = {
  lhs: variable;
  rhs: position
}

type propagate_eq = HintParser_t.propagate_eq = { lhs: value; rhs: value }

type propagate_object = HintParser_t.propagate_object = 
    Instr of propagate_instr
  | Eq of propagate_eq


type propagate = HintParser_t.propagate = {
  propagate: propagate_object;
  propagate_from: position;
  propagate_to: position;
  scope: scope
}

type infrule_base = HintParser_t.infrule_base = { position: position }

type add_assoc = HintParser_t.add_assoc = {
  position: position;
  lhs: variable;
  rhs: variable
}

type command = HintParser_t.command = 
    Propagate of propagate
  | AddAssoc of add_assoc
  | RemoveMaydiff of remove_maydiff


type hints = HintParser_t.hints = {
  module_id: string;
  function_id: string;
  opt_name: string;
  commands: command list
}

val write_age :
  Bi_outbuf.t -> age -> unit
  (** Output a JSON value of type {!age}. *)

val string_of_age :
  ?len:int -> age -> string
  (** Serialize a value of type {!age}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_age :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> age
  (** Input JSON data of type {!age}. *)

val age_of_string :
  string -> age
  (** Deserialize JSON data of type {!age}. *)

val write_variable :
  Bi_outbuf.t -> variable -> unit
  (** Output a JSON value of type {!variable}. *)

val string_of_variable :
  ?len:int -> variable -> string
  (** Serialize a value of type {!variable}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_variable :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> variable
  (** Input JSON data of type {!variable}. *)

val variable_of_string :
  string -> variable
  (** Deserialize JSON data of type {!variable}. *)

val write_int_type :
  Bi_outbuf.t -> int_type -> unit
  (** Output a JSON value of type {!int_type}. *)

val string_of_int_type :
  ?len:int -> int_type -> string
  (** Serialize a value of type {!int_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_int_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> int_type
  (** Input JSON data of type {!int_type}. *)

val int_type_of_string :
  string -> int_type
  (** Deserialize JSON data of type {!int_type}. *)

val write_int_value :
  Bi_outbuf.t -> int_value -> unit
  (** Output a JSON value of type {!int_value}. *)

val string_of_int_value :
  ?len:int -> int_value -> string
  (** Serialize a value of type {!int_value}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_int_value :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> int_value
  (** Input JSON data of type {!int_value}. *)

val int_value_of_string :
  string -> int_value
  (** Deserialize JSON data of type {!int_value}. *)

val write_float_type :
  Bi_outbuf.t -> float_type -> unit
  (** Output a JSON value of type {!float_type}. *)

val string_of_float_type :
  ?len:int -> float_type -> string
  (** Serialize a value of type {!float_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_float_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> float_type
  (** Input JSON data of type {!float_type}. *)

val float_type_of_string :
  string -> float_type
  (** Deserialize JSON data of type {!float_type}. *)

val write_float_value :
  Bi_outbuf.t -> float_value -> unit
  (** Output a JSON value of type {!float_value}. *)

val string_of_float_value :
  ?len:int -> float_value -> string
  (** Serialize a value of type {!float_value}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_float_value :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> float_value
  (** Input JSON data of type {!float_value}. *)

val float_value_of_string :
  string -> float_value
  (** Deserialize JSON data of type {!float_value}. *)

val write_const_value :
  Bi_outbuf.t -> const_value -> unit
  (** Output a JSON value of type {!const_value}. *)

val string_of_const_value :
  ?len:int -> const_value -> string
  (** Serialize a value of type {!const_value}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_const_value :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> const_value
  (** Input JSON data of type {!const_value}. *)

val const_value_of_string :
  string -> const_value
  (** Deserialize JSON data of type {!const_value}. *)

val write_value :
  Bi_outbuf.t -> value -> unit
  (** Output a JSON value of type {!value}. *)

val string_of_value :
  ?len:int -> value -> string
  (** Serialize a value of type {!value}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_value :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> value
  (** Input JSON data of type {!value}. *)

val value_of_string :
  string -> value
  (** Deserialize JSON data of type {!value}. *)

val write_scope :
  Bi_outbuf.t -> scope -> unit
  (** Output a JSON value of type {!scope}. *)

val string_of_scope :
  ?len:int -> scope -> string
  (** Serialize a value of type {!scope}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_scope :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> scope
  (** Input JSON data of type {!scope}. *)

val scope_of_string :
  string -> scope
  (** Deserialize JSON data of type {!scope}. *)

val write_instr_type :
  Bi_outbuf.t -> instr_type -> unit
  (** Output a JSON value of type {!instr_type}. *)

val string_of_instr_type :
  ?len:int -> instr_type -> string
  (** Serialize a value of type {!instr_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_instr_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> instr_type
  (** Input JSON data of type {!instr_type}. *)

val instr_type_of_string :
  string -> instr_type
  (** Deserialize JSON data of type {!instr_type}. *)

val write_position :
  Bi_outbuf.t -> position -> unit
  (** Output a JSON value of type {!position}. *)

val string_of_position :
  ?len:int -> position -> string
  (** Serialize a value of type {!position}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_position :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> position
  (** Input JSON data of type {!position}. *)

val position_of_string :
  string -> position
  (** Deserialize JSON data of type {!position}. *)

val write_remove_maydiff :
  Bi_outbuf.t -> remove_maydiff -> unit
  (** Output a JSON value of type {!remove_maydiff}. *)

val string_of_remove_maydiff :
  ?len:int -> remove_maydiff -> string
  (** Serialize a value of type {!remove_maydiff}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_remove_maydiff :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> remove_maydiff
  (** Input JSON data of type {!remove_maydiff}. *)

val remove_maydiff_of_string :
  string -> remove_maydiff
  (** Deserialize JSON data of type {!remove_maydiff}. *)

val write_propagate_instr :
  Bi_outbuf.t -> propagate_instr -> unit
  (** Output a JSON value of type {!propagate_instr}. *)

val string_of_propagate_instr :
  ?len:int -> propagate_instr -> string
  (** Serialize a value of type {!propagate_instr}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_propagate_instr :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> propagate_instr
  (** Input JSON data of type {!propagate_instr}. *)

val propagate_instr_of_string :
  string -> propagate_instr
  (** Deserialize JSON data of type {!propagate_instr}. *)

val write_propagate_eq :
  Bi_outbuf.t -> propagate_eq -> unit
  (** Output a JSON value of type {!propagate_eq}. *)

val string_of_propagate_eq :
  ?len:int -> propagate_eq -> string
  (** Serialize a value of type {!propagate_eq}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_propagate_eq :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> propagate_eq
  (** Input JSON data of type {!propagate_eq}. *)

val propagate_eq_of_string :
  string -> propagate_eq
  (** Deserialize JSON data of type {!propagate_eq}. *)

val write_propagate_object :
  Bi_outbuf.t -> propagate_object -> unit
  (** Output a JSON value of type {!propagate_object}. *)

val string_of_propagate_object :
  ?len:int -> propagate_object -> string
  (** Serialize a value of type {!propagate_object}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_propagate_object :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> propagate_object
  (** Input JSON data of type {!propagate_object}. *)

val propagate_object_of_string :
  string -> propagate_object
  (** Deserialize JSON data of type {!propagate_object}. *)

val write_propagate :
  Bi_outbuf.t -> propagate -> unit
  (** Output a JSON value of type {!propagate}. *)

val string_of_propagate :
  ?len:int -> propagate -> string
  (** Serialize a value of type {!propagate}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_propagate :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> propagate
  (** Input JSON data of type {!propagate}. *)

val propagate_of_string :
  string -> propagate
  (** Deserialize JSON data of type {!propagate}. *)

val write_infrule_base :
  Bi_outbuf.t -> infrule_base -> unit
  (** Output a JSON value of type {!infrule_base}. *)

val string_of_infrule_base :
  ?len:int -> infrule_base -> string
  (** Serialize a value of type {!infrule_base}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_infrule_base :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> infrule_base
  (** Input JSON data of type {!infrule_base}. *)

val infrule_base_of_string :
  string -> infrule_base
  (** Deserialize JSON data of type {!infrule_base}. *)

val write_add_assoc :
  Bi_outbuf.t -> add_assoc -> unit
  (** Output a JSON value of type {!add_assoc}. *)

val string_of_add_assoc :
  ?len:int -> add_assoc -> string
  (** Serialize a value of type {!add_assoc}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_add_assoc :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> add_assoc
  (** Input JSON data of type {!add_assoc}. *)

val add_assoc_of_string :
  string -> add_assoc
  (** Deserialize JSON data of type {!add_assoc}. *)

val write_command :
  Bi_outbuf.t -> command -> unit
  (** Output a JSON value of type {!command}. *)

val string_of_command :
  ?len:int -> command -> string
  (** Serialize a value of type {!command}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_command :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> command
  (** Input JSON data of type {!command}. *)

val command_of_string :
  string -> command
  (** Deserialize JSON data of type {!command}. *)

val write_hints :
  Bi_outbuf.t -> hints -> unit
  (** Output a JSON value of type {!hints}. *)

val string_of_hints :
  ?len:int -> hints -> string
  (** Serialize a value of type {!hints}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_hints :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> hints
  (** Input JSON data of type {!hints}. *)

val hints_of_string :
  string -> hints
  (** Deserialize JSON data of type {!hints}. *)

