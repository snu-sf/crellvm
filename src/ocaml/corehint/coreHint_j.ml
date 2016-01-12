(* Auto-generated from "coreHint.atd" *)


type age = CoreHint_t.age =  Old | New 

type variable = CoreHint_t.variable = { name: string; age: age }

type int_type = CoreHint_t.int_type =  IntType of (bool * int) 

type int_value = CoreHint_t.int_value = { myvalue: int; mytype: int_type }

type float_type = CoreHint_t.float_type = 
    FloatType | DoubleType | FP128Type | X86_FP80Type


type float_value = CoreHint_t.float_value = {
  myvalue: float;
  mytype: float_type
}

type const_value = CoreHint_t.const_value = 
    IntVal of int_value
  | FloatVal of float_value


type value = CoreHint_t.value = 
    VarValue of variable
  | ConstValue of const_value


type scope = CoreHint_t.scope =  Source | Target 

type instr_type = CoreHint_t.instr_type = 
    Command of int
  | Phinode
  | Terminator


type position = CoreHint_t.position = {
  block_index: string;
  instr_type: instr_type
}

type remove_maydiff = CoreHint_t.remove_maydiff = {
  position: position;
  variable: variable
}

type propagate_instr = CoreHint_t.propagate_instr = {
  lhs: variable;
  rhs: position
}

type propagate_eq = CoreHint_t.propagate_eq = { lhs: value; rhs: value }

type propagate_object = CoreHint_t.propagate_object = 
    Instr of propagate_instr
  | Eq of propagate_eq


type propagate = CoreHint_t.propagate = {
  propagate: propagate_object;
  propagate_from: position;
  propagate_to: position;
  scope: scope
}

type infrule_base = CoreHint_t.infrule_base = { position: position }

type add_assoc = CoreHint_t.add_assoc = {
  position: position;
  lhs: variable;
  rhs: variable
}

type command = CoreHint_t.command = 
    Propagate of propagate
  | AddAssoc of add_assoc
  | RemoveMaydiff of remove_maydiff


type hints = CoreHint_t.hints = {
  module_id: string;
  function_id: string;
  opt_name: string;
  commands: command list
}

let write_age : _ -> age -> _ = (
  fun ob sum ->
    match sum with
      | Old -> Bi_outbuf.add_string ob "<\"Old\">"
      | New -> Bi_outbuf.add_string ob "<\"New\">"
)
let string_of_age ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_age ob x;
  Bi_outbuf.contents ob
let read_age = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 3 then (
                  match String.unsafe_get s pos with
                    | 'N' -> (
                        if String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'w' then (
                          1
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | 'O' -> (
                        if String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'd' then (
                          0
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | _ -> (
                        raise (Exit)
                      )
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Old : age)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (New : age)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 3 then (
                  match String.unsafe_get s pos with
                    | 'N' -> (
                        if String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'w' then (
                          1
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | 'O' -> (
                        if String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'd' then (
                          0
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | _ -> (
                        raise (Exit)
                      )
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | 0 ->
              (Old : age)
            | 1 ->
              (New : age)
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
)
let age_of_string s =
  read_age (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_variable : _ -> variable -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"name\":";
    (
      Yojson.Safe.write_string
    )
      ob x.name;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"age\":";
    (
      write_age
    )
      ob x.age;
    Bi_outbuf.add_char ob '}';
)
let string_of_variable ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_variable ob x;
  Bi_outbuf.contents ob
let read_variable = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_name = ref (Obj.magic 0.0) in
    let field_age = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 3 -> (
                if String.unsafe_get s pos = 'a' && String.unsafe_get s (pos+1) = 'g' && String.unsafe_get s (pos+2) = 'e' then (
                  1
                )
                else (
                  -1
                )
              )
            | 4 -> (
                if String.unsafe_get s pos = 'n' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'e' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_name := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_age := (
              (
                read_age
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 3 -> (
                  if String.unsafe_get s pos = 'a' && String.unsafe_get s (pos+1) = 'g' && String.unsafe_get s (pos+2) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 4 -> (
                  if String.unsafe_get s pos = 'n' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'e' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_name := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_age := (
                (
                  read_age
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "name"; "age" |];
        (
          {
            name = !field_name;
            age = !field_age;
          }
         : variable)
      )
)
let variable_of_string s =
  read_variable (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_int_type : _ -> int_type -> _ = (
  fun ob sum ->
    match sum with
      | IntType x ->
        Bi_outbuf.add_string ob "<\"IntType\":";
        (
          fun ob x ->
            Bi_outbuf.add_char ob '(';
            (let x, _ = x in
            (
              Yojson.Safe.write_bool
            ) ob x
            );
            Bi_outbuf.add_char ob ',';
            (let _, x = x in
            (
              Yojson.Safe.write_int
            ) ob x
            );
            Bi_outbuf.add_char ob ')';
        ) ob x;
        Bi_outbuf.add_char ob '>'
)
let string_of_int_type ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_int_type ob x;
  Bi_outbuf.contents ob
let read_int_type = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 7 && String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'T' && String.unsafe_get s (pos+4) = 'y' && String.unsafe_get s (pos+5) = 'p' && String.unsafe_get s (pos+6) = 'e' then (
                  0
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  fun p lb ->
                    Yojson.Safe.read_space p lb;
                    let std_tuple = Yojson.Safe.start_any_tuple p lb in
                    let len = ref 0 in
                    let end_of_tuple = ref false in
                    (try
                      let x0 =
                        let x =
                          (
                            Ag_oj_run.read_bool
                          ) p lb
                        in
                        incr len;
                        Yojson.Safe.read_space p lb;
                        Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                        x
                      in
                      let x1 =
                        let x =
                          (
                            Ag_oj_run.read_int
                          ) p lb
                        in
                        incr len;
                        (try
                          Yojson.Safe.read_space p lb;
                          Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                        with Yojson.End_of_tuple -> end_of_tuple := true);
                        x
                      in
                      if not !end_of_tuple then (
                        try
                          while true do
                            Yojson.Safe.skip_json p lb;
                            Yojson.Safe.read_space p lb;
                            Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                          done
                        with Yojson.End_of_tuple -> ()
                      );
                      (x0, x1)
                    with Yojson.End_of_tuple ->
                      Ag_oj_run.missing_tuple_fields p !len [ 0; 1 ]);
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (IntType x : int_type)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 7 && String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'T' && String.unsafe_get s (pos+4) = 'y' && String.unsafe_get s (pos+5) = 'p' && String.unsafe_get s (pos+6) = 'e' then (
                  0
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  fun p lb ->
                    Yojson.Safe.read_space p lb;
                    let std_tuple = Yojson.Safe.start_any_tuple p lb in
                    let len = ref 0 in
                    let end_of_tuple = ref false in
                    (try
                      let x0 =
                        let x =
                          (
                            Ag_oj_run.read_bool
                          ) p lb
                        in
                        incr len;
                        Yojson.Safe.read_space p lb;
                        Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                        x
                      in
                      let x1 =
                        let x =
                          (
                            Ag_oj_run.read_int
                          ) p lb
                        in
                        incr len;
                        (try
                          Yojson.Safe.read_space p lb;
                          Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                        with Yojson.End_of_tuple -> end_of_tuple := true);
                        x
                      in
                      if not !end_of_tuple then (
                        try
                          while true do
                            Yojson.Safe.skip_json p lb;
                            Yojson.Safe.read_space p lb;
                            Yojson.Safe.read_tuple_sep2 p std_tuple lb;
                          done
                        with Yojson.End_of_tuple -> ()
                      );
                      (x0, x1)
                    with Yojson.End_of_tuple ->
                      Ag_oj_run.missing_tuple_fields p !len [ 0; 1 ]);
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (IntType x : int_type)
            | _ -> (
                assert false
              )
        )
)
let int_type_of_string s =
  read_int_type (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_int_value : _ -> int_value -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"myvalue\":";
    (
      Yojson.Safe.write_int
    )
      ob x.myvalue;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"mytype\":";
    (
      write_int_type
    )
      ob x.mytype;
    Bi_outbuf.add_char ob '}';
)
let string_of_int_value ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_int_value ob x;
  Bi_outbuf.contents ob
let read_int_value = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_myvalue = ref (Obj.magic 0.0) in
    let field_mytype = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 6 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'y' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' then (
                  1
                )
                else (
                  -1
                )
              )
            | 7 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 'v' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'u' && String.unsafe_get s (pos+6) = 'e' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_myvalue := (
              (
                Ag_oj_run.read_int
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_mytype := (
              (
                read_int_type
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 6 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'y' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 7 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 'v' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'u' && String.unsafe_get s (pos+6) = 'e' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_myvalue := (
                (
                  Ag_oj_run.read_int
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_mytype := (
                (
                  read_int_type
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "myvalue"; "mytype" |];
        (
          {
            myvalue = !field_myvalue;
            mytype = !field_mytype;
          }
         : int_value)
      )
)
let int_value_of_string s =
  read_int_value (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_float_type : _ -> float_type -> _ = (
  fun ob sum ->
    match sum with
      | FloatType -> Bi_outbuf.add_string ob "<\"FloatType\">"
      | DoubleType -> Bi_outbuf.add_string ob "<\"DoubleType\">"
      | FP128Type -> Bi_outbuf.add_string ob "<\"FP128Type\">"
      | X86_FP80Type -> Bi_outbuf.add_string ob "<\"X86_FP80Type\">"
)
let string_of_float_type ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_float_type ob x;
  Bi_outbuf.contents ob
let read_float_type = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 9 -> (
                      if String.unsafe_get s pos = 'F' then (
                        match String.unsafe_get s (pos+1) with
                          | 'P' -> (
                              if String.unsafe_get s (pos+2) = '1' && String.unsafe_get s (pos+3) = '2' && String.unsafe_get s (pos+4) = '8' && String.unsafe_get s (pos+5) = 'T' && String.unsafe_get s (pos+6) = 'y' && String.unsafe_get s (pos+7) = 'p' && String.unsafe_get s (pos+8) = 'e' then (
                                2
                              )
                              else (
                                raise (Exit)
                              )
                            )
                          | 'l' -> (
                              if String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'T' && String.unsafe_get s (pos+6) = 'y' && String.unsafe_get s (pos+7) = 'p' && String.unsafe_get s (pos+8) = 'e' then (
                                0
                              )
                              else (
                                raise (Exit)
                              )
                            )
                          | _ -> (
                              raise (Exit)
                            )
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'D' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'b' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'T' && String.unsafe_get s (pos+7) = 'y' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'e' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 12 -> (
                      if String.unsafe_get s pos = 'X' && String.unsafe_get s (pos+1) = '8' && String.unsafe_get s (pos+2) = '6' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = 'F' && String.unsafe_get s (pos+5) = 'P' && String.unsafe_get s (pos+6) = '8' && String.unsafe_get s (pos+7) = '0' && String.unsafe_get s (pos+8) = 'T' && String.unsafe_get s (pos+9) = 'y' && String.unsafe_get s (pos+10) = 'p' && String.unsafe_get s (pos+11) = 'e' then (
                        3
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (FloatType : float_type)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (DoubleType : float_type)
            | 2 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (FP128Type : float_type)
            | 3 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (X86_FP80Type : float_type)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 9 -> (
                      if String.unsafe_get s pos = 'F' then (
                        match String.unsafe_get s (pos+1) with
                          | 'P' -> (
                              if String.unsafe_get s (pos+2) = '1' && String.unsafe_get s (pos+3) = '2' && String.unsafe_get s (pos+4) = '8' && String.unsafe_get s (pos+5) = 'T' && String.unsafe_get s (pos+6) = 'y' && String.unsafe_get s (pos+7) = 'p' && String.unsafe_get s (pos+8) = 'e' then (
                                2
                              )
                              else (
                                raise (Exit)
                              )
                            )
                          | 'l' -> (
                              if String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'T' && String.unsafe_get s (pos+6) = 'y' && String.unsafe_get s (pos+7) = 'p' && String.unsafe_get s (pos+8) = 'e' then (
                                0
                              )
                              else (
                                raise (Exit)
                              )
                            )
                          | _ -> (
                              raise (Exit)
                            )
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'D' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'b' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'T' && String.unsafe_get s (pos+7) = 'y' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'e' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 12 -> (
                      if String.unsafe_get s pos = 'X' && String.unsafe_get s (pos+1) = '8' && String.unsafe_get s (pos+2) = '6' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = 'F' && String.unsafe_get s (pos+5) = 'P' && String.unsafe_get s (pos+6) = '8' && String.unsafe_get s (pos+7) = '0' && String.unsafe_get s (pos+8) = 'T' && String.unsafe_get s (pos+9) = 'y' && String.unsafe_get s (pos+10) = 'p' && String.unsafe_get s (pos+11) = 'e' then (
                        3
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | 0 ->
              (FloatType : float_type)
            | 1 ->
              (DoubleType : float_type)
            | 2 ->
              (FP128Type : float_type)
            | 3 ->
              (X86_FP80Type : float_type)
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
)
let float_type_of_string s =
  read_float_type (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_float_value : _ -> float_value -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"myvalue\":";
    (
      Yojson.Safe.write_float
    )
      ob x.myvalue;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"mytype\":";
    (
      write_float_type
    )
      ob x.mytype;
    Bi_outbuf.add_char ob '}';
)
let string_of_float_value ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_float_value ob x;
  Bi_outbuf.contents ob
let read_float_value = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_myvalue = ref (Obj.magic 0.0) in
    let field_mytype = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 6 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'y' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' then (
                  1
                )
                else (
                  -1
                )
              )
            | 7 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 'v' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'u' && String.unsafe_get s (pos+6) = 'e' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_myvalue := (
              (
                Ag_oj_run.read_number
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_mytype := (
              (
                read_float_type
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 6 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'y' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 7 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'y' && String.unsafe_get s (pos+2) = 'v' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'u' && String.unsafe_get s (pos+6) = 'e' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_myvalue := (
                (
                  Ag_oj_run.read_number
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_mytype := (
                (
                  read_float_type
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "myvalue"; "mytype" |];
        (
          {
            myvalue = !field_myvalue;
            mytype = !field_mytype;
          }
         : float_value)
      )
)
let float_value_of_string s =
  read_float_value (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_const_value : _ -> const_value -> _ = (
  fun ob sum ->
    match sum with
      | IntVal x ->
        Bi_outbuf.add_string ob "<\"IntVal\":";
        (
          write_int_value
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | FloatVal x ->
        Bi_outbuf.add_string ob "<\"FloatVal\":";
        (
          write_float_value
        ) ob x;
        Bi_outbuf.add_char ob '>'
)
let string_of_const_value ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_const_value ob x;
  Bi_outbuf.contents ob
let read_const_value = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 6 -> (
                      if String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'V' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'l' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 8 -> (
                      if String.unsafe_get s pos = 'F' && String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'V' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 'l' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_int_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (IntVal x : const_value)
            | 1 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_float_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (FloatVal x : const_value)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 6 -> (
                      if String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'V' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'l' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 8 -> (
                      if String.unsafe_get s pos = 'F' && String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'V' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 'l' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_int_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (IntVal x : const_value)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_float_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (FloatVal x : const_value)
            | _ -> (
                assert false
              )
        )
)
let const_value_of_string s =
  read_const_value (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_value : _ -> value -> _ = (
  fun ob sum ->
    match sum with
      | VarValue x ->
        Bi_outbuf.add_string ob "<\"VarValue\":";
        (
          write_variable
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | ConstValue x ->
        Bi_outbuf.add_string ob "<\"ConstValue\":";
        (
          write_const_value
        ) ob x;
        Bi_outbuf.add_char ob '>'
)
let string_of_value ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_value ob x;
  Bi_outbuf.contents ob
let read_value = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 8 -> (
                      if String.unsafe_get s pos = 'V' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'V' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'l' && String.unsafe_get s (pos+6) = 'u' && String.unsafe_get s (pos+7) = 'e' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'C' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 's' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'V' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 'l' && String.unsafe_get s (pos+8) = 'u' && String.unsafe_get s (pos+9) = 'e' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_variable
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (VarValue x : value)
            | 1 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_const_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (ConstValue x : value)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 8 -> (
                      if String.unsafe_get s pos = 'V' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'V' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'l' && String.unsafe_get s (pos+6) = 'u' && String.unsafe_get s (pos+7) = 'e' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'C' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 's' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'V' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 'l' && String.unsafe_get s (pos+8) = 'u' && String.unsafe_get s (pos+9) = 'e' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_variable
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (VarValue x : value)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_const_value
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (ConstValue x : value)
            | _ -> (
                assert false
              )
        )
)
let value_of_string s =
  read_value (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_scope : _ -> scope -> _ = (
  fun ob sum ->
    match sum with
      | Source -> Bi_outbuf.add_string ob "<\"Source\">"
      | Target -> Bi_outbuf.add_string ob "<\"Target\">"
)
let string_of_scope ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_scope ob x;
  Bi_outbuf.contents ob
let read_scope = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 6 then (
                  match String.unsafe_get s pos with
                    | 'S' -> (
                        if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 'c' && String.unsafe_get s (pos+5) = 'e' then (
                          0
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | 'T' -> (
                        if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'g' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 't' then (
                          1
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | _ -> (
                        raise (Exit)
                      )
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Source : scope)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Target : scope)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 6 then (
                  match String.unsafe_get s pos with
                    | 'S' -> (
                        if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 'c' && String.unsafe_get s (pos+5) = 'e' then (
                          0
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | 'T' -> (
                        if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'g' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 't' then (
                          1
                        )
                        else (
                          raise (Exit)
                        )
                      )
                    | _ -> (
                        raise (Exit)
                      )
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | 0 ->
              (Source : scope)
            | 1 ->
              (Target : scope)
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
)
let scope_of_string s =
  read_scope (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_instr_type : _ -> instr_type -> _ = (
  fun ob sum ->
    match sum with
      | Command x ->
        Bi_outbuf.add_string ob "<\"Command\":";
        (
          Yojson.Safe.write_int
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | Phinode -> Bi_outbuf.add_string ob "<\"Phinode\">"
      | Terminator -> Bi_outbuf.add_string ob "<\"Terminator\">"
)
let string_of_instr_type ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_instr_type ob x;
  Bi_outbuf.contents ob
let read_instr_type = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 7 -> (
                      match String.unsafe_get s pos with
                        | 'C' -> (
                            if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'd' then (
                              0
                            )
                            else (
                              raise (Exit)
                            )
                          )
                        | 'P' -> (
                            if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 'n' && String.unsafe_get s (pos+4) = 'o' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                              1
                            )
                            else (
                              raise (Exit)
                            )
                          )
                        | _ -> (
                            raise (Exit)
                          )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'T' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'i' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'o' && String.unsafe_get s (pos+9) = 'r' then (
                        2
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  Ag_oj_run.read_int
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Command x : instr_type)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Phinode : instr_type)
            | 2 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Terminator : instr_type)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 7 -> (
                      if String.unsafe_get s pos = 'P' && String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 'n' && String.unsafe_get s (pos+4) = 'o' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 10 -> (
                      if String.unsafe_get s pos = 'T' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'i' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'o' && String.unsafe_get s (pos+9) = 'r' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | 0 ->
              (Phinode : instr_type)
            | 1 ->
              (Terminator : instr_type)
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                if len = 7 && String.unsafe_get s pos = 'C' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'd' then (
                  0
                )
                else (
                  raise (Exit)
                )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  Ag_oj_run.read_int
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Command x : instr_type)
            | _ -> (
                assert false
              )
        )
)
let instr_type_of_string s =
  read_instr_type (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_position : _ -> position -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"block_index\":";
    (
      Yojson.Safe.write_string
    )
      ob x.block_index;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"instr_type\":";
    (
      write_instr_type
    )
      ob x.instr_type;
    Bi_outbuf.add_char ob '}';
)
let string_of_position ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_position ob x;
  Bi_outbuf.contents ob
let read_position = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_block_index = ref (Obj.magic 0.0) in
    let field_instr_type = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 10 -> (
                if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = 'y' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'e' then (
                  1
                )
                else (
                  -1
                )
              )
            | 11 -> (
                if String.unsafe_get s pos = 'b' && String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'k' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 'i' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'x' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_block_index := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_instr_type := (
              (
                read_instr_type
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 10 -> (
                  if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = 'y' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 11 -> (
                  if String.unsafe_get s pos = 'b' && String.unsafe_get s (pos+1) = 'l' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'k' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 'i' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'x' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_block_index := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_instr_type := (
                (
                  read_instr_type
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "block_index"; "instr_type" |];
        (
          {
            block_index = !field_block_index;
            instr_type = !field_instr_type;
          }
         : position)
      )
)
let position_of_string s =
  read_position (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_remove_maydiff : _ -> remove_maydiff -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"position\":";
    (
      write_position
    )
      ob x.position;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"variable\":";
    (
      write_variable
    )
      ob x.variable;
    Bi_outbuf.add_char ob '}';
)
let string_of_remove_maydiff ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_remove_maydiff ob x;
  Bi_outbuf.contents ob
let read_remove_maydiff = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_position = ref (Obj.magic 0.0) in
    let field_variable = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 8 then (
            match String.unsafe_get s pos with
              | 'p' -> (
                  if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 'v' -> (
                  if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'b' && String.unsafe_get s (pos+6) = 'l' && String.unsafe_get s (pos+7) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_position := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_variable := (
              (
                read_variable
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 8 then (
              match String.unsafe_get s pos with
                | 'p' -> (
                    if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                      0
                    )
                    else (
                      -1
                    )
                  )
                | 'v' -> (
                    if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'b' && String.unsafe_get s (pos+6) = 'l' && String.unsafe_get s (pos+7) = 'e' then (
                      1
                    )
                    else (
                      -1
                    )
                  )
                | _ -> (
                    -1
                  )
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_position := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_variable := (
                (
                  read_variable
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "position"; "variable" |];
        (
          {
            position = !field_position;
            variable = !field_variable;
          }
         : remove_maydiff)
      )
)
let remove_maydiff_of_string s =
  read_remove_maydiff (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_propagate_instr : _ -> propagate_instr -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"lhs\":";
    (
      write_variable
    )
      ob x.lhs;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"rhs\":";
    (
      write_position
    )
      ob x.rhs;
    Bi_outbuf.add_char ob '}';
)
let string_of_propagate_instr ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_propagate_instr ob x;
  Bi_outbuf.contents ob
let read_propagate_instr = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_lhs = ref (Obj.magic 0.0) in
    let field_rhs = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 3 then (
            match String.unsafe_get s pos with
              | 'l' -> (
                  if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 'r' -> (
                  if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_lhs := (
              (
                read_variable
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_rhs := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 3 then (
              match String.unsafe_get s pos with
                | 'l' -> (
                    if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                      0
                    )
                    else (
                      -1
                    )
                  )
                | 'r' -> (
                    if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                      1
                    )
                    else (
                      -1
                    )
                  )
                | _ -> (
                    -1
                  )
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_lhs := (
                (
                  read_variable
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_rhs := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "lhs"; "rhs" |];
        (
          {
            lhs = !field_lhs;
            rhs = !field_rhs;
          }
         : propagate_instr)
      )
)
let propagate_instr_of_string s =
  read_propagate_instr (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_propagate_eq : _ -> propagate_eq -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"lhs\":";
    (
      write_value
    )
      ob x.lhs;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"rhs\":";
    (
      write_value
    )
      ob x.rhs;
    Bi_outbuf.add_char ob '}';
)
let string_of_propagate_eq ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_propagate_eq ob x;
  Bi_outbuf.contents ob
let read_propagate_eq = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_lhs = ref (Obj.magic 0.0) in
    let field_rhs = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 3 then (
            match String.unsafe_get s pos with
              | 'l' -> (
                  if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 'r' -> (
                  if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_lhs := (
              (
                read_value
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_rhs := (
              (
                read_value
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 3 then (
              match String.unsafe_get s pos with
                | 'l' -> (
                    if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                      0
                    )
                    else (
                      -1
                    )
                  )
                | 'r' -> (
                    if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                      1
                    )
                    else (
                      -1
                    )
                  )
                | _ -> (
                    -1
                  )
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_lhs := (
                (
                  read_value
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_rhs := (
                (
                  read_value
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "lhs"; "rhs" |];
        (
          {
            lhs = !field_lhs;
            rhs = !field_rhs;
          }
         : propagate_eq)
      )
)
let propagate_eq_of_string s =
  read_propagate_eq (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_propagate_object : _ -> propagate_object -> _ = (
  fun ob sum ->
    match sum with
      | Instr x ->
        Bi_outbuf.add_string ob "<\"Instr\":";
        (
          write_propagate_instr
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | Eq x ->
        Bi_outbuf.add_string ob "<\"Eq\":";
        (
          write_propagate_eq
        ) ob x;
        Bi_outbuf.add_char ob '>'
)
let string_of_propagate_object ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_propagate_object ob x;
  Bi_outbuf.contents ob
let read_propagate_object = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 2 -> (
                      if String.unsafe_get s pos = 'E' && String.unsafe_get s (pos+1) = 'q' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 5 -> (
                      if String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'r' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_propagate_instr
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Instr x : propagate_object)
            | 1 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_propagate_eq
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Eq x : propagate_object)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 2 -> (
                      if String.unsafe_get s pos = 'E' && String.unsafe_get s (pos+1) = 'q' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 5 -> (
                      if String.unsafe_get s pos = 'I' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'r' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_propagate_instr
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Instr x : propagate_object)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_propagate_eq
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Eq x : propagate_object)
            | _ -> (
                assert false
              )
        )
)
let propagate_object_of_string s =
  read_propagate_object (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_propagate : _ -> propagate -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"propagate\":";
    (
      write_propagate_object
    )
      ob x.propagate;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"propagate_from\":";
    (
      write_position
    )
      ob x.propagate_from;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"propagate_to\":";
    (
      write_position
    )
      ob x.propagate_to;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"scope\":";
    (
      write_scope
    )
      ob x.scope;
    Bi_outbuf.add_char ob '}';
)
let string_of_propagate ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_propagate ob x;
  Bi_outbuf.contents ob
let read_propagate = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_propagate = ref (Obj.magic 0.0) in
    let field_propagate_from = ref (Obj.magic 0.0) in
    let field_propagate_to = ref (Obj.magic 0.0) in
    let field_scope = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 5 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'c' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'e' then (
                  3
                )
                else (
                  -1
                )
              )
            | 9 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' then (
                  0
                )
                else (
                  -1
                )
              )
            | 12 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 't' && String.unsafe_get s (pos+11) = 'o' then (
                  2
                )
                else (
                  -1
                )
              )
            | 14 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 'f' && String.unsafe_get s (pos+11) = 'r' && String.unsafe_get s (pos+12) = 'o' && String.unsafe_get s (pos+13) = 'm' then (
                  1
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_propagate := (
              (
                read_propagate_object
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_propagate_from := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_propagate_to := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | 3 ->
            field_scope := (
              (
                read_scope
              ) p lb
            );
            bits0 := !bits0 lor 0x8;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 5 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'c' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'e' then (
                    3
                  )
                  else (
                    -1
                  )
                )
              | 9 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 12 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 't' && String.unsafe_get s (pos+11) = 'o' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | 14 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 'f' && String.unsafe_get s (pos+11) = 'r' && String.unsafe_get s (pos+12) = 'o' && String.unsafe_get s (pos+13) = 'm' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_propagate := (
                (
                  read_propagate_object
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_propagate_from := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_propagate_to := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | 3 ->
              field_scope := (
                (
                  read_scope
                ) p lb
              );
              bits0 := !bits0 lor 0x8;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0xf then Ag_oj_run.missing_fields p [| !bits0 |] [| "propagate"; "propagate_from"; "propagate_to"; "scope" |];
        (
          {
            propagate = !field_propagate;
            propagate_from = !field_propagate_from;
            propagate_to = !field_propagate_to;
            scope = !field_scope;
          }
         : propagate)
      )
)
let propagate_of_string s =
  read_propagate (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_infrule_base : _ -> infrule_base -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"position\":";
    (
      write_position
    )
      ob x.position;
    Bi_outbuf.add_char ob '}';
)
let string_of_infrule_base ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_infrule_base ob x;
  Bi_outbuf.contents ob
let read_infrule_base = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_position = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 8 && String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
            0
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_position := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 8 && String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
              0
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_position := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x1 then Ag_oj_run.missing_fields p [| !bits0 |] [| "position" |];
        (
          {
            position = !field_position;
          }
         : infrule_base)
      )
)
let infrule_base_of_string s =
  read_infrule_base (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_add_assoc : _ -> add_assoc -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"position\":";
    (
      write_position
    )
      ob x.position;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"lhs\":";
    (
      write_variable
    )
      ob x.lhs;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"rhs\":";
    (
      write_variable
    )
      ob x.rhs;
    Bi_outbuf.add_char ob '}';
)
let string_of_add_assoc ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_add_assoc ob x;
  Bi_outbuf.contents ob
let read_add_assoc = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_position = ref (Obj.magic 0.0) in
    let field_lhs = ref (Obj.magic 0.0) in
    let field_rhs = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 3 -> (
                match String.unsafe_get s pos with
                  | 'l' -> (
                      if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                        1
                      )
                      else (
                        -1
                      )
                    )
                  | 'r' -> (
                      if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                        2
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 8 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_position := (
              (
                read_position
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_lhs := (
              (
                read_variable
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_rhs := (
              (
                read_variable
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 3 -> (
                  match String.unsafe_get s pos with
                    | 'l' -> (
                        if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                          1
                        )
                        else (
                          -1
                        )
                      )
                    | 'r' -> (
                        if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 's' then (
                          2
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 8 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_position := (
                (
                  read_position
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_lhs := (
                (
                  read_variable
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_rhs := (
                (
                  read_variable
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x7 then Ag_oj_run.missing_fields p [| !bits0 |] [| "position"; "lhs"; "rhs" |];
        (
          {
            position = !field_position;
            lhs = !field_lhs;
            rhs = !field_rhs;
          }
         : add_assoc)
      )
)
let add_assoc_of_string s =
  read_add_assoc (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_command : _ -> command -> _ = (
  fun ob sum ->
    match sum with
      | Propagate x ->
        Bi_outbuf.add_string ob "<\"Propagate\":";
        (
          write_propagate
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | AddAssoc x ->
        Bi_outbuf.add_string ob "<\"AddAssoc\":";
        (
          write_add_assoc
        ) ob x;
        Bi_outbuf.add_char ob '>'
      | RemoveMaydiff x ->
        Bi_outbuf.add_string ob "<\"RemoveMaydiff\":";
        (
          write_remove_maydiff
        ) ob x;
        Bi_outbuf.add_char ob '>'
)
let string_of_command ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_command ob x;
  Bi_outbuf.contents ob
let read_command = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 8 -> (
                      if String.unsafe_get s pos = 'A' && String.unsafe_get s (pos+1) = 'd' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'A' && String.unsafe_get s (pos+4) = 's' && String.unsafe_get s (pos+5) = 's' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'c' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 9 -> (
                      if String.unsafe_get s pos = 'P' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 13 -> (
                      if String.unsafe_get s pos = 'R' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'v' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'M' && String.unsafe_get s (pos+7) = 'a' && String.unsafe_get s (pos+8) = 'y' && String.unsafe_get s (pos+9) = 'd' && String.unsafe_get s (pos+10) = 'i' && String.unsafe_get s (pos+11) = 'f' && String.unsafe_get s (pos+12) = 'f' then (
                        2
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_propagate
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Propagate x : command)
            | 1 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_add_assoc
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (AddAssoc x : command)
            | 2 ->
              Ag_oj_run.read_until_field_value p lb;
              let x = (
                  read_remove_maydiff
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (RemoveMaydiff x : command)
            | _ -> (
                assert false
              )
        )
      | `Double_quote -> (
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
          in
          let i = Yojson.Safe.map_string p f lb in
          match i with
            | _ -> (
                assert false
              )
        )
      | `Square_bracket -> (
          Yojson.Safe.read_space p lb;
          let f =
            fun s pos len ->
              if pos < 0 || len < 0 || pos + len > String.length s then
                invalid_arg "out-of-bounds substring position or length";
              try
                match len with
                  | 8 -> (
                      if String.unsafe_get s pos = 'A' && String.unsafe_get s (pos+1) = 'd' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'A' && String.unsafe_get s (pos+4) = 's' && String.unsafe_get s (pos+5) = 's' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'c' then (
                        1
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 9 -> (
                      if String.unsafe_get s pos = 'P' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'g' && String.unsafe_get s (pos+6) = 'a' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'e' then (
                        0
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | 13 -> (
                      if String.unsafe_get s pos = 'R' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'v' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'M' && String.unsafe_get s (pos+7) = 'a' && String.unsafe_get s (pos+8) = 'y' && String.unsafe_get s (pos+9) = 'd' && String.unsafe_get s (pos+10) = 'i' && String.unsafe_get s (pos+11) = 'f' && String.unsafe_get s (pos+12) = 'f' then (
                        2
                      )
                      else (
                        raise (Exit)
                      )
                    )
                  | _ -> (
                      raise (Exit)
                    )
              with Exit -> (
                  Ag_oj_run.invalid_variant_tag p (String.sub s pos len)
                )
          in
          let i = Yojson.Safe.map_ident p f lb in
          match i with
            | 0 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_propagate
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Propagate x : command)
            | 1 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_add_assoc
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (AddAssoc x : command)
            | 2 ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_remove_maydiff
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (RemoveMaydiff x : command)
            | _ -> (
                assert false
              )
        )
)
let command_of_string s =
  read_command (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write__1 = (
  Ag_oj_run.write_list (
    write_command
  )
)
let string_of__1 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__1 ob x;
  Bi_outbuf.contents ob
let read__1 = (
  Ag_oj_run.read_list (
    read_command
  )
)
let _1_of_string s =
  read__1 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_hints : _ -> hints -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"module_id\":";
    (
      Yojson.Safe.write_string
    )
      ob x.module_id;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"function_id\":";
    (
      Yojson.Safe.write_string
    )
      ob x.function_id;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"opt_name\":";
    (
      Yojson.Safe.write_string
    )
      ob x.opt_name;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"commands\":";
    (
      write__1
    )
      ob x.commands;
    Bi_outbuf.add_char ob '}';
)
let string_of_hints ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_hints ob x;
  Bi_outbuf.contents ob
let read_hints = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_module_id = ref (Obj.magic 0.0) in
    let field_function_id = ref (Obj.magic 0.0) in
    let field_opt_name = ref (Obj.magic 0.0) in
    let field_commands = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 8 -> (
                match String.unsafe_get s pos with
                  | 'c' -> (
                      if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'd' && String.unsafe_get s (pos+7) = 's' then (
                        3
                      )
                      else (
                        -1
                      )
                    )
                  | 'o' -> (
                      if String.unsafe_get s (pos+1) = 'p' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = 'n' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'm' && String.unsafe_get s (pos+7) = 'e' then (
                        2
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 9 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = '_' && String.unsafe_get s (pos+7) = 'i' && String.unsafe_get s (pos+8) = 'd' then (
                  0
                )
                else (
                  -1
                )
              )
            | 11 -> (
                if String.unsafe_get s pos = 'f' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'i' && String.unsafe_get s (pos+10) = 'd' then (
                  1
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_module_id := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_function_id := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_opt_name := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | 3 ->
            field_commands := (
              (
                read__1
              ) p lb
            );
            bits0 := !bits0 lor 0x8;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 8 -> (
                  match String.unsafe_get s pos with
                    | 'c' -> (
                        if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' && String.unsafe_get s (pos+5) = 'n' && String.unsafe_get s (pos+6) = 'd' && String.unsafe_get s (pos+7) = 's' then (
                          3
                        )
                        else (
                          -1
                        )
                      )
                    | 'o' -> (
                        if String.unsafe_get s (pos+1) = 'p' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = 'n' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'm' && String.unsafe_get s (pos+7) = 'e' then (
                          2
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 9 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = '_' && String.unsafe_get s (pos+7) = 'i' && String.unsafe_get s (pos+8) = 'd' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 11 -> (
                  if String.unsafe_get s pos = 'f' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'i' && String.unsafe_get s (pos+10) = 'd' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_module_id := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_function_id := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_opt_name := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | 3 ->
              field_commands := (
                (
                  read__1
                ) p lb
              );
              bits0 := !bits0 lor 0x8;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0xf then Ag_oj_run.missing_fields p [| !bits0 |] [| "module_id"; "function_id"; "opt_name"; "commands" |];
        (
          {
            module_id = !field_module_id;
            function_id = !field_function_id;
            opt_name = !field_opt_name;
            commands = !field_commands;
          }
         : hints)
      )
)
let hints_of_string s =
  read_hints (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
