Require Import syntax.
Require Import syntax_ext.
Require Import hints.

Import LLVMsyntax.
Require Import Coqlib.
Require Import Metatheory.
Require Import infrastructure.
Import LLVMinfra.

Set Implicit Arguments.


(** * Def/Use Varaibles of Program *)

(** ** [def_cmd] ([def_phinode]) returns a variable or a
pointer(=value) defined by the input [cmd] ([phinode]). *)

Definition def_cmd (c:cmd): id + value :=
  match c with
    | insn_bop i _ _ _ _ => inl i
    | insn_fbop i _ _ _ _ => inl i
    | insn_extractvalue i _ _ _ _ => inl i
    | insn_insertvalue i _ _ _ _ _ => inl i
    | insn_malloc i _ _ _ => inl i
    | insn_free _ _ p => inr p
    | insn_alloca i _ _ _ => inl i
    | insn_load i _ _ _ => inl i
    | insn_store _ _ _ p _ => inr p
    | insn_gep i _ _ _ _ _ => inl i
    | insn_trunc i _ _ _ _ => inl i
    | insn_ext i _ _ _ _ => inl i
    | insn_cast i _ _ _ _ => inl i
    | insn_icmp i _ _ _ _ => inl i
    | insn_fcmp i _ _ _ _ => inl i
    | insn_select i _ _ _ _ => inl i
    | insn_call i _ _ _ _ _ _ => inl i
  end.

Definition def_phinode (p:phinode): id :=
  match p with
    | insn_phi i _ _ => i
  end.

Fixpoint def_phinodes (ps:phinodes): list id :=
  match ps with
    | nil => nil
    | h::t => (def_phinode h)::(def_phinodes t)
  end.

Fixpoint def_phinodes_set (ps:phinodes): atoms :=
  match ps with
    | nil => empty
    | h::t => add (def_phinode h) (def_phinodes_set t)
  end.

Definition def_terminator (t:terminator): id :=
  match t with
    | insn_return i _ _ => i
    | insn_return_void i => i
    | insn_br i _ _ _ => i
    | insn_br_uncond i _ => i
    | insn_unreachable i => i
  end.

Definition def_insn (i:insn): id + value :=
  match i with
    | insn_phinode p => inl (def_phinode p)
    | insn_cmd c => def_cmd c
    | insn_terminator t => inl (def_terminator t)
  end.

Definition def_cmd_opt (cmd_opt: option cmd) : atoms :=
  match cmd_opt with
  | Some c => 
    match def_cmd c with
    | inl x => AtomSetImpl.singleton x
    | _ => AtomSetImpl.empty
    end
  | _ => AtomSetImpl.empty
  end.

Definition def_cmd_opt2 (cmd_opt1 cmd_opt2:option cmd) : atoms :=
  AtomSetImpl.union (def_cmd_opt cmd_opt1) (def_cmd_opt cmd_opt2).

Definition is_defined_same_id (cmd_opt1 cmd_opt2:option cmd) : bool :=
  let nd1 := def_cmd_opt cmd_opt1 in
  let nd2 := def_cmd_opt cmd_opt2 in
  AtomSetImpl.eq_dec nd1 nd2.

Definition oldify_id_ext (ids:list atom) (id:id_ext) : id_ext :=
  if in_dec id_dec (fst id) ids
  then (fst id, ntag_old)
  else id.

Definition oldify_value_ext (ids:list atom) (v:value_ext) : value_ext :=
  match v with
    | value_ext_id id => value_ext_id (oldify_id_ext ids id)
    | value_ext_const c => v
  end.

Definition replace_value_ext (x:id_ext) (y:value_ext) (v:value_ext) : value_ext :=
  match v with
    | value_ext_id id => if id_ext_dec x id then y else v
    | value_ext_const c => v
  end.

Definition replace_lsv (x:id_ext) (y:value_ext) (l:list (sz * value_ext)) : list (sz * value_ext) :=
  List.map (fun sv => (fst sv, replace_value_ext x y (snd sv))) l.

Definition replace_rhs_ext (x:id_ext) (y:value_ext) (e:rhs_ext) : rhs_ext :=
  match e with
    | rhs_ext_bop b1 s1 v1 w1 => rhs_ext_bop b1 s1 (replace_value_ext x y v1) (replace_value_ext x y w1)
    | rhs_ext_fbop fb1 fp1 v1 w1 => rhs_ext_fbop fb1 fp1 (replace_value_ext x y v1) (replace_value_ext x y w1)
    | rhs_ext_extractvalue t1 v1 lc1 u1 => rhs_ext_extractvalue t1 (replace_value_ext x y v1) lc1 u1
    | rhs_ext_insertvalue t1 v1 u1 w1 lc1 => rhs_ext_insertvalue t1 (replace_value_ext x y v1) u1 (replace_value_ext x y w1) lc1
    | rhs_ext_gep ib1 t1 v1 lsv1 u1 => rhs_ext_gep ib1 t1 (replace_value_ext x y v1) (replace_lsv x y lsv1) u1
    | rhs_ext_trunc top1 t1 v1 u1 => rhs_ext_trunc top1 t1 (replace_value_ext x y v1) u1
    | rhs_ext_ext ex1 t1 v1 u1 => rhs_ext_ext ex1 t1 (replace_value_ext x y v1) u1
    | rhs_ext_cast cop1 t1 v1 u1 => rhs_ext_cast cop1 t1 (replace_value_ext x y v1) u1
    | rhs_ext_icmp con1 t1 v1 w1 => rhs_ext_icmp con1 t1 (replace_value_ext x y v1) (replace_value_ext x y w1)
    | rhs_ext_fcmp fcon1 fp1 v1 w1 => rhs_ext_fcmp fcon1 fp1 (replace_value_ext x y v1) (replace_value_ext x y w1)
    | rhs_ext_select v1 t1 w1 z1 => rhs_ext_select (replace_value_ext x y v1) t1 (replace_value_ext x y w1) (replace_value_ext x y z1)
    | rhs_ext_value v1 => rhs_ext_value (replace_value_ext x y v1)
    | rhs_ext_old_alloca => rhs_ext_old_alloca
  end.

(** * Used Varaibles/Dereferenced Pointers of Hint *)

Definition used_locals_in_value (v:value_ext) : IdExtSetImpl.t :=
  match v with
    | value_ext_id x => IdExtSetImpl.singleton x
    | value_ext_const _ => IdExtSetImpl.empty
  end.

Definition used_locals_in_lsv (lsv:list (sz * value_ext)) : IdExtSetImpl.t :=
  fold_right
  (fun (sv:sz*value_ext) acc => 
    IdExtSetImpl.union (used_locals_in_value (snd sv)) acc)
  IdExtSetImpl.empty lsv.

Definition used_locals_in_params (prms:list (typ * attributes * value_ext)) : IdExtSetImpl.t :=
  fold_left
  (fun acc (tav:typ*attributes*value_ext) => 
    IdExtSetImpl.union (used_locals_in_value (snd tav)) acc)
  prms IdExtSetImpl.empty.

Definition used_locals_in_rhs (r:rhs_ext) : IdExtSetImpl.t :=
  match r with
    | rhs_ext_bop _ _ v1 v2
    | rhs_ext_fbop _ _ v1 v2 
    | rhs_ext_insertvalue _ v1 _ v2 _
    | rhs_ext_icmp _ _ v1 v2
    | rhs_ext_fcmp _ _ v1 v2
      => IdExtSetImpl.union (used_locals_in_value v1) (used_locals_in_value v2)
    | rhs_ext_extractvalue _ v _ _ 
    | rhs_ext_trunc _ _ v _
    | rhs_ext_ext _ _ v _
    | rhs_ext_cast _ _ v _
      => used_locals_in_value v
    | rhs_ext_gep _ _ v lsv _ 
      => IdExtSetImpl.union (used_locals_in_value v) (used_locals_in_lsv lsv)
    | rhs_ext_select v1 _ v2 v3 
      => IdExtSetImpl.union (used_locals_in_value v1) 
      (IdExtSetImpl.union (used_locals_in_value v2) (used_locals_in_value v3))
    | rhs_ext_value v => used_locals_in_value v
    | rhs_ext_old_alloca => IdExtSetImpl.empty
  end.

Definition used_locals_in_localglobal (lg:localglobal_t) : IdExtSetImpl.t :=
  match lg with
    | inl l => IdExtSetImpl.singleton l
    | inr g => IdExtSetImpl.empty
  end.

Definition used_locals_in_value' (v:value) : atoms :=
  match v with
    | value_id x => AtomSetImpl.singleton x
    | _ => AtomSetImpl.empty
  end.

Definition used_locals_in_lsv' (lsv:list (sz * value)) : atoms :=
  fold_right
  (fun (sv:sz*value) acc => 
    AtomSetImpl.union (used_locals_in_value' (snd sv)) acc)
  AtomSetImpl.empty lsv.

Definition used_locals_in_params' (prms:list (typ * attributes * value)) : atoms :=
  fold_left
  (fun acc (tav:typ*attributes*value) => 
    AtomSetImpl.union (used_locals_in_value' (snd tav)) acc)
  prms AtomSetImpl.empty.

Definition used_locals_in_cmd (c:cmd) : atoms :=
  match c with
  | insn_malloc _ _ v _
  | insn_free _ _ v
  | insn_alloca _ _ v _
  | insn_load _ _ v _
  | insn_extractvalue _ _ v _ _
  | insn_trunc _ _ _ v _
  | insn_ext _ _ _ v _
  | insn_cast _ _ _ v _ 
    => used_locals_in_value' v

  | insn_bop _ _ _ v1 v2
  | insn_fbop _ _ _ v1 v2
  | insn_insertvalue _ _ v1 _ v2 _
  | insn_store _ _ v1 v2 _
  | insn_icmp _ _ _ v1 v2
  | insn_fcmp _ _ _ v1 v2 
    => AtomSetImpl.union (used_locals_in_value' v1) (used_locals_in_value' v2)

  | insn_select _ v1 _ v2 v3 
    => AtomSetImpl.union 
    (AtomSetImpl.union (used_locals_in_value' v1) (used_locals_in_value' v2))
    (used_locals_in_value' v3)

  | insn_gep _ _ _ v lsv _ 
    => AtomSetImpl.union (used_locals_in_value' v) (used_locals_in_lsv' lsv)

  | insn_call _ _ _ _ _ v prms 
    => AtomSetImpl.union (used_locals_in_value' v) (used_locals_in_params' prms)
  end.

(** * Extending Local Variables with New Tags *)

Definition add_ntag (x:id) : id_ext := (x, ntag_new).

Definition add_ntag_value (v:value) : value_ext :=
  match v with
    | value_id x => value_ext_id (add_ntag x)
    | value_const c => value_ext_const c
  end.

Definition add_ntag_lsv (lsv:list (sz * value)) : list (sz * value_ext) :=
  List.map (fun sv => (fst sv, add_ntag_value (snd sv))) lsv.

Definition add_ntag_params (prms:params) : params_ext :=
  List.map
  (fun prm => (fst (fst prm), snd (fst prm), add_ntag_value (snd prm)))
  prms.

Definition add_ntag_cmd (c:cmd) : option rhs_ext :=
  match c with
  | insn_bop x b s v1 v2 =>
    Some (rhs_ext_bop b s (add_ntag_value v1) (add_ntag_value v2))
  | insn_fbop x fb fp v1 v2 =>
    Some (rhs_ext_fbop fb fp (add_ntag_value v1) (add_ntag_value v2))
  | insn_extractvalue x ty1 v lc ty2 =>
    Some (rhs_ext_extractvalue ty1 (add_ntag_value v) lc ty2)
  | insn_insertvalue x ty1 v1 ty2 v2 lc =>
    Some (rhs_ext_insertvalue ty1 (add_ntag_value v1) ty2 (add_ntag_value v2) lc)
  | insn_malloc x ty v a =>
    None
  | insn_free x ty v =>
    None
  | insn_alloca x ty v a =>
    None
  | insn_load x ty v a =>
    None
  | insn_store x ty v1 v2 a =>
    None
  | insn_gep x ib ty1 v lsv ty2 =>
    Some (rhs_ext_gep ib ty1 (add_ntag_value v) (add_ntag_lsv lsv) ty2)
  | insn_trunc x trop ty1 v ty2 =>
    Some (rhs_ext_trunc trop ty1 (add_ntag_value v) ty2)
  | insn_ext x eop ty1 v ty2 =>
    Some (rhs_ext_ext eop ty1 (add_ntag_value v) ty2)
  | insn_cast x cop ty1 v ty2 =>
    Some (rhs_ext_cast cop ty1 (add_ntag_value v) ty2)
  | insn_icmp x con ty v1 v2 =>
    Some (rhs_ext_icmp con ty (add_ntag_value v1) (add_ntag_value v2))
  | insn_fcmp x fcon fp v1 v2 =>
    Some (rhs_ext_fcmp fcon fp (add_ntag_value v1) (add_ntag_value v2))
  | insn_select x v1 ty v2 v3 =>
    Some (rhs_ext_select (add_ntag_value v1) ty (add_ntag_value v2) (add_ntag_value v3))
  | insn_call x nrt cla ty va v prms =>
    None
  end.

Definition is_typ_floatpoint typ :=
  match typ with
    | typ_floatpoint _ => true
    | _ => false
  end.

Definition add_ntag_cmd_to_eqs (e:eqs_t) (c:cmd) : eqs_t :=
  match c with
  | insn_bop x b s v1 v2 => 
    add_eq_reg (add_ntag x, rhs_ext_bop b s (add_ntag_value v1) (add_ntag_value v2)) e
  | insn_fbop x fb fp v1 v2 => 
    add_eq_reg (add_ntag x, rhs_ext_fbop fb fp (add_ntag_value v1) (add_ntag_value v2)) e
  | insn_extractvalue x ty1 v lc ty2 =>
    add_eq_reg (add_ntag x, rhs_ext_extractvalue ty1 (add_ntag_value v) lc ty2) e
  | insn_insertvalue x ty1 v1 ty2 v2 lc =>
    add_eq_reg (add_ntag x, rhs_ext_insertvalue ty1 (add_ntag_value v1) ty2 (add_ntag_value v2) lc) e
  | insn_malloc x ty v a => e
  | insn_free x ty v => e
  | insn_alloca x ty v a => add_eq_reg (add_ntag x, rhs_ext_old_alloca) e
  | insn_load x ty p a => 
    add_eq_heap (add_ntag_value p, ty, a, value_ext_id (add_ntag x)) e
  | insn_store x ty v p a =>
    add_eq_heap (add_ntag_value p, ty, a, add_ntag_value v) e
  | insn_gep x ib ty1 v lsv ty2 =>
    add_eq_reg (add_ntag x, rhs_ext_gep ib ty1 (add_ntag_value v) (add_ntag_lsv lsv) ty2) e
  | insn_trunc x trop ty1 v ty2 =>
    add_eq_reg (add_ntag x, rhs_ext_trunc trop ty1 (add_ntag_value v) ty2) e
  | insn_ext x eop ty1 v ty2 =>
    add_eq_reg (add_ntag x, rhs_ext_ext eop ty1 (add_ntag_value v) ty2) e
  | insn_cast x cop ty1 v ty2 =>
    add_eq_reg (add_ntag x, rhs_ext_cast cop ty1 (add_ntag_value v) ty2) e
  | insn_icmp x con ty v1 v2 =>
    add_eq_reg (add_ntag x, rhs_ext_icmp con ty (add_ntag_value v1) (add_ntag_value v2)) e
  | insn_fcmp x fcon fp v1 v2 =>
    add_eq_reg (add_ntag x, rhs_ext_fcmp fcon fp (add_ntag_value v1) (add_ntag_value v2)) e
  | insn_select x v1 ty v2 v3 =>
    add_eq_reg (add_ntag x, rhs_ext_select (add_ntag_value v1) ty (add_ntag_value  v2) (add_ntag_value v3)) e
  | insn_call x _ _ typ _ f params => e
  end.

Definition add_ntag_option_cmd_to_eqs (e:eqs_t) (oc:option cmd) : eqs_t :=
  match oc with
  | None => e
  | Some c => add_ntag_cmd_to_eqs e c
  end.

(* Definition add_pointer_non_equations_gm (e: NeqRegSetImpl.t) (aid: id) (gids: ids) := *)
(*   List.fold_left *)
(*   (fun e gid => NeqRegSetImpl.add (add_ntag aid, inr gid) e) gids e. *)

Definition add_pointer_non_equations_mm_aux (e: NeqRegSetImpl.t) (aid: id)
  (eq: id_ext * rhs_ext) :=
  let '(eid, erhs) := eq in
    match erhs with
      | rhs_ext_old_alloca =>
        NeqRegSetImpl.add (add_ntag aid, inl eid)
        (NeqRegSetImpl.add (eid, inl (add_ntag aid)) e)
      | _ => e
    end.

Definition add_pointer_non_equations_mm (e: NeqRegSetImpl.t) (aid: id)
  (re: EqRegSetImpl.t) :=
  EqRegSetImpl.fold (fun eq e => add_pointer_non_equations_mm_aux e aid eq) re e.

Definition add_pointer_non_equations (e:eqs_t) (oc:option cmd) (gids: ids) : eqs_t :=
  {|
    eqs_eq_reg := eqs_eq_reg e;
    eqs_eq_heap := eqs_eq_heap e;
    eqs_neq_reg :=
    match oc with
      | Some (insn_alloca i _ _ _) =>
        (add_pointer_non_equations_mm (eqs_neq_reg e) i (eqs_eq_reg e))
      | _ => (eqs_neq_reg e)
    end
    |}.

(** ** Extending Local Variables with Old Tags *)

Definition add_otag (x:id) : id_ext := (x, ntag_old).

Definition add_otag_value (v:value) : value_ext :=
  match v with
    | value_id x => value_ext_id (add_otag x)
    | value_const c => value_ext_const c
  end.

(** ** Extending Local Variables with Newly Define Variable Set *)

Definition add_tag (nd_by_phi:list atom) (x:id) : id_ext := 
  if List.in_dec id_dec x nd_by_phi then (x, ntag_old) else (x, ntag_new).

Definition add_tag_value (nd_by_phi:list atom) (v:value) : value_ext :=
  match v with
    | value_id x => value_ext_id (add_tag nd_by_phi x)
    | value_const c => value_ext_const c
  end.
