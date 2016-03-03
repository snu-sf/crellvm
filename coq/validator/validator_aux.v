Require Import syntax.
Require Import alist.
Require Import extraction_defs.
Require Import decs.
Require Import syntax_ext.
Require Import hints.
Require Import basic_aux.
Require Import vars_aux.
Require Import datatype_base.
Require Import Floats.
Require Import infrules.

Require Import Metatheory.
Require Export monad.
Require Import TODO.

Set Implicit Arguments.


(** * [only_read_memory] checks whether a function modifies memory or
not. *)

Definition only_read_memory_fheader (fh:fheader) : bool :=
  match fh with
  | fheader_intro (fnattrs_intro _ _ _ _ a) _ _ _ _ =>
    in_dec attribute_dec attribute_readnone a || 
    in_dec attribute_dec attribute_readonly a
  end.

Definition only_read_memory (m:module) (f: id) : bool := 
  match lookupFdecViaIDFromModule m f with
  | Some (fdec_intro fh _) => only_read_memory_fheader fh
  | _ => false
  end ||
  match lookupFdefViaIDFromModule m f with
  | Some (fdef_intro fh _) => only_read_memory_fheader fh
  | _ => false
  end.

(** * Equation check for register and heap *)

Definition eq_check_value (md:maydiff_t) (eqs1 eqs2:eqs_t) (v1 v2:value_ext) : bool :=
  match v1,v2 with
    | value_ext_id x1,value_ext_id x2 =>
      (id_ext_dec x1 x2 && negb (IdExtSetImpl.mem x1 md)) ||
      (negb (IdExtSetImpl.mem x1 md) && 
        (EqRegSetImpl.mem (x1,rhs_ext_value v2) (eqs_eq_reg eqs2) ||
         EqRegSetImpl.mem (x2,rhs_ext_value v1) (eqs_eq_reg eqs2))) ||
      (negb (IdExtSetImpl.mem x2 md) && 
        (EqRegSetImpl.mem (x1,rhs_ext_value v2) (eqs_eq_reg eqs1) ||
         EqRegSetImpl.mem (x2,rhs_ext_value v1) (eqs_eq_reg eqs1)))
    | value_ext_const c1,value_ext_const c2 => const_dec c1 c2
    | value_ext_id x1,value_ext_const _ =>
      EqRegSetImpl.mem (x1,rhs_ext_value v2) (eqs_eq_reg eqs1)
    | value_ext_const _,value_ext_id y2 =>
      EqRegSetImpl.mem (y2,rhs_ext_value v1) (eqs_eq_reg eqs2)
  end.

Definition eq_check_sv (md:maydiff_t) (eqs1 eqs2:eqs_t) (sv1 sv2: sz * value_ext) : bool :=
  let (s1,v1) := sv1 in
    let (s2,v2) := sv2 in
      sz_dec s1 s2 && eq_check_value md eqs1 eqs2 v1 v2.

Fixpoint eq_check_lsv (md:maydiff_t) (eqs1 eqs2:eqs_t) (lsv1 lsv2:list (sz * value_ext)) : bool :=
  match lsv1,lsv2 with
    | hd1::tl1,hd2::tl2 =>
      eq_check_sv md eqs1 eqs2 hd1 hd2 &&
      eq_check_lsv md eqs1 eqs2 tl1 tl2
    | nil,nil => true
    | _,_ => false
  end.

Definition eq_check_param (md:maydiff_t) (eqs1 eqs2:eqs_t) (p1 p2:typ * attributes * value_ext) : bool :=
  match p1,p2 with
    | ((t1,a1),v1),((t2,a2),v2) =>
      typ_dec t1 t2 && attributes_dec a1 a2 && eq_check_value md eqs1 eqs2 v1 v2
  end.

Fixpoint eq_check_params (md:maydiff_t) (eqs1 eqs2:eqs_t) (ps1 ps2:params_ext) : bool :=
  match ps1,ps2 with
    | hd1::tl1,hd2::tl2 => eq_check_param md eqs1 eqs2 hd1 hd2 && eq_check_params md eqs1 eqs2 tl1 tl2
    | nil,nil => true
    | _,_ => false
  end.

Definition is_isolated (iso:IdExtSetImpl.t) (v:value_ext) : bool := 
  match v with
  | value_ext_id x => IdExtSetImpl.mem x iso
  | value_ext_const _ => false
  end.

Definition is_not_isolated (iso:IdExtSetImpl.t) (v:value_ext) : bool := 
  negb (is_isolated iso v).

Definition is_not_isolated_id_new (iso:IdExtSetImpl.t) (x:id) : bool :=
  negb (IdExtSetImpl.mem (x, ntag_new) iso).

Definition is_not_isolated_param (iso:IdExtSetImpl.t) (p:typ * attributes * value_ext)
  : bool :=
  match p with (_,v) => is_not_isolated iso v end.

Fixpoint is_not_isolated_params (iso:IdExtSetImpl.t) (ps:params_ext) : bool :=
  match ps with
    | h::t => is_not_isolated_param iso h && is_not_isolated_params iso t
    | nil => true
  end.

Definition heap_eq_check (md:maydiff_t) (eqs1 eqs2:eqs_t)
  (iso1 iso2:IdExtSetImpl.t) (oc_orig oc_opt:option cmd) : bool :=
  match oc_orig,oc_opt with
  | Some (insn_call x1 nr1 cl1 t1 va1 v1 p1), 
    Some (insn_call x2 nr2 cl2 t2 va2 v2 p2) => 
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let p1_ext := add_ntag_params p1 in
    let p2_ext := add_ntag_params p2 in
    noret_dec nr1 nr2 &&
    clattrs_dec cl1 cl2 &&
    typ_dec t1 t2 && 
    varg_dec va1 va2 &&
    eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
    (* is_not_isolated iso1 v1_ext && *)
    (* is_not_isolated iso2 v2_ext && *)
    eq_check_params md eqs1 eqs2 p1_ext p2_ext
    (* is_not_isolated_params iso1 p1_ext && *)
    (* is_not_isolated_params iso2 p2_ext && *)
    (* (is_not_isolated_id_new iso1 x1) &&  *)
    (* (is_not_isolated_id_new iso2 x2) *)

  | Some (insn_call _ _ _ _ _ _ _), _ 
  | _, Some (insn_call _ _ _ _ _ _ _) => false

  | Some (insn_store _ t1 v1 p1 a1), 
    Some (insn_store _ t2 v2 p2 a2) => 
     (let v1_ext := add_ntag_value v1 in
      let v2_ext := add_ntag_value v2 in
      let p1_ext := add_ntag_value p1 in
      let p2_ext := add_ntag_value p2 in
      typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      (* is_not_isolated iso1 v1_ext && *)
      (* is_not_isolated iso2 v2_ext && *)
      eq_check_value md eqs1 eqs2 p1_ext p2_ext &&
      ((is_not_isolated iso1 p1_ext && is_not_isolated iso2 p2_ext) ||
       (is_isolated iso1 p1_ext && is_isolated iso2 p2_ext)) &&
      align_dec a1 a2)

  | Some (insn_store _ t1 v1 p1 a1), None => is_isolated iso1 (add_ntag_value p1)
  | None, Some (insn_store _ t2 v2 p2 a2) => false

  | Some (insn_store _ _ _ _ _), _
  | _, Some (insn_store _ _ _ _ _) => false

  | Some (insn_load x1 t1 v1 a1), Some (insn_load x2 t2 v2 a2) => 
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    typ_dec t1 t2 &&
    eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
    ((is_not_isolated iso1 v1_ext && is_not_isolated iso2 v2_ext) ||
      (is_isolated iso1 v1_ext && is_isolated iso2 v2_ext)) &&
    (* is_not_isolated iso1 v1_ext && *)
    (* is_not_isolated iso2 v2_ext && *)
    align_dec a1 a2
    (* (is_not_isolated_id_new iso1 x1) && *)
    (* (is_not_isolated_id_new iso2 x2) *)

    (* If have a time, permit None-load case. *)
  | _ , Some (insn_load _ _ _ _) => false

  | Some (insn_free _ t1 p1), Some (insn_free _ t2 p2) => 
    let p1_ext := add_ntag_value p1 in
    let p2_ext := add_ntag_value p2 in
    typ_dec t1 t2 &&
    eq_check_value md eqs1 eqs2 p1_ext p2_ext

  | Some (insn_free _ _ _), _
  | _, Some (insn_free _ _ _) => false

  | Some (insn_alloca _ _ _ _), None => true (* (is_not_isolated_id_new iso1 x1) *)
  | None, Some (insn_alloca _ _ _ _) => true
  | Some (insn_alloca x1 t1 v1 a1), Some(insn_alloca x2 t2 v2 a2) =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      align_dec a1 a2

  | Some (insn_alloca _ _ _ _), _ => false
  | _, Some (insn_alloca _ _ _ _) => false

  | Some (insn_malloc x1 t1 v1 a1), Some (insn_malloc x2 t2 v2 a2) =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      align_dec a1 a2
      (* (is_not_isolated_id_new iso1 x1) && *)
      (* (is_not_isolated_id_new iso2 x2) *)
  | Some (insn_malloc _ _ _ _), _ => false
  | _, Some (insn_malloc _ _ _ _) => false

  (* | Some c_orig, Some c_opt => *)
  (*   match def_cmd c_orig, def_cmd c_opt with *)
  (*     | inl x1, inl x2 => *)
  (*       (is_not_isolated_id_new iso1 x1) && *)
  (*       (is_not_isolated_id_new iso2 x2) *)
  (*     | inl x1, _ => (is_not_isolated_id_new iso1 x1) *)
  (*     | _, inl x2 => (is_not_isolated_id_new iso2 x2) *)
  (*     | _, _ => true *)
  (*   end *)

  (* | Some c_orig, _ => *)
  (*   match def_cmd c_orig with *)
  (*     | inl x1 => (is_not_isolated_id_new iso1 x1) *)
  (*     | _ => true *)
  (*   end *)

  (* | _, Some c_opt => *)
  (*   match def_cmd c_opt with *)
  (*     | inl x2 => (is_not_isolated_id_new iso2 x2) *)
  (*     | _ => true *)
  (*   end *)

  | _, _ => true
end.

(** * Filtering Hints that Do NOT Use a Local Variable / that Do NOT Dereference a Pointer *)

(** ** Remove old in equation *)

Definition filter_local_in_eqs_eq_reg (x:id_ext) (e:EqRegSetImpl.t) : EqRegSetImpl.t :=
  EqRegSetImpl.filter
  (fun (y_r:id_ext * rhs_ext) =>
   let (y,r) := y_r in
   negb (IdExtSetImpl.mem x (IdExtSetImpl.add y (used_locals_in_rhs r))))
  e.

Definition filter_local_in_eqs_eq_heap (x:id_ext) (e:EqHeapSetImpl.t) : EqHeapSetImpl.t :=
  EqHeapSetImpl.filter
  (fun (p_v:value_ext * typ * align * value_ext) =>
   let '(p,_,_,v) := p_v in
   negb (IdExtSetImpl.mem x (IdExtSetImpl.union (used_locals_in_value p) (used_locals_in_value v))))
  e.

Definition filter_local_in_eqs_neq_reg (x:id_ext) (e:NeqRegSetImpl.t) : NeqRegSetImpl.t :=
  NeqRegSetImpl.filter
  (fun (y_lg:id_ext * localglobal_t) =>
   let (y,lg) := y_lg in
   negb (IdExtSetImpl.mem x (IdExtSetImpl.add y (used_locals_in_localglobal lg))))
  e.

Definition remove_old_by_newdefs (e:eqs_t) (nd:atoms) : eqs_t :=
  {|
    eqs_eq_reg := (AtomSetImpl.fold
      (fun x acc => filter_local_in_eqs_eq_reg (add_otag x) acc)
      nd (eqs_eq_reg e));
    eqs_eq_heap := (AtomSetImpl.fold
      (fun x acc => filter_local_in_eqs_eq_heap (add_otag x) acc)
      nd (eqs_eq_heap e));
    eqs_neq_reg := (AtomSetImpl.fold
      (fun x acc => filter_local_in_eqs_neq_reg (add_otag x) acc)
      nd (eqs_neq_reg e))
      |}.

Definition remove_old_by_newdefs_list (e:eqs_t) (nd:list atom) : eqs_t :=
  {|
    eqs_eq_reg := (List.fold_right
      (fun x acc => filter_local_in_eqs_eq_reg (add_otag x) acc)
      (eqs_eq_reg e) nd);
    eqs_eq_heap := (List.fold_right
      (fun x acc => filter_local_in_eqs_eq_heap (add_otag x) acc)
      (eqs_eq_heap e) nd);
    eqs_neq_reg := (List.fold_right
      (fun x acc => filter_local_in_eqs_neq_reg (add_otag x) acc)
      (eqs_neq_reg e) nd)
      |}.

Definition remove_old_by_newdefs_iso (iso:IdExtSetImpl.t) (nd:atoms) : IdExtSetImpl.t :=
  AtomSetImpl.fold
    (fun x acc => IdExtSetImpl.remove (add_otag x) acc)
    nd iso.

Definition remove_old_by_newdefs_iso_list (iso:IdExtSetImpl.t) (nd:list atom)
  : IdExtSetImpl.t :=
  List.fold_right
    (fun x acc => IdExtSetImpl.remove (add_otag x) acc)
    iso nd.

Definition remove_old_md_by_newdefs (md:maydiff_t) (nd:atoms) : maydiff_t :=
  AtomSetImpl.fold
    (fun x acc => IdExtSetImpl.remove (add_otag x) acc)
    nd md.

Definition remove_old_md_by_newdefs_list (md:maydiff_t) (nd:list atom) : maydiff_t :=
  List.fold_right
    (fun x acc => IdExtSetImpl.remove (add_otag x) acc)
    md nd.

(** ** Change new to old in equation *)

Definition new_to_old_local_in_id (x:id) (ye:id_ext) : id_ext :=
  let (y,_) := ye in
  if id_dec x y then add_otag y else ye.

Definition new_to_old_local_in_value (x:id) (v:value_ext) : value_ext :=
  match v with
  | value_ext_id y => value_ext_id (new_to_old_local_in_id x y)
  | value_ext_const _ => v
  end.

Fixpoint new_to_old_local_in_lsv (x:id) (lsv:list (sz * value_ext)) : list (sz * value_ext) :=
  match lsv with
  | nil => nil
  | (s,v)::tl => (s,new_to_old_local_in_value x v)::(new_to_old_local_in_lsv x tl)
  end.

Definition new_to_old_local_in_rhs (x:id) (r:rhs_ext) : rhs_ext :=
  match r with
  | rhs_ext_bop b s v w =>
    rhs_ext_bop b s (new_to_old_local_in_value x v) (new_to_old_local_in_value x w)
  | rhs_ext_fbop fb fp v w =>
    rhs_ext_fbop fb fp (new_to_old_local_in_value x v) (new_to_old_local_in_value x w)
  | rhs_ext_extractvalue t v lc u =>
    rhs_ext_extractvalue t (new_to_old_local_in_value x v) lc u
  | rhs_ext_insertvalue t v u w lc =>
    rhs_ext_insertvalue t (new_to_old_local_in_value x v) u (new_to_old_local_in_value x w) lc
  | rhs_ext_gep ib t v lsv u =>
    rhs_ext_gep ib t (new_to_old_local_in_value x v) (new_to_old_local_in_lsv x lsv) u
  | rhs_ext_trunc top t v u =>
    rhs_ext_trunc top t (new_to_old_local_in_value x v) u
  | rhs_ext_ext eop t v u =>
    rhs_ext_ext eop t (new_to_old_local_in_value x v) u
  | rhs_ext_cast castop t v u =>
    rhs_ext_cast castop t (new_to_old_local_in_value x v) u
  | rhs_ext_icmp c t v w =>
    rhs_ext_icmp c t (new_to_old_local_in_value x v) (new_to_old_local_in_value x w)
  | rhs_ext_fcmp fc fp v w =>
    rhs_ext_fcmp fc fp (new_to_old_local_in_value x v) (new_to_old_local_in_value x w)
  | rhs_ext_select v t w z =>
    rhs_ext_select (new_to_old_local_in_value x v) t (new_to_old_local_in_value x w) (new_to_old_local_in_value x z)
  | rhs_ext_value v =>
    rhs_ext_value (new_to_old_local_in_value x v)
  | rhs_ext_old_alloca => rhs_ext_old_alloca
  end.

Definition new_to_old_local_in_idrhs (x: id) (yr: id_ext * rhs_ext) :=
  (new_to_old_local_in_id x (fst yr), new_to_old_local_in_rhs x (snd yr)).

Definition new_to_old_local_in_eq_reg (x:id) (e:EqRegSetImpl.t) : EqRegSetImpl.t :=
  EqRegSetImpl.fold   
    (fun (yr:id_ext * rhs_ext) acc =>
     EqRegSetImpl.add (new_to_old_local_in_idrhs x yr) acc)
    e EqRegSetImpl.empty.

Definition new_to_old_local_in_vv (x: id) (vw: value_ext * typ * align * value_ext) :=
  let '(v, t, a, w) := vw in
  (new_to_old_local_in_value x v, t, a, new_to_old_local_in_value x w).

Definition new_to_old_local_in_eq_heap (x:id) (e:EqHeapSetImpl.t) : EqHeapSetImpl.t :=
  EqHeapSetImpl.fold   
    (fun (vw:value_ext * typ * align * value_ext) acc =>
     EqHeapSetImpl.add (new_to_old_local_in_vv x vw) acc)
    e EqHeapSetImpl.empty.

Definition new_to_old_local_in_localglobal (x:id) (lg:localglobal_t) : localglobal_t :=
  match lg with
    | inl y => inl (new_to_old_local_in_id x y)
    | _ => lg
  end.

Definition new_to_old_local_in_idlg (x: id) (ylg: id_ext * localglobal_t) :=
  (new_to_old_local_in_id x (fst ylg), new_to_old_local_in_localglobal x (snd ylg)).

Definition new_to_old_local_in_neq_reg (x:id) (e:NeqRegSetImpl.t) : NeqRegSetImpl.t :=
  NeqRegSetImpl.fold   
    (fun (ylg:id_ext * localglobal_t) acc =>
     NeqRegSetImpl.add (new_to_old_local_in_idlg x ylg) acc)
    e NeqRegSetImpl.empty.

Definition new_to_old_local_in_eqs (x:id) (e:eqs_t) : eqs_t :=
  {| eqs_eq_reg := new_to_old_local_in_eq_reg x (eqs_eq_reg e);
     eqs_eq_heap := new_to_old_local_in_eq_heap x (eqs_eq_heap e);
     eqs_neq_reg := new_to_old_local_in_neq_reg x (eqs_neq_reg e) |}.

Definition new_to_old_by_newdefs (e:eqs_t) (nd:atoms) : eqs_t :=
  {|
    eqs_eq_reg := (AtomSetImpl.fold
      (fun x acc => new_to_old_local_in_eq_reg x acc)
      nd (eqs_eq_reg e));
    eqs_eq_heap := (AtomSetImpl.fold
      (fun x acc => new_to_old_local_in_eq_heap x acc)
      nd (eqs_eq_heap e));
    eqs_neq_reg := (AtomSetImpl.fold
      (fun x acc => new_to_old_local_in_neq_reg x acc)
      nd (eqs_neq_reg e))
      |}.

Definition new_to_old_by_newdefs_list (e:eqs_t) (nd:list atom) : eqs_t :=
  {|
    eqs_eq_reg := (List.fold_right
      (fun x acc => new_to_old_local_in_eq_reg x acc)
      (eqs_eq_reg e) nd);
    eqs_eq_heap := (List.fold_right
      (fun x acc => new_to_old_local_in_eq_heap x acc)
      (eqs_eq_heap e) nd);
    eqs_neq_reg := (List.fold_right
      (fun x acc => new_to_old_local_in_neq_reg x acc)
      (eqs_neq_reg e) nd)
      |}.

Definition new_to_old_by_newdefs_iso (iso:IdExtSetImpl.t) (nd:atoms) : IdExtSetImpl.t :=
  AtomSetImpl.fold
    (fun x acc => 
      if IdExtSetImpl.mem (add_ntag x) acc
        then IdExtSetImpl.add (add_otag x) (IdExtSetImpl.remove (add_ntag x) acc)
        else acc)
    nd iso.

Definition new_to_old_by_newdefs_iso_list (iso:IdExtSetImpl.t) (nd:list atom)
  : IdExtSetImpl.t :=
  List.fold_right
    (fun x acc => 
      if IdExtSetImpl.mem (add_ntag x) acc
        then IdExtSetImpl.add (add_otag x) (IdExtSetImpl.remove (add_ntag x) acc)
        else acc)
    iso nd.

Definition new_to_old_md_by_newdefs (md:maydiff_t) (nd:atoms) : maydiff_t :=
  AtomSetImpl.fold
    (fun x acc => 
      if IdExtSetImpl.mem (add_ntag x) md
      then IdExtSetImpl.add (add_otag x) (IdExtSetImpl.remove (add_ntag x) md)
      else md)
    nd md.

Definition new_to_old_md_by_newdefs_list (md:maydiff_t) (nd:list atom) : maydiff_t :=
  List.fold_right
    (fun x acc => 
      if IdExtSetImpl.mem (add_ntag x) md
      then IdExtSetImpl.add (add_otag x) (IdExtSetImpl.remove (add_ntag x) md)
      else md)
    md nd.

(** ** Filter equations by function call 

       Remove invalid heap equations *)

Definition filter_pointer_in_eqs_eq_heap (ne:NeqRegSetImpl.t) (p:value_ext) (e:EqHeapSetImpl.t) : EqHeapSetImpl.t :=
  EqHeapSetImpl.filter
  (fun (q_v:value_ext * typ * align * value_ext) =>
   let '(q,_,_,_) := q_v in
   (* q MUST be different to p for NOT being filtered out. *)
   match p,q with
     | value_ext_id r1,value_ext_id r2 =>
       NeqRegSetImpl.mem (r1,inl r2) ne || NeqRegSetImpl.mem (r2,inl r1) ne
     | value_ext_const (const_gid _ g),value_ext_id r
     | value_ext_id r,value_ext_const (const_gid _ g) =>
       NeqRegSetImpl.mem (r,inr g) ne
     | value_ext_const (const_gid _ g1),value_ext_const (const_gid _ g2) =>
       negb (id_dec g1 g2)
     | _,_ => false
   end)
  e.

Definition filter_pointer_in_eqs (p:value_ext) (e:eqs_t) : eqs_t :=
  {| eqs_eq_reg := eqs_eq_reg e;
     eqs_eq_heap := filter_pointer_in_eqs_eq_heap (eqs_neq_reg e) p (eqs_eq_heap e);
     eqs_neq_reg := eqs_neq_reg e |}.

Definition filter_heap_eqs_by_cmd (e:eqs_t) (oc:option cmd) : eqs_t :=
  match oc with
  | None => e
  | Some c => 
    match def_cmd c with
    | inl x => e
    | inr p => filter_pointer_in_eqs (add_ntag_value p) e
    end
  end.

Definition is_empty_eqs_heap (h:insn_hint_t) : bool :=
  let inv := hint_invariant h in
    EqHeapSetImpl.is_empty (eqs_eq_heap (invariant_original inv)) &&
    EqHeapSetImpl.is_empty (eqs_eq_heap (invariant_optimized inv)).

Definition only_read_memory_value (m:module) (fv: value) : bool := 
  match fv with
    | value_id f => only_read_memory m f
    | value_const (const_gid _ f) => only_read_memory m f
    | _ => false
  end.

Definition filter_eq_heap_by_only_read_memory_value (m:module) (c_opt:option cmd) (e:eqs_t) : eqs_t :=
  let e := filter_heap_eqs_by_cmd e c_opt in                 

  {| eqs_eq_reg := eqs_eq_reg e;
     eqs_eq_heap := match c_opt with
                     | Some (insn_call _ _ _ _ _ f _) =>
                       if only_read_memory_value m f
                         then eqs_eq_heap e
                         else EqHeapSetImpl.empty
                     | _ => eqs_eq_heap e
                    end;
     eqs_neq_reg := eqs_neq_reg e |}.


(** * MayDiff Update by Cmds *)

Definition maydiff_add_def_new (md:maydiff_t) (c:cmd) : maydiff_t :=
  match def_cmd c with
  | inl x => IdExtSetImpl.add (add_ntag x) md
  | inr v => md
  end.

Definition maydiff_add_def_new_opt (md:maydiff_t) (oc:option cmd) : maydiff_t :=
  match oc with
    | None => md
    | Some c => maydiff_add_def_new md c
  end.

Definition maydiff_add_def_all (md:maydiff_t) (c:cmd) : maydiff_t :=
  match def_cmd c with
  | inl x => IdExtSetImpl.add (add_otag x) (IdExtSetImpl.add (add_ntag x) md)
  | inr v => md
  end.

Definition maydiff_add_def_all_opt (md:maydiff_t) (oc:option cmd) : maydiff_t :=
  match oc with
    | None => md
    | Some c => maydiff_add_def_all md c
  end.

Definition is_same_cmd (md:maydiff_t) (eqs1 eqs2:eqs_t)
  (* (iso1 iso2:atoms) *) (cmd1 cmd2:cmd) : bool :=

  match cmd1,cmd2 with
  | insn_bop x1 b1 s1 v1 w1,insn_bop x2 b2 s2 v2 w2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
      id_dec x1 x2 && bop_dec b1 b2 && sz_dec s1 s2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext && 
      eq_check_value md eqs1 eqs2 w1_ext w2_ext

  | insn_fbop x1 fb1 fp1 v1 w1,insn_fbop x2 fb2 fp2 v2 w2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
      id_dec x1 x2 && fbop_dec fb1 fb2 && 
      floating_point_dec fp1 fp2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      eq_check_value md eqs1 eqs2 w1_ext w2_ext

  | insn_extractvalue x1 t1 v1 lc1 u1, insn_extractvalue x2 t2 v2 lc2 u2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext && 
      list_const_dec lc1 lc2 && typ_dec u1 u2

  | insn_insertvalue x1 t1 v1 u1 w1 lc1, insn_insertvalue x2 t2 v2 u2 w2 lc2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
      id_dec x1 x2 && typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext && 
      typ_dec u1 u2 &&
      eq_check_value md eqs1 eqs2 w1_ext w2_ext && 
      list_const_dec lc1 lc2

  | insn_malloc x1 t1 v1 a1,insn_malloc x2 t2 v2 a2
  | insn_alloca x1 t1 v1 a1,insn_alloca x2 t2 v2 a2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      align_dec a1 a2
      (* negb (AtomSetImpl.mem x1 iso1) && *)
      (* negb (AtomSetImpl.mem x2 iso2) *)

  | insn_load x1 t1 v1 a1,insn_load x2 t2 v2 a2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      (* is_not_isolated iso1 v1 &&  *)
      (* is_not_isolated iso2 v2 &&  *)
      align_dec a1 a2

  | insn_free _ t1 v1,insn_free _ t2 v2 => true
  | insn_store _ t1 v1 p1 a1,insn_store _ t2 v2 p2 a2 => true

  | insn_gep x1 ib1 t1 v1 lsv1 u1,insn_gep x2 ib2 t2 v2 lsv2 u2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let lsv1_ext := add_ntag_lsv lsv1 in
    let lsv2_ext := add_ntag_lsv lsv2 in
      id_dec x1 x2 && inbounds_dec ib1 ib2 &&
      typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      eq_check_lsv md eqs1 eqs2 lsv1_ext lsv2_ext &&
      typ_dec u1 u2

  | insn_trunc x1 top1 t1 v1 u1,insn_trunc x2 top2 t2 v2 u2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && truncop_dec top1 top2 &&
      typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      typ_dec u1 u2

  | insn_ext x1 eop1 t1 v1 u1,insn_ext x2 eop2 t2 v2 u2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && extop_dec eop1 eop2 &&
      typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      typ_dec u1 u2

  | insn_cast x1 cop1 t1 v1 u1,insn_cast x2 cop2 t2 v2 u2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
      id_dec x1 x2 && castop_dec cop1 cop2 &&
      typ_dec t1 t2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      typ_dec u1 u2

  | insn_icmp x1 c1 t1 v1 w1,insn_icmp x2 c2 t2 v2 w2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
      id_dec x1 x2 && cond_dec c1 c2 &&
      typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      eq_check_value md eqs1 eqs2 w1_ext w2_ext

  | insn_fcmp x1 fc1 fp1 v1 w1,insn_fcmp x2 fc2 fp2 v2 w2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
      id_dec x1 x2 && fcond_dec fc1 fc2 &&
      floating_point_dec fp1 fp2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      eq_check_value md eqs1 eqs2 w1_ext w2_ext

  | insn_select x1 v1 t1 w1 z1,insn_select x2 v2 t2 w2 z2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let w1_ext := add_ntag_value w1 in
    let w2_ext := add_ntag_value w2 in
    let z1_ext := add_ntag_value z1 in
    let z2_ext := add_ntag_value z2 in
      id_dec x1 x2 && 
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      typ_dec t1 t2 && 
      eq_check_value md eqs1 eqs2 w1_ext w2_ext &&
      eq_check_value md eqs1 eqs2 z1_ext z2_ext

  | insn_call x1 nr1 cl1 t1 va1 v1 p1, insn_call x2 nr2 cl2 t2 va2 v2 p2 =>
    let v1_ext := add_ntag_value v1 in
    let v2_ext := add_ntag_value v2 in
    let p1_ext := add_ntag_params p1 in
    let p2_ext := add_ntag_params p2 in
      id_dec x1 x2 && noret_dec nr1 nr2 && noret_dec nr1 false &&
      clattrs_dec cl1 cl2 &&
      typ_dec t1 t2 && 
      varg_dec va1 va2 &&
      eq_check_value md eqs1 eqs2 v1_ext v2_ext &&
      (* is_not_isolated iso1 v1 && *)
      (* is_not_isolated iso2 v2 && *)
      eq_check_params md eqs1 eqs2 p1_ext p2_ext
      (* is_not_isolated_params iso1 p1 && *)
      (* is_not_isolated_params iso2 p2 *)

  | _,_ => false
  end.

Definition maydiff_update (md:maydiff_t) (eqs1 eqs2:eqs_t) (cmd1 cmd2:cmd)
  : maydiff_t :=
  if (is_same_cmd md eqs1 eqs2 cmd1 cmd2)
    then md
    else if is_defined_same_id (Some cmd1) (Some cmd2)
      then maydiff_add_def_new md cmd1
      else maydiff_add_def_all (maydiff_add_def_all md cmd1) cmd2.

Definition maydiff_update_opt 
  (md:maydiff_t) (eqs1 eqs2:eqs_t) (ocmd1 ocmd2:option cmd) : maydiff_t :=
  match ocmd1,ocmd2 with
    | None,None => md
    | Some cmd_original,None =>  
      maydiff_add_def_all md cmd_original
    | None,Some cmd_optimized => 
      maydiff_add_def_all md cmd_optimized
    | Some cmd_original,Some cmd_optimized =>
      maydiff_update md eqs1 eqs2 cmd_original cmd_optimized 
  end.

(** * adds equations from phinodes according to the previous label. *)

Definition phinode_select_by_l (nd_by_phi:list atom) (prev_bb:l) (p:phinode)
  : option (id_ext * rhs_ext) :=
  match p with
    | insn_phi x typ_x lvl =>
      match getValueViaLabelFromValuels lvl prev_bb with
        | Some v => Some (add_ntag x, rhs_ext_value (add_tag_value nd_by_phi v))
        | None => None
      end
  end.

Fixpoint add_ntag_phis_to_eqs_reg_eq (nd:list atom) (prev_bb:l)
  (e:EqRegSetImpl.t) (phis:phinodes) : EqRegSetImpl.t :=
  match phis with
    | nil => e
    | phi::tphis =>
      match phinode_select_by_l nd prev_bb phi with
        | ret (x, r) =>
          EqRegSetImpl.add (x, r) (filter_local_in_eqs_eq_reg x
            (add_ntag_phis_to_eqs_reg_eq nd prev_bb e tphis))
        | merror => add_ntag_phis_to_eqs_reg_eq nd prev_bb e tphis
      end
  end.

Fixpoint filter_locals_in_eqs_eq_heap (nd:list atom) (prev_bb:l)
  (e:EqHeapSetImpl.t) (phis:phinodes) : EqHeapSetImpl.t :=
  match phis with
    | nil => e
    | phi::tphis =>
      match phinode_select_by_l nd prev_bb phi with
        | ret (x, r) => (filter_local_in_eqs_eq_heap x
          (filter_locals_in_eqs_eq_heap nd prev_bb e tphis))
        | merror => filter_locals_in_eqs_eq_heap nd prev_bb e tphis
      end
  end.

Fixpoint filter_locals_in_eqs_neq_reg (nd:list atom) (prev_bb:l)
  (e:NeqRegSetImpl.t) (phis:phinodes) : NeqRegSetImpl.t :=
  match phis with
    | nil => e
    | phi::tphis =>
      match phinode_select_by_l nd prev_bb phi with
        | ret (x, r) => (filter_local_in_eqs_neq_reg x
          (filter_locals_in_eqs_neq_reg nd prev_bb e tphis))
        | merror => filter_locals_in_eqs_neq_reg nd prev_bb e tphis
      end
  end.

Definition add_ntag_phis_to_eqs (nd:list atom) (prev_bb:l) (e:eqs_t) (phis:phinodes)
  : eqs_t :=
  match e with Build_eqs_t er eh enr =>
    {|
      eqs_eq_reg := add_ntag_phis_to_eqs_reg_eq nd prev_bb er phis;
      eqs_eq_heap := filter_locals_in_eqs_eq_heap nd prev_bb eh phis;
      eqs_neq_reg := filter_locals_in_eqs_neq_reg nd prev_bb enr phis
      |}
  end.

(** * Equality check on terminator  *)

Definition terminator_args_eq_check (t1 t2:terminator) (h:insn_hint_t) : bool :=
  let inv := hint_invariant h in
  let eqs_orig := invariant_original inv in
  let eqs_opt := invariant_optimized inv in
  match t1,t2 with
  | insn_return_void _, insn_return_void _ => true
  | insn_return _ t1 v1, insn_return _ t2 v2 =>
    typ_dec t1 t2 && 
    eq_check_value (hint_maydiff h) eqs_orig eqs_opt
                   (add_ntag_value v1) 
                   (add_ntag_value v2)
  | insn_br _ v1 l1 r1, insn_br _ v2 l2 r2 =>
    eq_check_value (hint_maydiff h) eqs_orig eqs_opt
                   (add_ntag_value v1) 
                   (add_ntag_value v2) &&
    l_dec l1 l2 && l_dec r1 r2
  | insn_br_uncond _ l1, insn_br_uncond _ l2 => l_dec l1 l2
  | insn_unreachable _, insn_unreachable _ => true
  | _, _ => false
  end.


(** * Self use check: for example, x=x+1 is validation failed *)

Definition self_use_check' (c:cmd) : bool :=
  match def_cmd c with
  | inl x => negb (AtomSetImpl.mem x (used_locals_in_cmd c))
  | _ => true
  end.

Definition self_use_check (c_opt:option cmd) : bool :=
  match c_opt with
  | None => true
  | Some c => self_use_check' c
  end.

(** * Register isolated pointers *)

Definition register_isolated_pointers_orig (ocmd1 ocmd2: option cmd)
  (iso1: IdExtSetImpl.t) : IdExtSetImpl.t :=
  match ocmd1, ocmd2 with
    | Some (insn_alloca aid _ _ _), None => IdExtSetImpl.add (add_ntag aid) iso1
    | _, _ => iso1
  end.

Definition register_isolated_pointers_opt (ocmd1 ocmd2: option cmd)
  (iso2: IdExtSetImpl.t) : IdExtSetImpl.t :=
  match ocmd1, ocmd2 with
    | None, Some (insn_alloca aid _ _ _) => IdExtSetImpl.add (add_ntag aid) iso2
    | _, _ => iso2
  end.

(** * Invariant Proceed

This returns the invariant and newly generated maydiffs after an
invariant([inv]) goes through instructions [cmd_original](optional)
and [cmd_optimized](optional).  *)

Definition invariant_proceed (lm rm: module) (h: insn_hint_t) 
  (cmd_original_opt cmd_optimized_opt: option cmd)
  : option insn_hint_t :=

  let md := hint_maydiff h in
  let inv := hint_invariant h in
  let ifr := hint_infrules h in

  let eqs_orig := invariant_original inv in
  let eqs_opt := invariant_optimized inv in
  let iso_orig := iso_original inv in
  let iso_opt := iso_optimized inv in

  (* 0.1 heap equality check *)
  if negb (heap_eq_check md eqs_orig eqs_opt
    iso_orig iso_opt cmd_original_opt cmd_optimized_opt)
  then None
  else

  (* 0.2 self use check: for example, x=x+1 is validation failed *)
  if negb (self_use_check cmd_original_opt) ||
     negb (self_use_check cmd_optimized_opt)
  then None
  else

  let nd_orig := def_cmd_opt cmd_original_opt in
  let nd_opt := def_cmd_opt cmd_optimized_opt in
  let nd_inter := AtomSetImpl.inter nd_orig nd_opt in

  (* 1.1 remove old *)
  let md := remove_old_md_by_newdefs md nd_inter in
  let eqs_orig := remove_old_by_newdefs eqs_orig nd_orig in 
  let eqs_opt := remove_old_by_newdefs eqs_opt nd_opt in
  let iso_orig := remove_old_by_newdefs_iso iso_orig nd_orig in
  let iso_opt := remove_old_by_newdefs_iso iso_opt nd_opt in

  (* 1.2 new -> old *)
  let md := new_to_old_md_by_newdefs md nd_inter in
  let eqs_orig := new_to_old_by_newdefs eqs_orig nd_orig in 
  let eqs_opt := new_to_old_by_newdefs eqs_opt nd_opt in
  let iso_orig := new_to_old_by_newdefs_iso iso_orig nd_orig in
  let iso_opt := new_to_old_by_newdefs_iso iso_opt nd_opt in

  (* 2. update maydiff *)
  let md := maydiff_update_opt md eqs_orig eqs_opt
    cmd_original_opt cmd_optimized_opt in

  (* 3. add pointer non-equations *)
  let lgids := collect_global_ids (get_products_from_module lm) in
  let rgids := collect_global_ids (get_products_from_module rm) in
  let eqs_orig := add_pointer_non_equations eqs_orig cmd_original_opt lgids in
  let eqs_opt := add_pointer_non_equations eqs_opt cmd_optimized_opt rgids in

  (* 4. filter heap equations when callee may change memory *)
  let eqs_orig := filter_eq_heap_by_only_read_memory_value lm
    cmd_original_opt eqs_orig in
  let eqs_opt := filter_eq_heap_by_only_read_memory_value rm
    cmd_optimized_opt eqs_opt in

  (* 5. add the new definitions to the equations *)
  let eqs_orig := add_ntag_option_cmd_to_eqs eqs_orig cmd_original_opt in
  let eqs_opt := add_ntag_option_cmd_to_eqs eqs_opt cmd_optimized_opt in

  (* 6. register isolated pointers, if necessary *)
  let iso_orig := register_isolated_pointers_orig
    cmd_original_opt cmd_optimized_opt iso_orig in
  let iso_opt := register_isolated_pointers_opt
    cmd_original_opt cmd_optimized_opt iso_opt in

  Some {|
    hint_maydiff := md;
    hint_invariant := 
    {| invariant_original := eqs_orig; invariant_optimized := eqs_opt;
       iso_original := iso_orig; iso_optimized := iso_opt |};
    hint_infrules := ifr |}
  .

Definition atom_inter (l1 l2: list atom) : list atom :=
  List.filter (fun e => if (List.in_dec id_dec e l2) then true else false) l1.

Definition atom_union (l1 l2: list atom) : list atom := List.app l1 l2.

Fixpoint is_uniq_def_phinodes (ps:phinodes): bool :=
  match ps with
    | nil => true
    | h::t => negb (in_dec id_dec (def_phinode h) (def_phinodes t)) &&
      is_uniq_def_phinodes t
  end.

Definition invariant_proceed_phis (h:insn_hint_t) 
  (lphis rphis:phinodes) (prev_bb:l) : option insn_hint_t :=

  let md := hint_maydiff h in
  let inv := hint_invariant h in
  let ifr := hint_infrules h in

  let eqs_orig := invariant_original inv in
  let eqs_opt := invariant_optimized inv in
  let iso_orig := iso_original inv in
  let iso_opt := iso_optimized inv in

  let nd_orig := def_phinodes lphis in
  let nd_opt := def_phinodes rphis in
  let nd_inter := atom_inter nd_orig nd_opt in
  let nd := atom_union nd_orig nd_opt in

  (* 0.1 Isolation check: if x(in iso) is defined in phinodes,
     the validation will be failed. *)
  if negb (IdExtSetImpl.for_all
    (fun x => negb (List.in_dec id_dec (fst x) (def_phinodes lphis))) iso_orig)
  then None
  else

  if negb (IdExtSetImpl.for_all
    (fun x => negb (List.in_dec id_dec (fst x) (def_phinodes rphis))) iso_opt)
  then None
  else

  (* 0.2. Uniqueness check *)
  if negb (is_uniq_def_phinodes lphis && is_uniq_def_phinodes rphis)
  then None
  else

  (* 1.1 remove old *)
  let md := remove_old_md_by_newdefs_list md nd_inter in
  let eqs_orig := remove_old_by_newdefs_list eqs_orig nd_orig in 
  let eqs_opt := remove_old_by_newdefs_list eqs_opt nd_opt in

  (* 1.2 new -> old for invariants *)
  let eqs_orig := new_to_old_by_newdefs_list eqs_orig nd_orig in 
  let eqs_opt := new_to_old_by_newdefs_list eqs_opt nd_opt in

  (* 2. update maydiff *)
  let md :=
    List.fold_right
      (fun x acc => 
        if ((List.in_dec id_dec x nd_inter) && (negb (IdExtSetImpl.mem (add_ntag x) md)))
          then IdExtSetImpl.add (add_ntag x) (IdExtSetImpl.remove (add_otag x) acc)
          else IdExtSetImpl.add (add_ntag x) (IdExtSetImpl.add (add_otag x) acc)
      )
      md nd
  in

  (* 3. add the new definitions to the equations *)
  let eqs_orig := add_ntag_phis_to_eqs nd_orig prev_bb eqs_orig lphis in
  let eqs_opt := add_ntag_phis_to_eqs nd_opt prev_bb eqs_opt rphis in

  Some {|
    hint_maydiff := md;
    hint_invariant := 
    {| invariant_original := eqs_orig; invariant_optimized := eqs_opt;
       iso_original := iso_orig; iso_optimized := iso_opt |};
    hint_infrules := ifr |}
  .

(** * Inference Rules Resolve

[infrule_resolve] applies an infrule to [inv].  If the application is
failed, it returns [inv] as it is.  See doc/hint for more details. *)

Definition infrule_resolve (m1 m2:module) (h:insn_hint_t) (inf: infrule_t) : insn_hint_t :=
  infrule_sem m1 m2 inf h.

Definition infrules_resolve (m1 m2:module) (h: insn_hint_t) : insn_hint_t :=
  fold_left
  (fun (h: insn_hint_t) (inf: infrule_t) => infrule_resolve m1 m2 h inf)
  (hint_infrules h) h.


(** * Implications of Hint *)

Definition maydiff_implies (md1 md2: maydiff_t): bool :=
  IdExtSetImpl.subset md1 md2.

Definition eqs_implies (eqs1 eqs2:eqs_t) : bool :=
  EqRegSetImpl.subset (eqs_eq_reg eqs2) (eqs_eq_reg eqs1) &&
  EqHeapSetImpl.subset (eqs_eq_heap eqs2) (eqs_eq_heap eqs1) &&
  NeqRegSetImpl.subset (eqs_neq_reg eqs2) (eqs_neq_reg eqs1).

Definition iso_implies (iso1 iso2:isolated_t) : bool :=
  IdExtSetImpl.subset iso2 iso1.

Definition hint_invariant_implies (from_inv to_inv: invariant_t) : bool :=
  eqs_implies (invariant_original from_inv) (invariant_original to_inv) &&
  eqs_implies (invariant_optimized from_inv) (invariant_optimized to_inv) &&
  iso_implies (iso_original from_inv) (iso_original to_inv) &&
  iso_implies (iso_optimized from_inv) (iso_optimized to_inv).

Definition invariant_implies (from_h to_h:insn_hint_t) : bool :=
  maydiff_implies (hint_maydiff from_h) (hint_maydiff to_h) &&
  hint_invariant_implies (hint_invariant from_h) (hint_invariant to_h).

(* Get next nop id. Each id should be unique in Function. *)
(* Should manually be extracted to proper Ocaml code. *)
Parameter next_nop_id : blocks -> id.

(* Search through blocks with target label, and insert nop. *)
(* Logic adding nop is commented below. *)
(* If there is multiple blocks with target label, it only inserts in FIRST block. *)
Fixpoint insert_nop (target : l * id) (bs : blocks) : option blocks :=
  match bs with
    | nil => Some nil
    | head :: tail =>
      let (target_label, target_id) := target in
      let (head_label, head_stmts) := head in
      if (eq_atom_dec target_label head_label)
      then
        let (head_phis, head_cmds, head_term) := head_stmts in
        (* #1 target_id is in head_phis -> insert as first of cmds *)
        (* #2 target_id is in head_cmds -> insert after that cmd *)
        (* #3 target_id is in head_term or not in anywhere -> None *)
        let idx_ := find_index head_phis
                               (fun x => eq_atom_dec (getPhiNodeID x) target_id) in
        let new_nop := insn_nop (next_nop_id bs) in
        let make_blocks := (fun x => Some ((head_label, x) :: tail)) in
        match idx_ with
            (* #1 *)
          | Some _ => make_blocks (stmts_intro head_phis
                                               (new_nop :: head_cmds)
                                               head_term)
          | None =>
            let idy_ := find_index head_cmds
                                   (fun x => eq_atom_dec (getCmdLoc x) target_id) in
            match idy_ with
              (* #2 *)
              | Some idy => make_blocks (stmts_intro head_phis (insert_at head_cmds (idy + 1) new_nop) head_term)
              (* #3 *)
              | None => None
            end
        end
      else option_map (fun x => head :: x) (insert_nop target tail)
  end.

(* Insert multiple nops in blocks. *)
Definition insert_nops (targets : list (l * id)) (bs : blocks) : option blocks :=
  List.fold_left (fun (s : option blocks) i
                  => mjoin blocks (option_map (fun x => insert_nop i x) s))
                                        targets (Some bs).
