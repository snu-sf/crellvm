Require Import sflib.

Require Import vellvm.
Require Import memory_sim.
Require Import genericvalues_inject.

Require Import syntax_ext.
Require Import hints.
Require Import logical_step.

Import Opsem.

Section HintSem.
  Variable (cfg1 cfg2: Config).
  Variable (lc1 lc2: GVMap).
  Variable (Mem1 Mem2: mem).

  Definition eq_gvs (gvs1 gvs2:GenericValue) : Prop :=
    forall gv, (gv @ gvs1 -> gv @ gvs2) /\ (gv @ gvs2 -> gv @ gvs1).

  Definition neq_gvs (gvs1 gvs2:GenericValue) : Prop :=
    forall gv, (gv @ gvs1 -> ~ gv @ gvs2) /\ (gv @ gvs2 -> ~ gv @ gvs1).

  Definition getOperandValueExt (TD:TargetData) (v:value_ext) 
    (lc_old lc_new:GVMap) (globals:GVMap) : option GenericValue :=
  match v with
    | value_ext_id x => lookupALExt lc_old lc_new x
    | value_ext_const c => const2GV TD globals c
  end.

  Definition variable_equivalent (alpha: meminj) (olc1 olc2: GVMap)
    (x: id_ext) : Prop :=
    match lookupALExt olc1 lc1 x, lookupALExt olc2 lc2 x with
      | None, None => True
      | Some gvs1, Some gvs2 => gv_inject alpha gvs1 gvs2
      | _, _ => False
    end.

  Definition maydiff_sem (alpha: meminj) (olc1 olc2: GVMap)
    (md: IdExtSetImpl.t) : Prop :=
    forall x, IdExtSetImpl.mem x md = false -> variable_equivalent alpha olc1 olc2 x.

  Definition BOPEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (op:bop) 
    (bsz:sz) (v1 v2:value_ext) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl, 
           getOperandValueExt TD v2 olc lc gl) with
      | (Some gvs1, Some gvs2) =>
        GenericValueHelper.lift_op2 (mbop TD op bsz) gvs1 gvs2 (typ_int bsz)
      | _ => None
    end.

  Definition FBOPEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (op:fbop) 
    (fp:floating_point) (v1 v2:value_ext) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl, 
           getOperandValueExt TD v2 olc lc gl) with
      | (Some gvs1, Some gvs2) =>
        GenericValueHelper.lift_op2 (mfbop TD op fp) gvs1 gvs2 (typ_floatpoint fp)
      | _ => None
    end.

  Definition TRUNCEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (op:truncop)
    (t1:typ) (v1:value_ext) (t2:typ) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl) with
      | (Some gvs1) => GenericValueHelper.lift_op1 (mtrunc TD op t1 t2) gvs1 t2
      | _ => None
    end.

  Definition EXTEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (op:extop)
    (t1:typ) (v1:value_ext) (t2:typ) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl) with
      | (Some gvs1) => GenericValueHelper.lift_op1 (mext TD op t1 t2) gvs1 t2
      | _ => None
    end.

  Definition CASTEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (op:castop)
    (t1:typ) (v1:value_ext) (t2:typ) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl) with
      | (Some gvs1) => GenericValueHelper.lift_op1 (mcast TD op t1 t2) gvs1 t2
      | _ => None
    end.

  Definition ICMPEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (c:cond) 
    (t:typ) (v1 v2:value_ext) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl, 
           getOperandValueExt TD v2 olc lc gl) with
      | (Some gvs1, Some gvs2) =>
        GenericValueHelper.lift_op2 (micmp TD c t) gvs1 gvs2 (typ_int Size.One)
      | _ => None
    end.

  Definition FCMPEXT (TD:TargetData) (olc lc:GVMap) (gl:GVMap) (c:fcond) 
    (fp:floating_point) (v1 v2:value_ext) : option GenericValue :=
    match (getOperandValueExt TD v1 olc lc gl, 
           getOperandValueExt TD v2 olc lc gl) with
      | (Some gvs1, Some gvs2) =>
        GenericValueHelper.lift_op2 (mfcmp TD c fp) gvs1 gvs2 (typ_int Size.One)
      | _ => None
    end.

  Fixpoint values2GenericValueExt (TD:TargetData) (lv:list (sz * value_ext))
    (olocals locals:GVMap) (globals:GVMap) : option (list GenericValue):=
    match lv with
      | nil => Some nil
      | (_, v) :: lv' =>
        match (getOperandValueExt TD v olocals locals globals) with
          | Some GV =>
            match (values2GenericValueExt TD lv' olocals locals globals) with
              | Some GenericValue => Some (GV::GenericValue)
              | None => None
            end
          | None => None
        end
    end.

  Inductive rhs_ext_value_sem (cfg:Config) (olc lc:GVMap) :
    rhs_ext -> GenericValue -> Prop :=
  | rhs_ext_bop_sem : forall bop sz v1 v2 gvs3,
    BOPEXT (CurTargetData cfg) olc lc (Globals cfg) bop sz v1 v2 = Some gvs3 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_bop bop sz v1 v2) gvs3
  | rhs_ext_fbop_sem : forall fbop fp v1 v2 gvs3,
    FBOPEXT (CurTargetData cfg) olc lc (Globals cfg) fbop fp v1 v2 = Some gvs3 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_fbop fbop fp v1 v2) gvs3
  | rhs_ext_extractvalue_sem:  forall t t' v idxs gvs gvs',
    getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) = Some gvs ->
    extractGenericValue (CurTargetData cfg) t gvs idxs = Some gvs' ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_extractvalue t v idxs t') gvs'
  | rhs_ext_insertvalue_sem : forall t t' v v' idxs gvs gvs' gvs'',
    getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) = Some gvs ->
    getOperandValueExt (CurTargetData cfg) v' olc lc (Globals cfg) = Some gvs' ->
    insertGenericValue (CurTargetData cfg) t gvs idxs t' gvs' = Some gvs'' ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_insertvalue t v t' v' idxs) gvs''
  | rhs_ext_gep_sem : forall inbounds t t' v idxs mp mp' vidxs vidxss,
    getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) = Some mp ->
    values2GenericValueExt (CurTargetData cfg) idxs olc lc (Globals cfg) = Some vidxss ->
    vidxs @@ vidxss ->
    GEP (CurTargetData cfg) t mp vidxs inbounds t' = Some mp' ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_gep inbounds t v idxs t') mp'
  | rhs_ext_trunc_sem : forall truncop t1 t2 v1 gvs2,
    TRUNCEXT (CurTargetData cfg) olc lc (Globals cfg) truncop t1 v1 t2 = Some gvs2 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_trunc truncop t1 v1 t2) gvs2
  | rhs_ext_ext_sem : forall extop t1 t2 v1 gvs2,
    EXTEXT (CurTargetData cfg) olc lc (Globals cfg) extop t1 v1 t2 = Some gvs2 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_ext extop t1 v1 t2) gvs2
  | rhs_ext_cast_sem : forall castop t1 t2 v1 gvs2,
    CASTEXT (CurTargetData cfg) olc lc (Globals cfg) castop t1 v1 t2 = Some gvs2 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_cast castop t1 v1 t2) gvs2
  | rhs_ext_icmp_sem : forall cond t v1 v2 gvs3,
    ICMPEXT (CurTargetData cfg) olc lc (Globals cfg) cond t v1 v2 = Some gvs3 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_icmp cond t v1 v2) gvs3
  | rhs_ext_fcmp_sem : forall fcond fp v1 v2 gvs3,
    FCMPEXT (CurTargetData cfg) olc lc (Globals cfg) fcond fp v1 v2 = Some gvs3 ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_fcmp fcond fp v1 v2) gvs3
  | rhs_ext_select_true_sem : forall v0 v1 v2 t gvs c cond,
    getOperandValueExt (CurTargetData cfg) v0 olc lc (Globals cfg) = Some cond ->
    getOperandValueExt (CurTargetData cfg) v1 olc lc (Globals cfg) = Some gvs ->
    c @ cond ->
    isGVZero (CurTargetData cfg) c = false ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_select v0 t v1 v2) gvs
  | rhs_ext_select_false_sem : forall v0 v1 v2 t gvs c cond,
    getOperandValueExt (CurTargetData cfg) v0 olc lc (Globals cfg) = Some cond ->
    getOperandValueExt (CurTargetData cfg) v2 olc lc (Globals cfg) = Some gvs ->
    c @ cond ->
    isGVZero (CurTargetData cfg) c = true ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_select v0 t v1 v2) gvs
  | rhs_ext_value__sem : forall v gvs,
    getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) = Some gvs ->
    rhs_ext_value_sem cfg olc lc (rhs_ext_value v) gvs.

  Hint Constructors rhs_ext_value_sem.

  Inductive eq_reg_sem (cfg: Config) (olc: GVMap)
    (lc: GVMap) (Mem:mem) (gmax: positive) (x: id_ext) : forall (rhs:rhs_ext), Prop :=
  | eq_reg_sem_value :
    forall gvs gvs' r
      (Hlookup: lookupALExt olc lc x = Some gvs)
      (Hrhs: rhs_ext_value_sem cfg olc lc r gvs')
      (Heqgvs: eq_gvs gvs gvs'),
      eq_reg_sem cfg olc lc Mem gmax x r
  | eq_reg_sem_old_alloca :
    forall gvs xblk xofs
      (Hlookup: lookupALExt olc lc x = Some gvs)
      (Hptr: GV2ptr (CurTargetData cfg) (getPointerSize (CurTargetData cfg)) gvs =
        ret Vptr xblk xofs)
      (Hvalid: (xblk < (Mem.nextblock Mem))%positive)
      (Hgvalid: (gmax < xblk)%positive),
      eq_reg_sem cfg olc lc Mem gmax x rhs_ext_old_alloca.
  Hint Constructors eq_reg_sem.

  Definition eq_heap_sem (cfg: Config) (olc lc: GVMap)
    (Mem: mem) (p:value_ext) (t:typ) (a:align) (v:value_ext) : Prop :=
    match getOperandValueExt (CurTargetData cfg) p olc lc (Globals cfg),
      getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) with
      | Some mps1, Some gvs2 => 
        forall mp (Hmp: mp @ mps1),
          match mload (CurTargetData cfg) Mem mp t a with
            | Some gvs1 => eq_gvs gvs1 gvs2
            | None => False
          end
      | _, _ => False
    end.

  Definition not_undef (gvs: GenericValue) : Prop :=
    match gvs with
      | [(Vundef, _)] => False
      | _ => True
    end.

  Definition no_alias' (gvs1 gvs2: GenericValue) : Prop :=
    memory_props.MemProps.no_alias gvs1 gvs2 /\ not_undef gvs1 /\ not_undef gvs2.

  Definition neq_reg_sem (cfg: Config) (olc lc: GVMap)
    (i: id_ext) (lg: localglobal_t) : Prop :=
    match lookupALExt olc lc i with
      | Some gvs1 => 
        match lg with
          | inl y' => match lookupALExt olc lc y' with
                        | Some gvs2 => (~ eq_gvs gvs1 gvs2) /\
                          no_alias' gvs1 gvs2
                        | None => False
                      end
          | inr g => match lookupAL _ (Globals cfg) g with
                       | Some gvs2 => (~ eq_gvs gvs1 gvs2) /\
                         no_alias' gvs1 gvs2
                       | None => False
                     end
        end
      | None => False
    end.

  Definition eqs_eq_reg_sem (cfg: Config) (olc: GVMap)
    (lc: GVMap) (Mem:mem) (gmax: positive) (e:EqRegSetImpl.t) : Prop :=
    forall x r, EqRegSetImpl.mem (x,r) e -> 
      eq_reg_sem cfg olc lc Mem gmax x r.

  Definition eqs_eq_heap_sem (cfg: Config) (olc: GVMap)
    (lc: GVMap) (Mem:mem) (e:EqHeapSetImpl.t) : Prop :=
    forall p t a v, EqHeapSetImpl.mem (p,t,a,v) e ->
      eq_heap_sem cfg olc lc Mem p t a v.

  Definition eqs_neq_reg_sem (cfg: Config) (olc: GVMap)
    (lc: GVMap) (e:NeqRegSetImpl.t) : Prop :=
    forall x y, NeqRegSetImpl.mem (x,y) e -> 
      neq_reg_sem cfg olc lc x y.

  Definition eqs_sem (cfg: Config) (olc: GVMap) (lc: GVMap)
    (Mem:mem) (gmax: positive) (e:eqs_t) : Prop :=
    eqs_eq_reg_sem cfg olc lc Mem gmax (eqs_eq_reg e) /\
    eqs_eq_heap_sem cfg olc lc Mem (eqs_eq_heap e) /\
    eqs_neq_reg_sem cfg olc lc (eqs_neq_reg e).

  Definition isolated_sem (TD:TargetData) (olc lc: GVMap)
    (li: list mblock) (iso: IdExtSetImpl.t) : Prop :=
    IdExtSetImpl.For_all
    (fun x =>
      (lookupALExt olc lc x = None) \/
      (exists gvp,
        lookupALExt olc lc x = Some gvp /\
        match GV2ptr TD (getPointerSize TD) gvp with
          | ret Vptr b _ => In b li
          | _ => False
        end))
    iso.

  Definition invariant_sem (olc1 olc2: GVMap)
    (gmax: positive) (li1 li2: list mblock)
    (inv: hints.invariant_t) : Prop := 
    eqs_sem cfg1 olc1 lc1 Mem1 gmax (invariant_original inv) /\
    eqs_sem cfg2 olc2 lc2 Mem2 gmax (invariant_optimized inv) /\
    isolated_sem (CurTargetData cfg1) olc1 lc1 li1 (iso_original inv) /\
    isolated_sem (CurTargetData cfg2) olc2 lc2 li2 (iso_optimized inv).

  Definition hint_sem (alpha: meminj) (gmax: positive) (li1 li2: list mblock)
    (h: hints.insn_hint_t) : Prop :=
    exists olc1, exists olc2,
      maydiff_sem alpha olc1 olc2 (hint_maydiff h) /\
      invariant_sem olc1 olc2 gmax li1 li2 (hint_invariant h).

End HintSem.

Notation "$$ cfg1 ; cfg2 ; lc1 ; lc2 ; mem1 ; mem2 ; alpha ; gmax ; li1 ; li2 ; h $$" :=
  (hint_sem cfg1 cfg2 lc1 lc2 mem1 mem2 alpha gmax li1 li2 h)
  (at level 41).

Section AlphaRelated.
  (* li1: isolated heap, which was related to alpha, not alpha' *)
  Definition inject_incr' f1 f2 li1 pi1 li2 pi2 :=
    inject_incr f1 f2 /\
    (forall b, In b li1 -> f1 b = merror -> f2 b = merror) /\
    (forall b, In b pi1 -> f1 b = merror -> f2 b = merror) /\
    (forall b, In b li2 -> (forall sb, f1 sb <> ret (b, 0%Z)) ->
      (forall sb, f2 sb <> ret (b, 0%Z))) /\
    (forall b, In b pi2 -> (forall sb, f1 sb <> ret (b, 0%Z)) ->
      (forall sb, f2 sb <> ret (b, 0%Z))).

  Definition alpha_incr_both alpha mem1 mem2 : Prop :=
    alpha (Mem.nextblock mem1) = ret (Mem.nextblock mem2, 0%Z).

  Definition li_incr_1 li1 mem1 (ocmd1 ocmd2: option cmd) : Prop :=
    match ocmd1, ocmd2 with
      | Some (insn_alloca _ _ _ _), None => List.In (Mem.nextblock mem1) li1
      | _, _ => True
    end.

  Definition li_incr_2 li2 mem2 (ocmd1 ocmd2: option cmd) : Prop :=
    match ocmd1, ocmd2 with
      | None, Some (insn_alloca _ _ _ _) => List.In (Mem.nextblock mem2) li2
      | _, _ => True
    end.

  Inductive allocas_equivalent (alpha: meminj) (li1 li2: list mblock) :
    list mblock -> list mblock -> Prop :=
  | allocas_equivalent_nil :
    allocas_equivalent alpha li1 li2 nil nil
  | allocas_equivalent_ignore_left :
    forall b1 als1' als2
      (Hbin: In b1 li1)
      (Hequiv: allocas_equivalent alpha li1 li2 als1' als2),
      allocas_equivalent alpha li1 li2 (b1::als1') als2
  | allocas_equivalent_ignore_right :
    forall b2 als1 als2'
      (Hbin: In b2 li2)
      (Hequiv: allocas_equivalent alpha li1 li2 als1 als2'),
      allocas_equivalent alpha li1 li2 als1 (b2::als2')
  | allocas_equivalent_map :
    forall b1 b2 als1' als2'
      (Hbin1: ~ In b1 li1)
      (Hbin2: ~ In b2 li2)
      (Hsome: alpha b1 = Some (b2, 0%Z))
      (Hequiv: allocas_equivalent alpha li1 li2 als1' als2'),
      allocas_equivalent alpha li1 li2 (b1::als1') (b2::als2').

  Definition valid_allocas mem1 mem2 als1 als2 : Prop :=
    Forall (fun blk => (blk < Mem.nextblock mem1)%positive) als1 /\
    Forall (fun blk => (blk < Mem.nextblock mem2)%positive) als2 /\
    NoDup als1 /\ NoDup als2.

  Inductive globals_equivalent (alpha: meminj) (gmax: positive) (gl1 gl2: GVMap) : Prop :=
  | globals_equivalent_intro :
    forall gl
      (Hgl1: gl = gl1) (Hgl2: gl = gl2)
      (Hgmax: genericvalues_inject.wf_globals gmax gl),
      globals_equivalent alpha gmax gl1 gl2.

  Inductive valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2 : Prop :=
  | valid_memories_intro :
    forall
      (Hmemi: MoreMem.mem_inj alpha mem1 mem2)
      (Hwf: wf_sb_mi gmax alpha mem1 mem2)

      (Hli1none: forall b, In b li1 -> alpha b = None)
      (Hli2none: forall b, In b li2 -> (forall sb, alpha sb <> ret (b, 0%Z)))
      (Hpi1none: forall b, In b pi1 -> alpha b = None)
      (Hpi2none: forall b, In b pi2 -> (forall sb, alpha sb <> ret (b, 0%Z)))

      (Hli1free: forall b, In b li1 ->
        let (l, h) := Mem.bounds mem1 b in Mem.free mem1 b l h <> merror)
      (Hli2free: forall b, In b li2 ->
        let (l, h) := Mem.bounds mem2 b in Mem.free mem2 b l h <> merror)
      (Hpi1free: forall b, In b pi1 ->
        let (l, h) := Mem.bounds mem1 b in Mem.free mem1 b l h <> merror)
      (Hpi2free: forall b, In b pi2 ->
        let (l, h) := Mem.bounds mem2 b in Mem.free mem2 b l h <> merror)

      (Hlipidisj1: list_disjoint li1 pi1)
      (Hlipidisj2: list_disjoint li2 pi2)

      (Hvli1: Forall (fun b => (b < (Mem.nextblock mem1))%positive) li1)
      (Hvpi1: Forall (fun b => (b < (Mem.nextblock mem1))%positive) pi1)
      (Hvli1: Forall (fun b => (b < (Mem.nextblock mem2))%positive) li2)
      (Hvpi1: Forall (fun b => (b < (Mem.nextblock mem2))%positive) pi2),
      valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2.

End AlphaRelated.

Definition globals_no_alias gl : Prop :=
  forall i1 i2 (Hineq: i1 <> i2) gp1 gp2
    (Hiv1: lookupAL GenericValue gl i1 = ret gp1)
    (Hiv2: lookupAL GenericValue gl i2 = ret gp2),
    no_alias' gp1 gp2.

Definition is_global_ids gids (gl: GVMap) : Prop :=
  Forall (fun gid => lookupAL _ gl gid <> merror) gids.

Inductive hint_sem_insn
  (hint: insn_hint_t)
  (pecs1 pecs2: ECStack) (pns1 pns2: noop_stack_t)
  (pi1 pi2: list mblock) (li1 li2: list mblock) :
  meminj -> positive ->
  OpsemAux.Config -> (ECStack) -> mem -> noop_stack_t -> 
  OpsemAux.Config -> (ECStack) -> mem -> noop_stack_t ->
  Prop :=

| hint_sem_insn_intro :
    forall alpha gmax cfg1 cfg2 mem1 mem2 ec1 ec2 n1 n2
      (Hsem: hint_sem cfg1 cfg2 (Locals ec1) (Locals ec2)
        mem1 mem2 alpha gmax li1 li2 hint)
      (Haequiv: allocas_equivalent alpha li1 li2 (Allocas ec1) (Allocas ec2))
      (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
      (Hvals: valid_allocas mem1 mem2 (Allocas ec1) (Allocas ec2))
      (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2),
      hint_sem_insn hint pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1::pecs1) mem1 (n1::pns1)
      cfg2 (ec2::pecs2) mem2 (n2::pns2).
