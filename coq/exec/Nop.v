Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import GenericValues.
Require Import MemInvariants.
Require Import SimulationLocal.

Set Implicit Arguments.

(* Get next nop id. Each id should be unique in Function. *)
(* Should manually be extracted to proper Ocaml code. *)
Parameter next_nop_id: blocks -> id.

(* Search through blocks with target label, and insert nop. *)
(* Logic adding nop is commented below. *)
(* If there is multiple blocks with target label, it only inserts in FIRST block. *)
Definition insert_nop (target:id) (bs:blocks): blocks :=
  map
    (fun stmts =>
       let '(stmts_intro phinodes cmds terminator) := stmts in

       (* after a phinode *)
       let phinodes_valid :=
           List.existsb
             (fun phinode => if eq_atom_dec (getPhiNodeID phinode) target then true else false)
             phinodes
       in
       let cmds :=
           if phinodes_valid
           then insert_at 0 (insn_nop (next_nop_id bs)) cmds
           else cmds
       in

       (* after a command *)
       let cmds_idx :=
           find_index
             cmds
             (fun c => if eq_atom_dec (getCmdLoc c) target then true else false)
       in
       let cmds :=
           match cmds_idx with
           | None => cmds
           | Some idx => insert_at (idx + 1) (insn_nop (next_nop_id bs)) cmds
           end
       in

       stmts_intro phinodes cmds terminator)
    bs.

Definition insert_nops (targets:list id) (bs:blocks): blocks :=
  List.fold_left (flip insert_nop) targets bs.

Definition is_nop (c: cmd) :=
  match c with
    | insn_nop _ => true
    |  _ => false
  end.

Definition nop_cmds (cmds_src cmds_tgt:cmds) :=
  filter (negb <*> is_nop) cmds_src = filter (negb <*> is_nop) cmds_tgt.

Definition nop_blocks (blocks_src blocks_tgt:blocks): Prop :=
  forall bid,
    lift2_option
      (fun stmts_src stmts_tgt =>
         let '(stmts_intro phinodes_src cmds_src terminator_src) := stmts_src in
         let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := stmts_tgt in
         phinodes_src = phinodes_tgt /\
         nop_cmds cmds_src cmds_tgt /\
         terminator_src = terminator_tgt)
    (lookupAL _ blocks_src bid)
    (lookupAL _ blocks_tgt bid).

Lemma lookupAL_mapAL A B i (f:A -> B) l:
  lookupAL _ (map f l) i = option_map f (lookupAL _ l i).
Proof.
  induction l; simpl in *; auto.
  destruct a. destruct (i == a); auto.
Qed.

Lemma nop_cmds_commutes
      x y (NOP: nop_cmds x y):
  nop_cmds y x.
Proof.
  unfold nop_cmds.
  induction x; intros; simpl in *; auto.
Qed.

Lemma nop_blocks_commutes
      x y (NOP: nop_blocks x y):
  nop_blocks y x.
Proof.
  ii. specialize (NOP bid).
  destruct (lookupAL _ x bid), (lookupAL _ y bid);
    simpl in *; try congruence.
  destruct s, s0. des. splits; auto.
  apply nop_cmds_commutes. auto.
Qed.

Lemma insert_nop_spec1 id bs:
  nop_blocks bs (insert_nop id bs).
Proof.
  ii. unfold insert_nop. rewrite lookupAL_mapAL.
  unfold insert_at, nop_cmds.
  destruct (lookupAL stmts bs bid); simpl in *; auto.
  destruct s. splits; auto.
  repeat
    match goal with
      | [|- context[match ?c with | Some _ => _ | None => _ end]] => destruct c
      | [|- context[if ?c then _ else _]] => destruct c
    end;
    simpl; splits; auto.
  - rewrite util.filter_app; simpl.
    rewrite <- util.filter_app; simpl.
    rewrite firstn_skipn. auto.
  - rewrite util.filter_app; simpl.
    rewrite <- util.filter_app; simpl.
    rewrite firstn_skipn. auto.
Qed.

Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
  apply nop_blocks_commutes.
  apply insert_nop_spec1.
Qed.

Inductive nop_fdef: forall (fdef_src fdef_tgt:fdef), Prop :=
| nop_fdef_intro
    header
    blocks_src blocks_tgt
    (BLOCKS: nop_blocks blocks_src blocks_tgt):
    nop_fdef (fdef_intro header blocks_src) (fdef_intro header blocks_tgt)
.

Inductive nop_state_sim
          stack0_src stack0_tgt (inv:Relational.t):
  forall (idx:nat) (st_src st_tgt:State), Prop :=
| nop_state_sim_intro
    fdef_src fdef_tgt
    l s_src s_tgt
    cmds_src cmds_tgt term locals_src locals_tgt allocas_src allocas_tgt
    mem_src mem_tgt
    (FDEF: nop_fdef fdef_src fdef_tgt)
    (CMDS: nop_cmds cmds_src cmds_tgt)
    (LOCALS_TODO: True)
    (ALLOCAS_TODO: True)
    (MEM_TODO: True):
    nop_state_sim
      stack0_src stack0_tgt inv
      (length cmds_tgt)
      (mkState
         (mkEC fdef_src (l, s_src) cmds_src term locals_src allocas_src)
         stack0_src
         mem_src)
      (mkState
         (mkEC fdef_tgt (l, s_tgt) cmds_tgt term locals_tgt allocas_tgt)
         stack0_tgt
         mem_tgt)
.

Lemma locals_init
      inv la gvs_tgt
    args_src args_tgt
    conf_src conf_tgt
    (CONF_TODO : True)
    (ARGS: list_forall2 (GVs.inject inv.(Relational.alpha)) args_src args_tgt)
    (LOCALS : initLocals (CurTargetData conf_tgt) la args_tgt = Some gvs_tgt) :
  initLocals (CurTargetData conf_src) la args_src =
  initLocals (CurTargetData conf_tgt) la args_tgt.
Proof.
Admitted.

Lemma nop_init
      conf_src conf_tgt
      stack0_src stack0_tgt
      header
      blocks_src blocks_tgt
      args_src args_tgt
      mem_src mem_tgt
      inv
      ec_tgt
      (NOP_FDEF: nop_fdef (fdef_intro header blocks_src)
                          (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt))
      (ARGS: list_forall2 (GVs.inject inv.(Relational.alpha)) args_src args_tgt)
      (MEM_TODO: True)
      (CONF_TODO: True)
      (INIT: init_fdef conf_tgt (fdef_intro header blocks_tgt) args_tgt ec_tgt):
  exists ec_src idx,
    init_fdef conf_src (fdef_intro header blocks_src) args_src ec_src /\
    nop_state_sim
      stack0_src stack0_tgt
      inv idx
      (mkState ec_src stack0_src mem_src)
      (mkState ec_tgt stack0_tgt mem_tgt).
Proof.
  inv INIT.
  inv NOP_FDEF.
  destruct header.
  destruct blocks_src, blocks_tgt; inv NOP_FIRST_MATCHES; try inv ENTRY.
  inv FDEF.
  destruct b. destruct s.
  simpl in H0. subst.
  eexists.
  eexists.
  splits.
  - econs; simpl; eauto. rewrite <- LOCALS. eapply locals_init; eauto.
  - assert(G:=BLOCKS l').
    simpl in G.
    match goal with | [H: context[if ?cond then Some _ else _] |- _] => destruct cond eqn:T end.
    Focus 2.
    + unfold not in n. contradiction n. auto.
    + simpl in G.
      destruct G as [nop_phi [nop_cmd nop_term]].
      subst. simpl.
      econs; eauto.
      econs; eauto.
Qed.

Lemma double_neg : forall A : Prop, ~ ~ A -> A.
Proof.
  unfold not; intros.
  assert(G:ClassicalFacts.excluded_middle).
  unfold ClassicalFacts.excluded_middle.
  intro.
(*   apply ClassicalFacts.prop_degeneracy in A0. *)
(*   apply ClassicalFacts.excluded_middle in A0. *)

(*   ClassicalFacts.prop_degen_em: *)
(*   ClassicalFacts.prop_degeneracy -> ClassicalFacts.excluded_middle *)
(* ClassicalFacts.prop_ext_em_degen: *)
(*   ClassicalFacts.prop_extensionality -> *)
(*   ClassicalFacts.excluded_middle -> ClassicalFacts.prop_degeneracy *)
(* ClassicalFacts.excluded_middle_Godel_Dummett: *)
(*   ClassicalFacts.excluded_middle -> ClassicalFacts.GodelDummett *)

(*   exploit (ClassicalFacts.excluded_middle A). *)
  Admitted.

Lemma double_neg2 : forall A : Prop, A -> ~ ~ A.
Proof.
  unfold not; intros.
  apply H0 in H.
  inv H.
Qed.
(* sim_local : *)
(* Config -> *)
(* Config -> ECStack -> ECStack -> Relational.t -> nat -> State -> State -> Prop *)

(* Argument scopes are [_ _ _ _ _ nat_scope _ _] *)
(* sim_local is transparent *)
(* Expands to: Constant LLVMBerry.exec.SimulationLocal.sim_local *)


(* _sim_local : *)
(* Config -> *)
(* Config -> *)
(* (ECStack -> ECStack -> Relational.t -> nat -> State -> State -> Prop) -> *)
(* ECStack -> ECStack -> Relational.t -> nat -> State -> State -> Prop *)

(* Argument scopes are [_ _ _ _ _ _ nat_scope _ _] *)
(* Expands to: Inductive LLVMBerry.exec.SimulationLocal._sim_local *)


(* nop_state_sim : *)
(* ECStack -> ECStack -> Relational.t -> nat -> State -> State -> Prop *)

(* Argument scopes are [_ _ _ nat_scope _ _] *)
(* Expands to: Inductive Top.nop_state_sim *)


Inductive trivial_state_sim (stack0_src stack0_tgt : ECStack) (inv : Relational.t)
          : nat -> State -> State -> Prop :=
  trivial_state_sim_intro :
    forall same_state
      (SRC_STACK : ECS same_state = stack0_src)
      (TGT_STACK : ECS same_state = stack0_tgt),
    trivial_state_sim stack0_src stack0_tgt inv
                      (length (CurCmds (EC same_state)))
                      same_state same_state.

Lemma trivial_step
      conf_src conf_tgt:
  trivial_state_sim <6= (sim_local conf_src conf_tgt).
Proof.
  pcofix CIH. i.
  inv PR.
  pfold; simpl.
 
  destruct x5. (* eqn:T. *)
  destruct EC0. (* eqn:T2. *)
  destruct CurCmds0. (* eqn:T3. *)
  destruct conf_tgt, conf_src.
  -
    destruct Terminator0. (* eqn:T4. *)
    + (* insn_return *)
      eapply _sim_local_return; repeat (simpl; eauto).
      admit. admit. admit.
    + (* insn_return_void *)
      eapply _sim_local_return_void; repeat (simpl; eauto).
    + (* insn_br *)
      eapply _sim_local_step; repeat (simpl; eauto).
      unfold stuck_state, not.
      apply double_neg2.
      repeat eexists.
      eapply sBranch; simpl; eauto.
      admit. admit. admit.

      ii.
      destruct event.
      *
        inv STEP.
        eexists.
        eexists.
        eexists.
        eexists.
        eexists.
        splits.
        econs; simpl; eauto.
        econs; simpl; eauto.
        eapply sBranch; simpl; eauto.
        admit. admit. admit.
        econs; simpl; eauto.

        pfold; simpl.
    +
      
        | _sim_local_return : forall (st2_src : State) (id2_src : id)
                          (typ2_src : typ) (ret2_src : value) 
                          (id1_tgt : id) (typ1_tgt : typ) 
                          (ret1_tgt : value)
                          (retval2_src retval1_tgt : GenericValue),
                        sop_star conf_src st1_src st2_src events.E0 ->
                        CurCmds (EC st2_src) = [] ->
                        CurCmds (EC st1_tgt) = [] ->
                        Terminator (EC st2_src) =
                        insn_return id2_src typ2_src ret2_src ->
                        Terminator (EC st1_tgt) =
                        insn_return id1_tgt typ1_tgt ret1_tgt ->
                        typ2_src = typ1_tgt ->
                        ECS st2_src = stack0_src ->
                        ECS st1_tgt = stack0_tgt ->
                        True ->
                        getOperandValue (CurTargetData conf_src) ret2_src
                          (Locals (EC st2_src)) (Globals conf_src) =
                        Some retval2_src ->
                        getOperandValue (CurTargetData conf_tgt) ret1_tgt
                          (Locals (EC st1_tgt)) (Globals conf_tgt) =
                        Some retval1_tgt ->
                        GVs.inject (Relational.alpha inv1) retval2_src
                          retval1_tgt ->
                        _sim_local conf_src conf_tgt sim_local stack0_src
                          stack0_tgt inv1 idx1 st1_src st1_tgt

                          ECS0 = x0
                                   subgoal 2 (ID 1106) is:
                          ECS0 = x1


    +
    econs; simpl; eauto.
    unfold stuck_state, not; i.
    inv H.
    inv H0.
    inv H.
    (* (sInsn_cases (inversion H) Case). *)
  -
  eapply _sim_local_step; simpl; eauto.
  unfold stuck_state, not.
  apply double_neg2.

  repeat eexists.


Lemma nop_step
      conf_src conf_tgt:
  nop_state_sim <6= (sim_local conf_src conf_tgt).
Proof.
  pcofix CIH. i.
  inv PR.
  pfold; simpl.
  
  (* destruct (cmds_src) eqn:EMPTY_CMD. *)
  (* - (* empty_src *) *)
  (*   subst; simpl. *)
  (*   destruct (cmds_tgt) eqn:EMPTY_TGT. *)
  (*   + *)
  (*     destruct term. *)
  (*     * *)
  (*       eapply _sim_local_return; simpl; eauto. *)
  (*       simpl; eauto. *)
  (*       simpl; eauto. *)
  (*       admit. *)
  (*       admit. *)
  (*       admit. *)
  (*     * *)
  (*       (* return_void *) *)
  (*       eapply _sim_local_return_void; simpl; eauto. *)
  (*       simpl; eauto. *)
  (*     * *)
  (*       (* insn_br *) *)
  (*       destruct conf_tgt. *)
  (*       destruct value5. *)
  (*       eapply _sim_local_step; simpl; eauto. *)
  (*       unfold stuck_state, not. *)
  (*       apply double_neg2. *)
  (*       repeat eexists. *)
  (*       eapply sBranch; simpl; eauto. *)
  (*       admit. *)
  (*       admit. *)
  (*       admit. *)

  (*       admit. *)
  (*       admit. *)
  (*     * (* insn_br_uncond *) *)
  (*       admit. *)
  (*     * (* insn_unreachable *) *)
  (*       admit. *)
  (*   + *)
  (* - *)
  
  destruct (forallb is_nop cmds_tgt) eqn:ALL_NOP.
  -
    assert(G:(forallb is_nop cmds_src)) by admit.
    destruct cmds_src eqn:SRC_EMPTY;
      destruct cmds_tgt eqn:TGT_EMPTY;
      subst; simpl.
    +
      destruct term.
      *
        (* return *)
        destruct value5;
        eapply _sim_local_return; simpl; eauto; unfold Terminator; simpl; eauto.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
      *
        (* return_void *)
        eapply _sim_local_return_void; simpl; eauto; unfold Terminator; simpl; eauto.
      *
        (* br *)
        admit.
      *
        destruct conf_tgt, conf_src.
        
        eapply _sim_local_step; simpl; eauto.
        apply double_neg2.
        repeat eexists.
        eapply sBranch_uncond; simpl; eauto.
        admit. (* <___________________ not able *)
        admit.

        intros.
        repeat eexists.
        eapply sop_star_nil; simpl; eauto.
        econs; eauto.
        instantiate (1:=st3_tgt).
        eapply sBranch_uncond.
      *
        (* br_uncond *)
        *
        (* br_unreachable *)
  -
    
    

Lemma nop_sim
      conf_src conf_tgt
      header
      blocks_src blocks_tgt
      (NOP: nop_fdef (fdef_intro header blocks_src) (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt)):
  sim_func conf_src conf_tgt (fdef_intro header blocks_src) (fdef_intro header blocks_tgt).
Proof.
  ii.
  exploit nop_init; eauto. i. des.
  eexists _, _. splits; eauto.
  apply nop_step. eauto.
Qed.
