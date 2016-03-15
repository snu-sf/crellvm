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
Require Import MemInv.
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
    (ARGS: list_forall2 (GVs.inject inv.(Relational.inject)) args_src args_tgt)
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
      (ARGS: list_forall2 (GVs.inject inv.(Relational.inject)) args_src args_tgt)
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

Inductive inject_EC (inv:Relational.t): forall (ec_src ec_tgt:ExecutionContext), Prop :=
| inject_EC_intro
    fdef block cmds terminator
    locals1 locals2
    allocas1 allocas2
    (LOCALS: True)
    (ALLOCAS: True):
    inject_EC
      inv
      (mkEC fdef block cmds terminator locals1 allocas1)
      (mkEC fdef block cmds terminator locals2 allocas2)
.

Inductive identity_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (inv:Relational.t):
  forall (idx:nat) (st_src st_tgt:State), Prop :=
| identity_state_sim_intro
    state_src state_tgt
    (EC_INJECT: inject_EC inv state_src.(EC) state_tgt.(EC))
    (STACK_SRC : state_src.(ECS) = stack0_src)
    (STACK_TGT : state_tgt.(ECS) = stack0_tgt)
    (MEM_INJECT: Relational.sem conf_src conf_tgt state_src.(Mem) state_tgt.(Mem) inv):
    identity_state_sim
      conf_src conf_tgt
      stack0_src stack0_tgt inv
      (length state_tgt.(EC).(CurCmds))
      state_src state_tgt.

Inductive status :=
| status_call
| status_return
| status_return_void
| status_step
.

(* TODO *)
Definition get_status (ec:ExecutionContext): status :=
  match ec.(CurCmds) with
  | c::_ =>
    match c with
    | insn_call _ _ _ _ _ _ _ => status_call
    | _ => status_step
    end
  | nil =>
    match ec.(Terminator) with
    | insn_return _ _ _ => status_return
    | insn_return_void _ => status_return_void
    | _ => status_step
    end
  end.

Lemma get_status_call_inv ec
      (CALL: get_status ec = status_call):
  exists id noret attrs ty varg f args cmds,
    ec.(CurCmds) = (insn_call id noret attrs ty varg f args)::cmds.
Proof.
  destruct ec. unfold get_status in *. simpl in *.
  destruct CurCmds0.
  - destruct Terminator0; inv CALL.
  - destruct c; inv CALL.
    eexists _, _, _, _, _, _, _, _. eauto.
Qed.

(* TODO *)
Definition is_error (st:State): bool :=
  false.

Lemma identity_step:
  identity_state_sim <8= sim_local.
Proof.
  intros conf_src conf_tgt stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM.
  pfold. inv SIM.

  destruct (is_error st_tgt) eqn:ERROR.
  { eapply _sim_local_error.
    - econs 1.
    - admit.
  }

  destruct st_src as [ec_src ecs_src mem_src].
  destruct st_tgt as [ec_tgt ecs_tgt mem_tgt].

  destruct (get_status ec_tgt) eqn:TGT.
  - inv EC_INJECT. simpl in *. subst.
    apply get_status_call_inv in TGT. des. simpl in *. subst.
    eapply _sim_local_call;
      repeat (simpl in *; eauto).
    + admit. (* locals inject *)
    + admit. (* no error *)
    + admit. (* locals inject *)
    + admit. (* locals inject *)
    + admit. (* no error *)
    + admit. (* locals inject *)
    + i. eexists. right. apply CIH.
      econs; simpl; eauto.
      admit. (* inject_EC *)
  - eapply _sim_local_return.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - eapply _sim_local_return_void.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - eapply _sim_local_step.
    + admit.
    + i. eexists _, _, _, _, _. splits.
      * admit.
      * admit.
      * admit.
      * right. apply CIH.
        admit.
Admitted.

Lemma identity_init
      conf_src conf_tgt
      stack_src stack_tgt
      mem_src mem_tgt
      same_fdef
      args_src args_tgt
      inv
      ec_tgt
      (ARGS: list_forall2 (GVs.inject inv.(Relational.inject)) args_src args_tgt)
      (INIT: init_fdef conf_tgt same_fdef args_tgt ec_tgt):
  exists ec_src idx,
    init_fdef conf_src same_fdef args_src ec_src /\
    identity_state_sim
      conf_src conf_tgt
      stack_src stack_tgt
      inv idx
      (mkState ec_src stack_src mem_src)
      (mkState ec_tgt stack_tgt mem_tgt).
Proof.
  inv INIT.
  do 2 eexists.
  splits.
  econs; eauto. erewrite locals_init; eauto.
  eapply identity_state_sim_intro; eauto.
  - admit.
  - admit.
Admitted.

Lemma identity_sim
      conf_src conf_tgt
      fdef_same :
  sim_func conf_src conf_tgt fdef_same fdef_same.
Proof.
  ii.
  exploit identity_init; eauto.
  ii.
  inv x0. inv H. inv H0. inv H1.
  do 2 eexists.
  splits; eauto.
  apply identity_step.
  eapply identity_state_sim_intro; simpl; eauto.
Qed.

Lemma nop_step
      conf_src conf_tgt:
  nop_state_sim <6= (sim_local conf_src conf_tgt).
Proof.
Admitted.

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
