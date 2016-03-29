Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import sflib.

Require Import TODO.

Set Implicit Arguments.

(* Get next nop id. Each id should be unique in Function. *)
(* Should manually be extracted to proper Ocaml code. *)
Parameter next_nop_id: blocks -> id.

Inductive nop_position : Type :=
  | phi_node_current_block_name : l -> nop_position
  | command_register_name : id -> nop_position
.
(* Search through blocks with target label, and insert nop. *)
(* Logic adding nop is commented below. *)
(* If there is multiple blocks with target label, it only inserts in FIRST block. *)
Definition insert_nop (target : nop_position) (bs:blocks): blocks :=
  mapiAL (fun i stmts =>
            match target with
              | phi_node_current_block_name target_l =>
                if(eq_atom_dec i target_l)
                then let '(stmts_intro ps cmds t) := stmts in
                     let cmds := insert_at 0 (insn_nop (next_nop_id bs)) cmds in
                     (stmts_intro ps cmds t)
                else stmts
              | command_register_name target_id =>
                let '(stmts_intro phinodes cmds terminator) := stmts in
                let cmds_idx :=
                    find_index
                      cmds
                      (fun c => if eq_atom_dec (getCmdLoc c) target_id then true else false)
                in
                let cmds :=
                    match cmds_idx with
                      | None => cmds
                      | Some idx => insert_at (idx + 1) (insn_nop (next_nop_id bs)) cmds
                    end
                in
                stmts_intro phinodes cmds terminator
            end) bs.

Definition insert_nops (targets:list nop_position) (bs:blocks): blocks :=
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

Lemma lookupAL_mapiAL :
  forall (A B : Type)
         (i : atom)
         (f : atom -> A -> B)
         (l : AssocList A),
    lookupAL B (mapiAL f l) i = option_map (f i) (lookupAL A l i).
Proof.
  induction l0; ii; simpl in *; auto.
  destruct a.
  destruct (i0 == a).
  - subst; auto.
  - auto.
Qed.

Lemma insert_nop_spec1 nop_position bs:
  nop_blocks bs (insert_nop nop_position bs).
Proof.
  Ltac insert_nop_ltac :=
    repeat
    match goal with
      | [|- context[match ?c with | Some _ => _ | None => _ end]] =>
        let T := fresh "T" in
        destruct c eqn:T
      | [|- context[if ?c then _ else _]] =>
        let T := fresh "T" in
        destruct c eqn:T
      | [ H : option_map _ (Some _) = None |- _ ] => inv H
      | [ H : option_map _ None = (Some _) |- _ ] => inv H
    end;
    simpl; splits; auto.

  ii. unfold insert_nop.
  unfold lift2_option.
  destruct nop_position; simpl.
  - rewrite lookupAL_mapiAL.
    insert_nop_ltac.
    destruct s, s0.
    simpl in *.
    destruct (eq_atom_dec bid l0); simpl in *; inv T0; splits; auto.
    + unfold nop_cmds. simpl. auto.
    + unfold nop_cmds; auto.
  - rewrite lookupAL_mapiAL.
    insert_nop_ltac.
    destruct s, s0.
    simpl in T0.
    inv T0.
    splits; auto.
    destruct (find_index
                cmds5 (fun c : cmd => if eq_atom_dec (getCmdLoc c) i0 then true else false)) eqn:T2.
    + unfold insert_at.
      unfold nop_cmds.
      rewrite util.filter_app.
      simpl.
      rewrite <- util.filter_app.
      rewrite firstn_skipn.
      auto.
    + unfold nop_cmds.
      auto.
Qed.

Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
  apply nop_blocks_commutes.
  apply insert_nop_spec1.
Qed.
