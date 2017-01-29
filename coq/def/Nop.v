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

Inductive nop_instr_index : Type :=
  | phi_node : nop_instr_index
  | command_index : nat -> nop_instr_index
.

Definition nop_position : Type := l * nop_instr_index.
  
(* Search through blocks with target label, and insert nop. *)
(* Logic adding nop is commented below. *)
(* If there is multiple blocks with target label, it only inserts in FIRST block. *)
Definition insert_nop (target : nop_position) (bs:blocks): blocks :=
  mapiAL (fun i stmts =>
            let (target_l, pos_i) := target in
            if (eq_atom_dec i target_l)
            then
              match pos_i with
                | phi_node =>
                  let '(stmts_intro ps cmds t) := stmts in
                  let cmds := insert_at 0 (insn_nop (next_nop_id bs)) cmds in
                  (stmts_intro ps cmds t)
                | command_index idx =>
                  let '(stmts_intro phinodes cmds terminator) := stmts in
                  let cmds := insert_at (idx + 1) (insn_nop (next_nop_id bs)) cmds in
                  stmts_intro phinodes cmds terminator
              end
            else stmts
         ) bs.

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
  List.Forall2
    (fun (block_src block_tgt : block) =>
       let (l_src, stmts_src) := block_src in
       let (l_tgt, stmts_tgt) := block_tgt in
       let '(stmts_intro phinodes_src cmds_src terminator_src) := stmts_src in
       let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := stmts_tgt in
       l_src = l_tgt /\
       phinodes_src = phinodes_tgt /\
       nop_cmds cmds_src cmds_tgt /\
       terminator_src = terminator_tgt)
    blocks_src blocks_tgt
.

Inductive nop_fdef: forall (fdef_src fdef_tgt:fdef), Prop :=
| nop_fdef_intro
    header
    blocks_src blocks_tgt
    (BLOCKS: nop_blocks blocks_src blocks_tgt):
    nop_fdef (fdef_intro header blocks_src) (fdef_intro header blocks_tgt)
.

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
  induction NOP; ss.
  econs; eauto.
  destruct x. destruct y. destruct s0. destruct s.
  des. esplits; eauto.
  apply nop_cmds_commutes. eauto.
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

Lemma insert_nop_nop_cmds
      cmds n next_id
  : nop_cmds cmds (insert_at n (insn_nop next_id) cmds).
Proof.
  revert n.
  induction cmds.
  - i. unfold insert_at. ss.
    rewrite util.firstn_nil. ss.
    rewrite util.skipn_nil. ss.
  - i. unfold nop_cmds in *.
    unfold insert_at.
    rewrite <- (firstn_skipn n (a::cmds0)) at 1.
    rewrite util.filter_app.
    rewrite util.filter_app.
    ss.
Qed.

Lemma insert_nop_spec1 nop_position bs:
  nop_blocks bs (insert_nop nop_position bs).
Proof.
  ii. unfold insert_nop.
  unfold lift2_option.
  destruct nop_position.
  remember (next_nop_id bs) as next_id.
  clear Heqnext_id.
  destruct n; simpl.
  - unfold nop_blocks.
    induction bs; ss.
    econs; eauto.
    des_ifs.
  - unfold nop_blocks.
    induction bs; ss.
    econs; eauto.
    des_ifs.
    esplits; eauto.
    apply insert_nop_nop_cmds.
Qed.

Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
  apply nop_blocks_commutes.
  apply insert_nop_spec1.
Qed.
