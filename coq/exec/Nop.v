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

(* Insert multiple nops in blocks. *)
Definition insert_nops (targets:list id) (bs:blocks): blocks :=
  List.fold_left (flip insert_nop) targets bs.

Definition is_not_nop (c: cmd) :=
  match c with
    | insn_nop _ => false
    |  _ => true
  end.

Definition nop_cmds (cmds_src cmds_tgt:cmds) :=
  filter is_not_nop cmds_src = filter is_not_nop cmds_tgt.

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
  destruct a.
  destruct (i ==a); simpl; auto.
Qed.

Lemma nop_cmds_commutes : forall x y,
                            nop_cmds x y -> nop_cmds y x.
Proof.
  unfold nop_cmds.
  induction x; intros; simpl in *; auto.
Qed.

Lemma lift2_option_commutes :
  forall X f (a b : option X),
    (forall x y, f x y <-> f y x) ->
    lift2_option f a b -> lift2_option f b a.
Proof.
  intros.
  unfold lift2_option.
  destruct a, b; simpl; auto.
  simpl in H0.
  apply H in H0.
  auto.
Qed.

Theorem nop_blocks_commutes : forall x y,
                            nop_blocks x y -> nop_blocks y x.
Proof.
  unfold nop_blocks.
  ii.
  assert(H := H bid).
  apply lift2_option_commutes in H; auto.
  clear H.
  intros.
  destruct x0, y0; splits; auto.
  unfold iff.
  splits; intros H; destruct H as [H [H1 H2]]; splits; auto; try apply nop_cmds_commutes; auto.
Qed.

Lemma insert_nop_spec1 id bs:
  nop_blocks bs (insert_nop id bs).
Proof.
  ii. unfold insert_nop. rewrite lookupAL_mapAL.
  unfold insert_at, nop_cmds.
  destruct (lookupAL stmts bs bid) eqn:LOOKUP2; simpl in *; auto.
  repeat
    match goal with
      | [|- context[match ?c with | Some _ => _ | None => _ end]] => destruct c
      | [|- context[if ?c then _ else _]] => destruct c
      | [|- context[let (_) := ?c in _]] => destruct c
    end;
    simpl; splits; auto.
  - rewrite util.filter_app; simpl.
  clear phinodes5 terminator5 LOOKUP2 bid id.
  rewrite Nat.add_comm.
  simpl.
  rewrite <- util.filter_app.
  rewrite firstn_skipn.
  auto.
  - rewrite util.filter_app.
  simpl. rewrite <- util.filter_app.
  rewrite firstn_skipn. auto.
Qed.

Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
  apply nop_blocks_commutes.
  apply insert_nop_spec1.
Qed.
