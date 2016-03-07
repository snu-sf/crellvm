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

(* TODO: how about defining with filters? *)
(* Inductive nop_cmds: forall (cmds_src cmds_tgt:cmds), Prop := *)
(* | nop_cmds_nil: *)
(*     nop_cmds nil nil *)
(* | nop_cmds_cons *)
(*     c cmds_src cmds_tgt *)
(*     (NOP: nop_cmds cmds_src cmds_tgt): *)
(*     nop_cmds (c::cmds_src) (c::cmds_tgt) *)
(* | nop_cmds_src *)
(*     id cmds_src cmds_tgt *)
(*     (NOP: nop_cmds cmds_src cmds_tgt): *)
(*     nop_cmds ((insn_nop id)::cmds_src) cmds_tgt *)
(* | nop_cmds_tgt *)
(*     id cmds_src cmds_tgt *)
(*     (NOP: nop_cmds cmds_src cmds_tgt): *)
(*     nop_cmds cmds_src ((insn_nop id)::cmds_tgt) *)
(* . *)

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

Lemma filter_pop_tail : forall A f (l : list A) x,
                          (filter f (l ++ [x])) =
                          (filter f l) ++ (if (f x) then [x] else nil).
Proof.
  ii.
  induction l0 as [|y l IH];
    destruct (f x) eqn:T; simpl in *; auto; try (rewrite T; auto);
    destruct (f y); simpl in *; try (rewrite <- IH; auto).
Qed.

Lemma nop_cmds_commutes : forall x y,
                            nop_cmds x y -> nop_cmds y x.
Proof.
  unfold nop_cmds.
  induction x; intros; simpl in *; auto.
Qed.

Lemma nop_blocks_commutes : forall x y,
                            nop_blocks x y -> nop_blocks y x.
Proof.
  ii.
  unfold nop_blocks.
  unfold lift2_option.
  destruct (lookupAL stmts y bid) eqn:T.
  generalize dependent y.
  induction x; intros; simpl in *; auto.
  - unfold nop_blocks in H.
    assert(G:=(H bid)).
    simpl in G.
    rewrite T in G.
    inv G.
  - destruct a;
    destruct (bid == l0);
    destruct s, s0;
    destruct (lookupAL stmts x bid) eqn:T2;
    subst; simpl.
    +
    unfold nop_blocks in H.
    assert(G:= (H l0)).
    rewrite T in G.
    simpl in G.
    Set Printing All.
    unfold lift2_option in G.
    Check (l0 == l0).
    Admitted.
    (* { *)
    (*   assert(J: (if l0 == l0 *)
    (*              then Some (stmts_intro phinodes0 cmds0 terminator0) *)
    (*              else lookupAL stmts x l0) = Some (stmts_intro phinodes0 cmds0 terminator0)). *)
    (*   destruct (l0 == l0); auto. unfold not in n. exploit n; auto. intro. inv x0. *)
    (*   unfold lift2_option in G. *)
    (*   simpl in G. *)
    (* } *)



(*     destruct *)
(*       (if l0 == l0 *)
(*          then Some (stmts_intro phinodes0 cmds0 terminator0) *)
(*          else lookupAL stmts x l0) eqn:ABC. *)
(*     cbn in ABC. *)
(*     (* cbv in ABC. *) *)
(*     hnf in ABC. *)

(*     unfold lift2_option in G. *)
(*     (* rewrite ABC in G. *) *)
(*     destruct (l0 == l0) eqn:TT. *)
(*     rewrite TT in G. *)
(*     simpl in G. *)
    
(*     inv ABC. *)
(*     destruct (l0 == l0) eqn:ABC. *)
(*     inv H1. *)
(*     Focus 2. admit. *)
(*     cbv in H1. *)


(*     rewrite J in G. *)
(*     assert(J:= (eq_atom_dec l0 l0)). *)
(*     destruct J. *)
(*     Focus 2. unfold not in n. exploit n; auto. intro. inv x0. *)
(*     splits.  *)
(*     (* + destruct s. destruct s0. splits; auto. *) *)

(*     admit. *)
(*     admit. *)
(*     (* destruct (lookupAL stmts x bid). *) *)
(*     (* destruct s. destruct s1. splits. auto. *) *)
(*   - destruct (lookupAL stmts x bid) eqn:T2. *)
(*     admit. *)
(*     auto. *)
(* Admitted. *)

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

Lemma gggg : forall n m,
               (fix mul (n0 m0 : nat) {struct n0} : nat :=
                  match n0 with
                    | 0%nat => 0%nat
                    | S p => (m0 + mul p m0)%nat
                  end) n m
               =
               match n with
                 | 0%nat => 0%nat
                 | S p => (m +
                           (fix mul (n0 m0 : nat) {struct n0} : nat :=
                  match n0 with
                    | 0%nat => 0%nat
                    | S p => (m0 + mul p m0)%nat
                  end) p m)%nat
               end
.
Proof.
  induction n; intros; auto.
Qed.
(* Lemma ggg : forall n m, Nat.mul n m = 0%nat. *)
(* Proof. *)
(*   intros. *)
(*   unfold Nat.mul. *)
(*   simpl. *)
(* Qed. *)
Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
  apply nop_blocks_commutes.
  apply insert_nop_spec1.
Qed.
  ii. unfold insert_nop. rewrite lookupAL_mapAL.
  destruct (lookupAL _ bs bid); simpl in *; auto.
  destruct s; splits; auto.
  repeat
    match goal with
    | [|- context[match ?c with | Some _ => _ | None => _ end]] => destruct c
    | [|- context[if ?c then _ else _]] => destruct c
    end.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
