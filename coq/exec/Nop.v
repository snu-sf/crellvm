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

(* TODO: how about defining with filters? *)
Inductive nop_cmds: forall (cmds_src cmds_tgt:cmds), Prop :=
| nop_cmds_nil:
    nop_cmds nil nil
| nop_cmds_cons
    c cmds_src cmds_tgt
    (NOP: nop_cmds cmds_src cmds_tgt):
    nop_cmds (c::cmds_src) (c::cmds_tgt)
| nop_cmds_src
    id cmds_src cmds_tgt
    (NOP: nop_cmds cmds_src cmds_tgt):
    nop_cmds ((insn_nop id)::cmds_src) cmds_tgt
| nop_cmds_tgt
    id cmds_src cmds_tgt
    (NOP: nop_cmds cmds_src cmds_tgt):
    nop_cmds cmds_src ((insn_nop id)::cmds_tgt)
.

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
Admitted.

Lemma insert_nop_spec1 id bs:
  nop_blocks bs (insert_nop id bs).
Proof.
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

Lemma insert_nop_spec2 id bs:
  nop_blocks (insert_nop id bs) bs.
Proof.
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
