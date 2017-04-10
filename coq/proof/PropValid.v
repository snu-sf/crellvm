Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
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
Require Import Decs.
Require Import Hints.
Require Import Validator.
Require Import GenericValues.
Require Import PropOpsem.
Require Import SimulationLocal.
Require Import Simulation.
Require Import AdequacyLocal.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


Lemma valid_fdef_valid_stmts
      m_src m_tgt fdef_src fdef_tgt fdef_hint l
      phinodes_src cmds_src terminator_src
      phinodes_tgt cmds_tgt terminator_tgt
      stmts_hint
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (SRC: lookupAL stmts (get_blocks fdef_src) l = Some (stmts_intro phinodes_src cmds_src terminator_src))
      (TGT: lookupAL stmts (get_blocks fdef_tgt) l = Some (stmts_intro phinodes_tgt cmds_tgt terminator_tgt))
      (HINT: lookupAL _ fdef_hint l = Some stmts_hint):
  exists inv_term infrules,
    <<CMDS: valid_cmds m_src m_tgt cmds_src cmds_tgt
                       stmts_hint.(Hints.ValidationHint.cmds)
                       stmts_hint.(ValidationHint.invariant_after_phinodes) =
            Some inv_term>> /\
    <<TERM: valid_terminator fdef_hint
                             (Infrules.apply_infrules m_src m_tgt infrules inv_term)
                             m_src m_tgt
                             fdef_src.(get_blocks) fdef_tgt.(get_blocks)
                             l terminator_src terminator_tgt>>.
Proof.
  unfold valid_fdef in FDEF.
  do 2 simtac0.
  destruct (negb (fheader_dec fheader5 fheader0)) eqn:X; ss.
  apply andb_true_iff in FDEF. des. clear FDEF. simtac.
  revert SRC TGT FDEF0.
  generalize blocks0 at 1 3.
  generalize blocks5 at 1 3.
  induction blocks1; i; ss.
  destruct blocks2; [by inv FDEF0|].
  unfold forallb2AL in FDEF0. simtac; eauto.
  - rewrite HINT in COND. inv COND.
    esplits; eauto.
    instantiate (1:= []). ss.
  - rewrite HINT in COND. inv COND.
    esplits; eauto.
Qed.
