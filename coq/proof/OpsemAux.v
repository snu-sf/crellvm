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
Require Import Inject.

Set Implicit Arguments.


Lemma sInsn_non_call
      conf fdef bb cmd cmds term locals1 allocas1 ecs mem1
      st2 event
      (NONCALL: ~ Instruction.isCallInst cmd)
      (STEP: sInsn
               conf
               (mkState (mkEC fdef bb (cmd::cmds) term locals1 allocas1) ecs mem1)
               st2
               event):
  exists locals2 allocas2 mem2,
    st2 = mkState (mkEC fdef bb cmds term locals2 allocas2) ecs mem2.
Proof.
  inv STEP; eauto. ss. congruence.
Qed.

Lemma inject_decide_nonzero
      TD inv
      val_src decision_src
      val_tgt decision_tgt
      (INJECT: genericvalues_inject.gv_inject inv val_src val_tgt)
      (SRC: decide_nonzero TD val_src decision_src)
      (TGT: decide_nonzero TD val_tgt decision_tgt):
  decision_src = decision_tgt.
Proof.
  inv SRC. inv TGT. unfold GV2int in *.
  destruct val_src; ss. destruct p, v, val_src; ss.
  destruct val_tgt; ss. destruct p, v, val_tgt; ss.
  simtac. inv INJECT. inv H1.
  apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
Qed.

Coercion module_of_conf (conf: Config): module.
Proof.
  destruct conf.
  destruct CurTargetData0.
  econs; eauto.
Defined.

Coercion get_cmds_from_stmts (s: stmts): cmds :=
  let '(stmts_intro _ cs _) := s in cs
.

Coercion get_cmds_from_block (b: block): cmds := b.(snd).

Inductive wf_EC (ec: ExecutionContext): Prop :=
| wf_EC_intro
    (BLOCK: blockInFdefB ec.(CurBB) ec.(CurFunction))
    (* (CMDS: forall c (IN: In c ec.(CurCmds)), insnInBlockB (insn_cmd c) ec.(CurBB)) *)
    (* wf_fdef lemmas, such as "typings_props.wf_fdef__wf_cmd", doesn't use insnInBlockB *)
    (CMDS: sublist ec.(CurCmds) (ec.(CurBB): cmds))
    (TERM: insnInBlockB (insn_terminator ec.(Terminator)) ec.(CurBB))
.
