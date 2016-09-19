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
Require Import Validator.
Require Import Postcond.
Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.

Definition locals_equiv_except (ids:IdTSet.t) (locals0 locals1:GVsMap): Prop :=
  forall id (NOT_IN: ~ IdTSet.In (Tag.physical, id) ids),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Inductive state_equiv_except (ids:IdTSet.t) (st0 st1: State): Prop :=
| state_eq_except_intro
    (MEM: st0.(Mem) = st1.(Mem))
    (LOCALS: locals_equiv_except ids st0.(EC).(Locals) st1.(EC).(Locals))
.

(* TODO: not sure if needed *)
(* Lemma forget_unary_reduce_lessdef *)
(*       s inv0 inv1 ld *)
(*       (FORGET: Forget.unary s inv0 = inv1) *)
(*       (MEM: ExprPairSet.mem ld inv1.(Invariant.lessdef)): *)
(*   <<MEM: ExprPairSet.mem ld inv0.(Invariant.lessdef)>>. *)
(* Proof. *)
(*   (* unfold Forget.unary in *. *) *)
(* Admitted. *)

Lemma sem_inject_equiv_except
      ids st0 st1 invst id val
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_idT st0 invst id = Some val)
      (NOTIN: ~ IdTSet.In id ids)
  :
    <<STATE: InvState.Unary.sem_idT st1 invst id = Some val>>.
Proof.
  unfold InvState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  destruct id.
  destruct t; ss.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma forget_unary_sound
      ids st0 st1
      conf invst invmem inv0 
      (EQUIV : state_equiv_except ids st0 st1)
      (STATE : InvState.Unary.sem conf st0 invst invmem inv0)
  :
    <<STATE: InvState.Unary.sem conf st1 invst invmem (Forget.unary ids inv0)>>.
Proof.
  inv STATE.
  (* econs. *)
  (* - *)
Admitted.

Lemma forget_sound
      conf_src st_src0
      conf_tgt st_tgt0
      st_src1 st_tgt1
      invst invmem inv0
      s_src s_tgt
      (EQUIV_SRC: state_equiv_except s_src st_src0 st_src1)
      (EQUIV_TGT: state_equiv_except s_tgt st_tgt0 st_tgt1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src0 st_tgt0
                               invst invmem inv0):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src1 st_tgt1
                            invst invmem (Forget.t s_src s_tgt inv0)>>.
Proof.
  inv STATE.
  econs.
  - eapply forget_unary_sound; eauto.
  - eapply forget_unary_sound; eauto.
  - i. ss.
    admit. (* forget maydiff *)
Admitted.
