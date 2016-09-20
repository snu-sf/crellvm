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
Require Import Validator.
Require Import GenericValues.
Require Import Inject.
Require InvMem.
Require InvState.

Set Implicit Arguments.


(* TODO: position *)
Definition get_blocks (f:fdef): blocks :=
  let '(fdef_intro _ blocks) := f in
  blocks.

(* TODO: position *)
Lemma lookupBlockViaLabelFromFdef_spec
      fdef l:
  lookupBlockViaLabelFromFdef fdef l =
  lookupAL _ fdef.(get_blocks) l.
Proof. destruct fdef. ss. Qed.

(* TODO: position *)
Definition ite A (c:bool) (a b:A): A :=
  if c then a else b.

(* TODO: position *)
Lemma ite_spec A c (a b:A):
  ite c a b = if c then a else b.
Proof. ss. Qed.

(* TODO: position *)
Opaque ite.

(* TODO: position *)
Lemma lookupAL_ite
      X (l:AssocList X) decision l1 l2 v1 v2
      (V1: lookupAL _ l l1 = Some v1)
      (V2: lookupAL _ l l2 = Some v2):
  lookupAL _ l (ite decision l1 l2) = Some (ite decision v1 v2).
Proof. destruct decision; ss. Qed.

(* TODO: position *)
Definition return_locals
           (TD:TargetData)
           (retval:option GenericValue)
           (id:id) (noret:noret) (ct:typ)
           (lc:GVMap): option GVsMap :=
  match retval, noret with
  | Some retval, false =>
    match (fit_gv TD ct) retval with
    | Some retval' => Some (updateAddAL _ lc id retval')
    | _ => None
    end
  | _, true => Some lc
  | _, _ => None
  end.

Lemma returnUpdateLocals_spec
      TD id noret clattrs ty va f args Result lc lc' gl:
  returnUpdateLocals TD (insn_call id noret clattrs ty va f args) Result lc lc' gl =
  match getOperandValue TD Result lc gl with
  | Some retval => return_locals TD (Some retval) id noret ty lc'
  | None => None
  end.
Proof.
  unfold returnUpdateLocals.
  destruct (getOperandValue TD Result lc gl); ss.
Qed.

Lemma exCallUpdateLocals_spec
      TD rt noret rid oResult lc:
  exCallUpdateLocals TD rt noret rid oResult lc =
  return_locals TD oResult rid noret rt lc.
Proof. destruct oResult; ss. Qed.

Lemma has_false_False
      conf_src conf_tgt st_src st_tgt invst invmem inv
      (HAS_FALSE: Hints.Invariant.has_false inv)
      (SEM: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv):
  False.
Proof.
  unfold Hints.Invariant.has_false in *.
  unfold Hints.Invariant.false_encoding in *.
  inv SEM. inv SRC.
  apply Exprs.ExprPairSet.mem_2 in HAS_FALSE.
  specialize (LESSDEF _ HAS_FALSE).
  clear -LESSDEF.
  unfold InvState.Unary.sem_lessdef in *. ss.
  admit.
Admitted.
