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


Ltac simtac0 :=
  try match goal with
      | [H: ?a = ?a |- _] => clear H
      | [H: is_true true |- _] => clear H
      | [H: Some _ = Some _ |- _] => inv H
      | [H: context[let (_, _) := ?p in _] |- _] => destruct p
      | [H: negb _ = true |- _] =>
        apply negb_true_iff in H
      | [H: negb _ = false |- _] =>
        apply negb_false_iff in H
      | [H: andb _ _ = true |- _] => apply andb_true_iff in H; destruct H

      | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
        destruct (id_dec a b)
      | [H: proj_sumbool (typ_dec ?a ?b) = true |- _] =>
        destruct (typ_dec a b)
      | [H: proj_sumbool (l_dec ?a ?b) = true |- _] =>
        destruct (l_dec a b)
      | [H: proj_sumbool (fheader_dec ?a ?b) = true |- _] =>
        destruct (fheader_dec a b)
      | [H: proj_sumbool (noret_dec ?a ?b) = true |- _] =>
        destruct (noret_dec a b)
      | [H: proj_sumbool (clattrs_dec ?a ?b) = true |- _] =>
        destruct (clattrs_dec a b)
      | [H: proj_sumbool (varg_dec ?a ?b) = true |- _] =>
        destruct (varg_dec a b)
      | [H: proj_sumbool (layouts_dec ?a ?b) = true |- _] => destruct (layouts_dec a b)
      | [H: proj_sumbool (namedts_dec ?a ?b) = true |- _] => destruct (namedts_dec a b)
      | [H: productInModuleB_dec ?a ?b = left _ |- _] => destruct (productInModuleB_dec a b)

      | [H: context[match ?c with
                    | [] => _
                    | _::_ => _
                    end] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      | [H: context[match ?c with
                    | Some _ => _
                    | None => _
                    end] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      | [H: context[if ?c then _ else _] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      end;
  unfold Debug.debug_print_validation_process, Debug.debug_print in *;
  try subst; ss.

Ltac simtac := repeat simtac0.

(* TODO: m_src, m_tgt, conf_src, conf_tgt *)
Inductive valid_conf
          (m_src m_tgt:module)
          (conf_src conf_tgt:Config): Prop :=
| valid_conf_intro
    (INJECT: inject_conf conf_src conf_tgt)
.

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
