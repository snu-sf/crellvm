Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import syntax_ext.
Require Import validator_aux.
Require Import validator.
Require Import validator_props.
Require Import logical_step.
Require Import state_props.
Require Import hints.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import syntax_ext.
Require Import basic_const_inject.

Require Import hint_sem_props_implies.
Require Import hint_sem_props_resolve_defs.
Require Import hint_sem_props_resolve.
Require Import hint_sem_props_proceed.
Require Import hint_sem_props_proceed_call.
Require Import hint_sem_props_proceed_branch.

Require Import paco.

Import Opsem.


(** observation **)
CoInductive observation : Set :=
| obs_done
| obs_inftau
| obs_event (evt:event) (obs:observation).

Definition trace_observation (tr:trace) (obs:observation) : observation :=
  fold_right obs_event obs tr.


(** physical behavior **)
Inductive behmatch (cfg:Config) behave : (@State DGVs) -> observation -> Prop :=
| beh_err s obs
  (STUCK: stuck_state cfg s)
  (NFINAL: s_isFinialState cfg s = None)
  : behmatch cfg behave s obs
| beh_done s
  (STUCK: stuck_state cfg s)
  (FINAL: s_isFinialState cfg s <> None)
  : behmatch cfg behave s obs_done
| beh_inftau s s'
    (ST: sInsn cfg s s' E0)
    (INF: behave s' obs_inftau : Prop)
  : behmatch cfg behave s obs_inftau
| beh_evt s s' tr obs
    (ST: sInsn cfg s s' tr)
    (TR: tr <> E0)
    (INF: behave s' obs : Prop)
  : behmatch cfg behave s (trace_observation tr obs)
.
Hint Constructors behmatch.

Inductive behave_ cfg behave s obs : Prop :=
behave_intro s'
  (MAT: behmatch cfg behave s' obs)
  (TAU: sop_star cfg s s' E0).
Hint Constructors behave_.

Definition behave cfg : _ -> _ -> Prop := paco2 (behave_ cfg) bot2.

Lemma behave_mon cfg: monotone2 (@behave_ cfg).
Proof.
  ii; destruct IN; destruct MAT; eauto.
Qed.
Hint Resolve behave_mon: paco.

Inductive behave_prog m main args obs : Prop :=
| _behave_prog :
  forall cfg ist
    (Hinit: s_genInitState [m] main args Mem.empty = Some (cfg, ist))
    (Hobs: behave cfg ist obs),
    behave_prog m main args obs.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
