Require Import sflib.

Require Import vellvm.
Require Import paco.

Import Opsem.


(* TODO: obs_done should have the return value. *)
CoInductive observation : Set :=
| obs_done
| obs_inftau
| obs_event (evt:event) (obs:observation)
.

Definition trace_observation (tr:trace) (obs:observation) : observation :=
  fold_right obs_event obs tr.

Inductive behmatch
          (conf:Config)
          (behave: forall (st:State) (obs:observation), Prop):
  forall (st:State) (obs:observation), Prop :=
| beh_error
    s obs
    (STUCK: stuck_state conf s)
    (NFINAL: s_isFinialState conf s = None):
    behmatch conf behave s obs
| beh_done
    s
    (STUCK: stuck_state conf s)
    (FINAL: s_isFinialState conf s <> None):
    behmatch conf behave s obs_done
| beh_inftau
    s s'
    (ST: sInsn conf s s' E0)
    (INF: behave s' obs_inftau):
    behmatch conf behave s obs_inftau
| beh_evt
    s s' tr obs
    (ST: sInsn conf s s' tr)
    (TR: tr <> E0)
    (INF: behave s' obs):
    behmatch conf behave s (trace_observation tr obs)
.
Hint Constructors behmatch.

Inductive behave_ conf behave s obs: Prop :=
| behave_intro
    s'
    (TAU: sop_star conf s s' E0)
    (MAT: behmatch conf behave s' obs)
.
Hint Constructors behave_.

Definition behave conf : _ -> _ -> Prop := paco2 (behave_ conf) bot2.

Lemma behave_mon conf: monotone2 (@behave_ conf).
Proof.
  ii; destruct IN; destruct MAT; eauto.
Qed.
Hint Resolve behave_mon: paco.

Definition behave_system system main args obs: Prop :=
  forall conf st (INIT: s_genInitState system main args Mem.empty = Some (conf, st)),
    behave conf st obs.
