Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.
Require Import RndHoare.history_anti_chain.
Require Import RndHoare.random_variable.
Require Import RndHoare.meta_state.
Require Import RndHoare.pstate_stream_lemmas.
Require Import RndHoare.pstate_stream_limit.
Require Import RndHoare.probabilistic_pred.
Require RndHoare.cut_stream. Import RndHoare.cut_stream.CutStream.
Require Import RndHoare.imperative.
Require Import RndHoare.normal_imperative.

Import Randomized.

Section GuardedOAccess.

Context {imp: Imperative} {sss: SmallStepSemantics}.

Definition guarded_omega_access {O1 O2: RandomVarDomain} (ban_command: cmd) (src: ProgState O1 (cmd * state)) (dst: ProgState O2 (cmd * state)): Prop :=
  exists (l: execution_trace),
    (forall n h, step_domains l (S n) h -> ~ exists sigma, trace_states l (S n) h (Terminating _ (ban_command, sigma))) /\
    RandomVar_global_equiv (trace_states l 0) src /\
    RandomVar_global_equiv (limit (trace_states l) (step_domains l)) dst.

End GuardedOAccess.

Section NormalImpLemma.

Import Normal.

Context {Nimp: Normal.Imperative} {Nsss: Normal.SmallStepSemantics}.

Lemma guarded_skip_access_is_no_guard: forall {O1 O2: RandomVarDomain} (src: ProgState O1 (cmd * state)) (dst: ProgState O2 (cmd * state)), guarded_omega_access Sskip src dst <-> omega_access src dst.
Admitted.

Lemma guarded_seq_const_access: forall {O1 O2: RandomVarDomain} (c1 c2: cmd) (src: ProgState O1 state) (dst: ProgState O2 state),
  guarded_omega_access
   (Ssequence Sskip c2)
   (ProgState_pair_left (Ssequence c1 c2) src)
   (ProgState_pair_left (Ssequence Sskip c2) dst) ->
  omega_access
   (ProgState_pair_left c1 src)
   (ProgState_pair_left Sskip dst).
Admitted.

Lemma guarded_skip_access: forall {O1 O2: RandomVarDomain} (c: cmd) (src: ProgState O1 state) (dst: ProgState O2 state),
  guarded_omega_access
    Sskip
   (ProgState_pair_left (Ssequence Sskip c) src)
   (ProgState_pair_left Sskip dst) ->
  omega_access
   (ProgState_pair_left c src)
   (ProgState_pair_left Sskip dst).
Admitted.

(*
Lemma guarded_loop_0: forall {O1 O2: RandomVarDomain} (b: expr) (c: cmd) (src: ProgState O1 state) (dst: ProgState O2 state),
  guarded_omega_access
   (Swhile b c)
   (ProgState_pair_left (Swhile b c) src)
   (ProgState_pair_left_choice (PreImage_MSet (eval_bool b) (Swhile b c) Sskip dst).
*)

End NormalImpLemma.

Section SubTrace.

Context {imp: Imperative} {sss: SmallStepSemantics}.

Variable (s: execution_trace) (filter: nat -> cmd).

Definition pfilter (m: nat) : measurable_set (MetaState (cmd * state)) := TerminatingP_MSet (LeftP_MSet (eq (filter m))).

Definition sub_trace (m: nat): execution_trace.
  refine (Build_execution_trace
           (sub_domain pfilter (trace_domain s) (trace_states s) (step_domains s) m)
           (sub_state pfilter (trace_domain s) (trace_states s) (step_domains s) m)
           (sub_dir pfilter (trace_domain s) (trace_states s) (step_domains s) m) _).
  intros r.
  pose proof sub_step_sound pfilter (trace_domain s) (trace_states s) (step_domains s) m r.
  hnf; intros.
  specialize (H h H0).
  destruct H as [n [? [? ?]]].
  pose proof step_sound s n.
  pose proof H3 h H.
  destruct H4.
  apply (Build_local_step h _ _ _ _ cs1 Omega cs2); auto.
  + rewrite (H1 _); auto.
  + intros h' p.
    rewrite <- sound2.
    apply H2.
    apply prefix_app_history.
Defined.

Definition main_domain: RandomVarDomainStream := main_domain pfilter (trace_domain s) (trace_states s) (step_domains s).

Definition main_state: ProgStateStream main_domain (cmd * state) := main_state pfilter (trace_domain s) (trace_states s) (step_domains s).

Definition main_dir: ConvergeDir main_state := main_dir pfilter (trace_domain s) (trace_states s) (step_domains s).

Lemma cut_trace_omega_access: forall m, guarded_omega_access (filter m) (main_state m) (main_state (S m)).
Proof.
  intros.
  exists (sub_trace m).
  split; [| split].
  + intros r ? ? [sigma ?].
    apply (cut_filter_complete pfilter (trace_domain s) (trace_states s) (step_domains s) m r h (Terminating _ (filter m, sigma))); auto.
    unfold pfilter. simpl. unfold Terminating_pred, Ensembles.In; simpl.
    auto.
  + apply global_equiv_sym, main_state_sound.
  + eapply global_equiv_trans.
    - eapply global_equiv_sym, init_state_is_limit_state.
    - apply global_equiv_sym, main_state_sound.
Qed.

End SubTrace.