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

Definition cmd_skip_or_else {Omega: RandomVarDomain} (c: cmd) (s: ProgState Omega (cmd * state)): Prop :=
  forall h cs, s h (Terminating _ cs) -> fst cs = Sskip \/ fst cs = c.

Lemma ProgState_pair_left_cmd_is_skip_or_else: forall {Omega: RandomVarDomain} (c: cmd) (s: ProgState Omega state), cmd_skip_or_else c (ProgState_pair_left c s).
Proof.
  intros.
  hnf; intros.
  destruct cs as [cc ss].
  rewrite (ProgState_pair_left_Terminating_spec c s h cc ss) in H.
  right; simpl; tauto.
Qed.
  
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

Definition is_loop_global_state {Omega: RandomVarDomain} (b: expr) (c: cmd) (s: ProgState Omega state) (s': ProgState Omega (cmd * state)): Prop :=
  (forall h, s h (NonTerminating _) <-> s' h (NonTerminating _)) /\
  (forall h, s h (Error _) <-> s' h (Error _)) /\
  (forall h a, s h (Terminating _ a) <-> s' h (Terminating _ (Sskip, a)) \/ s' h (Terminating _ (Swhile b c, a))) /\
  (forall h a, s' h (Terminating _ (Sskip, a)) -> eval_bool b a false).

Lemma guarded_loop: forall {O1 O2: RandomVarDomain} (b: expr) (c: cmd) (src: ProgState O1 state) (dst: ProgState O2 state) (src': ProgState O1 (cmd * state)) (dst': ProgState O2 (cmd * state)),
  is_loop_global_state b c src src' ->
  is_loop_global_state b c dst dst' ->
  guarded_omega_access (Swhile b c) src' dst' ->
  omega_access (ProgState_pair_left (Sifthenelse b c Sskip) src) (ProgState_pair_left Sskip dst).
Proof.
  intros.
Admitted.

Lemma cmd_skip_or_seq: forall {O1 O2: RandomVarDomain} (c1 c2: cmd) (src: ProgState O1 state) (dst': ProgState O2 (cmd * state)),
  guarded_omega_access
   (Ssequence Sskip c2)
   (ProgState_pair_left (Ssequence c1 c2) src)
   dst' ->
  cmd_skip_or_else (Ssequence Sskip c2) dst' ->
  exists dst, dst' = ProgState_pair_left (Ssequence Sskip c2) dst.
Admitted.

Lemma cmd_skip_or_loop: forall {O1 O2: RandomVarDomain} (b: expr) (c: cmd) (src: ProgState O1 state)(src': ProgState O1 (cmd * state)) (dst': ProgState O2 (cmd * state)),
  is_loop_global_state b c src src' ->
  guarded_omega_access (Swhile b c) src' dst' ->
  cmd_skip_or_else (Swhile b c) dst' ->
  exists dst, is_loop_global_state b c dst dst'.
Admitted.

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

Lemma cut_trace_cmd_skip_or_else: forall {O1 O2} c (src: ProgState O1 state) (dst: ProgState O2 state),
  RandomVar_global_equiv (trace_states s 0) (ProgState_pair_left c src) ->
  RandomVar_global_equiv (limit (trace_states s) (step_domains s)) (ProgState_pair_left Sskip dst) ->
  forall m, cmd_skip_or_else (filter m) (main_state (S m)).
Proof.
  intros.
  hnf; intros.
  pose proof cut_filter_sound pfilter (trace_domain s) (trace_states s) (step_domains s) m h (Terminating _ cs).
  destruct (classic (main_dir (S m) h)); [right | left].
  + rewrite <- (app_same_set (main_dir_sound pfilter (trace_domain s) (trace_states s) (step_domains s) (S m))) in H2.
    rewrite <- (main_state_sound pfilter (trace_domain s) (trace_states s) (step_domains s) (S m) h _) in H2.
    specialize (H2 H3 H1).
    simpl in H2.
    hnf in H2.
    symmetry; auto.
  + clear H2.
    pose proof limit_state_sound pfilter (trace_domain s) (trace_states s) (step_domains s) h.
    pose proof dir_limit_slow main_state main_dir (S m) h.
    destruct H4.
    - exfalso; apply H3; clear - H1 H4.
      pose proof covered_by_is_element (main_dir (S m)) (main_domain (S m)) h.
      apply PrFamily.rf_sound in H1.
      specialize (H H1 (MeasurableSubset_in_domain _ _)).
      tauto.
    - rewrite (H4 _) in H1.
      unfold main_state in H1; rewrite (H2 _) in H1.
      rewrite (H0 h _) in H1.
      destruct cs as [cc ss].
      rewrite (ProgState_pair_left_Terminating_spec Sskip dst h cc ss) in H1.
      destruct H1; auto.
Qed.

End SubTrace.