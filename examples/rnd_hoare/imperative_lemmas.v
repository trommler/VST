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

Lemma cmd_not_rec: forall c1 c2, Ssequence c1 c2 <> c2.
Proof.
  intros.
  revert c1; induction c2; intros.
  + intro; inversion H.
  + intro; inversion H.
  + intro; inversion H.
  + intro; inversion H.
    apply (IHc2_2 c2_1); auto.
  + intro; inversion H.
Qed.

Definition seq1_MFun (c2: cmd): @MeasurableFunction cmd cmd (max_sigma_alg _) (max_sigma_alg _).
  refine (Build_MeasurableFunction _ _ _ _ (fun c c' => c = Ssequence c' c2 \/ c' = c2 /\ forall c'', c <> Ssequence c'' c2) _ _ _).
  + intros.
    destruct H as [? | [? ?]], H0 as [? | [? ?]]; try congruence.
  + intros.
    destruct (classic (exists c' : cmd, a = Ssequence c' c2)) as [[c' ?] | ?].
    - exists c'; auto.
    - exists c2; right.
      pose proof not_ex_all_not _ _ H.
      auto.
  + intros.
    apply I.
Defined.

Definition seq1P (c2: cmd): Ensemble (cmd * state) := fun cs => fst cs = c2 \/ exists c1, fst cs = Ssequence c1 c2.

Lemma seq_step_spec: forall {Omega} c1 c2 s (cs: ProgState Omega _) h mcs,
  step (Ssequence c1 c2, s) cs ->
  cs h mcs ->
   partial_Terminating_pred (seq1P c2) mcs.
Proof.
  intros.
  remember (Ssequence c1 c2, s) as cs0 eqn:?H.
  revert c1 c2 s H1 H0; induction H; intros; try congruence.
  + inversion H1; clear H1; subst.
    destruct mcs as [| | [cc ss]]; try solve [simpl; auto].
    Opaque RandomVarMap. simpl in H0. Transparent RandomVarMap.
    rewrite RandomVarMap_sound in H0.
    destruct H0 as [mcs [? ?]].
    inversion H1; subst.
    inversion H4; subst.
    destruct a as [cc' ss']; simpl in *; subst.
    right; simpl; eauto.
  + inversion H1; subst.
    Opaque unit_space_var. simpl in H0. Transparent unit_space_var.
    apply unit_space_var_spec in H0.
    destruct H0; subst.
    left; auto.
Qed.

Lemma guarded_skip_access_is_no_guard: forall {O1 O2: RandomVarDomain} (src: ProgState O1 (cmd * state)) (dst: ProgState O2 (cmd * state)), guarded_omega_access Sskip src dst <-> omega_access src dst.
Proof.
  intros.
  split; intros; [destruct H as [l [? [? ?]]]; exists l; auto |].
  destruct H as [l [? ?]].
  exists l; split; [| split]; auto.
  intros n h ? [ss ?].
  pose proof step_sound l (S n) h H1.
  inversion H3; subst.
  pose proof PrFamily.rf_partial_functionality _ _ (trace_states l (S n)) _ _ _ H2 sound1.
  inversion H4; subst cs1; clear H4.
  inversion step_fact.
Qed.

Lemma guarded_seq_const_access: forall {O1 O2: RandomVarDomain} (c1 c2: cmd) (src: ProgState O1 state) dst' ,
  guarded_omega_access c2 (ProgState_pair_left (Ssequence c1 c2) src) dst' ->
  cmd_skip_or_else c2 dst' ->
  exists (dst: ProgState O2 state), 
  dst' = ProgState_pair_left c2 dst /\
  omega_access
   (ProgState_pair_left c1 src)
   (ProgState_pair_left Sskip dst).
Proof.
  intros.
  destruct H as [[Omegas l dir ?H] [? [? ?]]]; simpl in *.
  assert (forall n h, (dir n) h -> ~ (exists sigma : state, (l n) h (Terminating (cmd * state) (c2, sigma)))) as HH.
  Focus 1. {
    destruct n; auto.
    intros ? ? [ss ?].
    rewrite (H2 _ _) in H5.
    rewrite RandomVarMap_sound in H5.
    destruct H5 as [ms [? ?]].
    inversion H6; subst; simpl; auto.
    inversion H9.
    apply (cmd_not_rec c1 c2); auto.
  } Unfocus.
  assert (forall n h mcs, l n h mcs -> partial_Terminating_pred (seq1P c2) mcs) as HH0.
  Focus 1. {
    induction n.
    + intros.
      rewrite (H2 _ _) in H4.
      rewrite RandomVarMap_sound in H4.
      destruct H4 as [ms [? ?]].
      inversion H5; subst; simpl; auto.
      inversion H6; subst.
      right; exists c1; auto.
    + intros.
      destruct (rdir_slow l dir n h).
      - destruct H5 as [h' [? ?]].
        pose proof H n _ H6.
        destruct H7.
        destruct cs1 as [cc1 ss1].
        pose proof IHn _ _ sound1.
        simpl in H7.
        destruct H7.
        * simpl in H7; subst cc1.
          exfalso; apply (HH _ _ H6).
          eauto.
        * destruct H7 as [cc1' ?]; simpl in H7; subst cc1.
          destruct (prefix_history_app_exists _ _ H5) as [h'' ?]; subst h.
          rewrite (sound2 h'' mcs) in H4; clear sound2.
          clear - step_fact H4.
          apply (seq_step_spec cc1' c2  _  _ h'' mcs step_fact H4).
      - rewrite <- (H5 _) in H4.
        eapply IHn; eauto.
  } Unfocus.
  pose (lmap_states (@LeftF_MFun' _ state _ (seq1_MFun c2)) l) as l'.
  pose (lmap_dir (@LeftF_MFun' _ state _ (seq1_MFun c2)) dir) as dir'.
  assert (forall n, global_step (dir' n) (l' n) (l' (S n))) as HH1.
  Focus 1. {
    intros.
    intros h ?.
    assert (dir n h) by auto.
    pose proof H n h H5.
    destruct H6.
    destruct (rf_complete _ _ (@LeftF_MFun' _ state _ (seq1_MFun c2)) cs1) as [cs1' ?].
    assert (sound1': l' n h (Terminating _ cs1')).
    Focus 1. {
      subst l'.
      Opaque RandomVarMap. simpl. Transparent RandomVarMap.
      rewrite RandomVarMap_sound; exists (Terminating _ cs1); split; auto.
      constructor; auto.
    } Unfocus.
    pose (cs2' := ProgState_lift_mf (LeftF_MFun' (seq1_MFun c2)) cs2).
    assert (step_fact': Randomized.step cs1' cs2'). admit.
    assert (sound2': forall h' mcs, l' (S n) (app_history h h') mcs <-> cs2' h' mcs). admit.
    apply (Build_local_step h _ _ (l' n) (l' (S n)) cs1' _ cs2'); auto.
  } Unfocus.
  exists (ProgState_snd dst').
  assert (dst' = ProgState_pair_left c2 (ProgState_snd dst')); [| split; auto].
  Focus 1. {
    ProgState_extensionality h mcs.
    Opaque RandomVarMap. simpl. Transparent RandomVarMap.
    rewrite !RV.Compose_assoc, RandomVarMap_sound, lift_mf_compose.
    split.
    + intros.
      exists mcs; split; auto.
      destruct mcs as [| | [cc ss]]; constructor.
      specialize (H0 _ _ H4).
      rewrite <- (H3 _ _) in H4.
      pose proof partial_Terminating_pred_limit l dir _ HH0.
      specialize (H5 _ _ H4).
      clear - H5 H0.
      simpl in *.
      exists ss; split; auto.
      destruct H0; [| subst; auto].
      destruct H5; [subst; auto |].
      destruct H0 as [c1 ?]; simpl in *.
      congruence.
    + intros [mcs' [? ?]].
      inversion H5; subst; auto.
      destruct a as [cc' ss'], b as [cc ss].
      destruct H6 as [ss'' [? ?]].
      simpl in H6; subst ss''.
      inversion H7; subst ss' cc.
      specialize (H0 _ _ H4).
      pose proof H4.
      rewrite <- (H3 _ _) in H4.
      pose proof partial_Terminating_pred_limit l dir _ HH0.
      specialize (H8 _ _ H4).
      clear - H8 H6 H0.
      simpl in *.
      destruct H0; [| subst; auto].
      destruct H8; [subst; auto |].
      destruct H0 as [c1 ?]; simpl in *.
      congruence.
  } Unfocus.
  Focus 1. {
    exists (@Build_execution_trace normal_imp normal_sss Omegas l' dir' HH1).
    split; simpl. admit. admit. (* subtle and true. *)
  } Unfocus.
Qed.

Lemma guarded_skip_access: forall {O1 O2: RandomVarDomain} (c: cmd) (src: ProgState O1 state) (dst: ProgState O2 state),
  guarded_omega_access
    Sskip
   (ProgState_pair_left c src)
   (ProgState_pair_left Sskip dst) ->
  omega_access
   (ProgState_pair_left c src)
   (ProgState_pair_left Sskip dst).
Proof.
  intros.
  rewrite guarded_skip_access_is_no_guard in H; auto.
Qed.

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