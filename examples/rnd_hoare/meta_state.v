Require Import RamifyCoq.lib.List_ext.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.
Require Import RndHoare.history_anti_chain.
Require Import RndHoare.random_variable.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Instance MetaState_SigmaAlgebra (state: Type) {state_sig: SigmaAlgebra state}: SigmaAlgebra (MetaState state).
  apply (Build_SigmaAlgebra _ (fun P => is_measurable_set (fun s => P (Terminating _ s)))).
  + hnf; intros; simpl.
    apply is_measurable_set_proper.
    destruct H; split; unfold Included, In in *; hnf; intros; auto.
  + eapply is_measurable_set_proper; [| apply full_measurable].
    split; hnf; unfold In; intros; constructor.
  + intros.
    change (fun s : state => Complement (MetaState state) P (Terminating state s))
      with (Complement _ (fun s : state => P (Terminating state s))).
    apply complement_measurable; auto.
  + intros.
    change (fun s : state => Countable_Union (MetaState state) P (Terminating state s))
      with (Countable_Union _ (fun i s => P i (Terminating state s))).
    apply countable_union_measurable.
    auto.
Defined.

Inductive raw_MetaState_pair_left (cmd state: Type) (c: cmd): MetaState state -> MetaState (cmd * state) -> Prop :=
  | Error_pair_left: raw_MetaState_pair_left cmd state c (Error _) (Error _)
  | NonTerminating_pair_left: raw_MetaState_pair_left cmd state c (NonTerminating _) (NonTerminating _)
  | Terminating_pair_left: forall s, raw_MetaState_pair_left cmd state c (Terminating _ s) (Terminating _ (c, s)).

Definition MetaState_pair_left {cmd state: Type} {state_sig: SigmaAlgebra state} (c: cmd): @MeasurableFunction (MetaState state) (MetaState (cmd * state)) _ (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)).
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_pair_left cmd state c)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a.
    - exists (Error _); constructor.
    - exists (NonTerminating _); constructor.
    - exists (Terminating _ (c, s)); constructor.
  + simpl.
    intros.
    destruct P as [P ?H].
    simpl in *.
    eapply is_measurable_set_proper; [| exact (H c)].
    simpl.
    split; hnf; unfold In; intros.
    - apply H0; constructor.
    - inversion H1; auto.
Defined.

Inductive raw_MetaState_snd (cmd state: Type): MetaState (cmd * state) -> MetaState state -> Prop :=
  | Error_snd: raw_MetaState_snd cmd state (Error _) (Error _)
  | NonTerminating_snd: raw_MetaState_snd cmd state (NonTerminating _) (NonTerminating _)
  | Terminating_snd: forall c s, raw_MetaState_snd cmd state (Terminating _ (c, s)) (Terminating _ s).

Definition MetaState_snd {cmd state: Type} {state_sig: SigmaAlgebra state}: @MeasurableFunction (MetaState (cmd * state)) (MetaState state) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) _.
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_snd cmd state)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a as [ | | [? ?]].
    - exists (Error _); constructor.
    - exists (NonTerminating _); constructor.
    - exists (Terminating _ s); constructor.
  + simpl.
    intros.
    destruct P as [P ?H].
    eapply is_measurable_set_proper; [| exact H].
    simpl.
    split; hnf; unfold In; intros.
    - apply H0; constructor.
    - inversion H1; auto.
Defined.

Definition meta_state_measurable_set {state: Type} {state_sig: SigmaAlgebra state} (P: measurable_set state) (error non_terminating: Prop): measurable_set (MetaState state).
  exists (fun x => match x with | Error => error | NonTerminating => non_terminating | Terminating s => P s end).
  simpl.
  apply (proj2_sig P).
Defined.

Section ProgState.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Record ProgState (Omega: RandomVarDomain) (state: Type) {state_sigma: SigmaAlgebra state} : Type := {
  raw_state: RandomVariable Omega (MetaState state);
  inf_history_sound: forall (h: RandomHistory) (ms: MetaState state), is_inf_history h -> raw_state h ms -> ms = NonTerminating _
}.

Definition ProgState_RandomVariable (Omega: RandomVarDomain) (state: Type) {state_sigma: SigmaAlgebra state} (s: ProgState Omega state): RandomVariable Omega (MetaState state) := @raw_state Omega state _ s.

Global Coercion ProgState_RandomVariable: ProgState >-> RandomVariable.

Definition ProgState_pair_left {cmd state: Type} {state_sigma: SigmaAlgebra state} (c: cmd) {Omega: RandomVarDomain} (s: ProgState Omega state): @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state).
  refine (Build_ProgState Omega _ _ (RandomVarMap (MetaState_pair_left c) (raw_state _ _ s)) _).
  intros.
  rewrite RandomVarMap_sound in H0.
  destruct H0 as [? [? ?]].
  pose proof inf_history_sound _ _ s h x H H0.
  inversion H1; subst; congruence.
Defined.

Definition non_branch_tstate {state: Type} {state_sigma: SigmaAlgebra state} (s: state): ProgState unit_space_domain state.
  refine (Build_ProgState _ _ _ (unit_space_var (Terminating _ s)) _).
  intros.
  exfalso.
  apply PrFamily.rf_sound in H0.
  specialize (H0 0); simpl in H0.
  specialize (H 0).
  rewrite <- H0 in H; apply H.
  apply empty_history_spec.
Defined.

Definition Terminating_raw_domain {Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (s: ProgState Omega state): MeasurableSubset Omega :=
  PrFamily.PreImage_MSet s (meta_state_measurable_set (Full_MSet _) False False).

End ProgState.

Section Limit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Record RandomVarDomainStream : Type := {
  raw_domains: nat -> RandomVarDomain;
  rdom_same_covered: forall n, same_covered_anti_chain (raw_domains n) (raw_domains (S n));
  rdom_forward: forall n, future_anti_chain (raw_domains n) (raw_domains (S n))
}.

Global Coercion raw_domains: RandomVarDomainStream >-> Funclass.

Definition ProgStateStream (Omegas: RandomVarDomainStream) (state: Type) {state_sigma: SigmaAlgebra state}: Type := forall n: nat, ProgState (Omegas n) state.

Record ConvergeDir {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state): Type := {
  raw_direction: forall n, MeasurableSubset (Omegas n);
  rdir_forward: forall n, future_anti_chain (raw_direction n) (raw_direction (S n));
  rdir_slow: forall n h, raw_direction n h \/ RandomVar_local_equiv (l n) (l (S n)) h h
}.

Global Coercion raw_direction: ConvergeDir >-> Funclass.

Lemma RandomVarDomainStream_same_covered: forall (Omegas: RandomVarDomainStream) (n1 n2: nat),
  same_covered_anti_chain (Omegas n1) (Omegas n2).
Proof.
  intros Omegas.
  assert (forall n1 n2, n1 <= n2 -> same_covered_anti_chain (Omegas n1) (Omegas n2)).
  + intros.
    remember (n2 - n1) as Delta.
    assert (n2 = Delta + n1) by omega.
    subst n2; clear HeqDelta H.
    induction Delta.
    - reflexivity.
    - transitivity (Omegas (Delta + n1)); auto.
      apply rdom_same_covered.
  + intros.
    destruct (le_dec n1 n2).
    - apply H; auto.
    - symmetry; apply H; omega.
Qed.

Lemma RandomVarDomainStream_mono: forall (Omegas: RandomVarDomainStream) (n1 n2: nat),
  n1 <= n2 ->
  future_anti_chain (Omegas n1) (Omegas n2).
Proof.
  intros.
  remember (n2 - n1) as Delta.
  assert (n2 = Delta + n1) by omega.
  subst n2; clear HeqDelta H.
  induction Delta.
  + apply future_anti_chain_refl.
  + apply future_anti_chain_trans with (Omegas (Delta + n1)); auto.
    apply rdom_forward.
Qed.

Lemma RandomVarDomainStream_hered: forall (Omegas: RandomVarDomainStream) (n1 n2: nat) h1,
  n1 <= n2 ->
  Omegas n1 h1 ->
  exists h2,
  prefix_history h1 h2 /\ Omegas n2 h2.
Proof.
  intros.
  apply same_covered_future_anti_chain_spec with (Omegas n1); auto.
  + apply RandomVarDomainStream_same_covered.
  + apply RandomVarDomainStream_mono; auto.
Qed.

Lemma RandomVarDomainStream_non_conflict_inf_hered: forall (Omegas: RandomVarDomainStream) (n: nat) h m,
  (Omegas n) h ->
  is_n_history m h ->
  exists h1,
    is_inf_history h1 /\
    prefix_history h h1 /\
    (forall n0, exists h2, prefix_history h2 h1 /\ (Omegas n0) h2).
Proof.
  intros.
  assert (exists h1,
    is_inf_history h1 /\
    prefix_history h h1 /\
    (forall m0, m <= m0 -> forall n0, exists h2, (prefix_history h2 (fstn_history m0 h1) \/ prefix_history (fstn_history m0 h1) h2) /\ (Omegas n0) h2)).
  + apply (inf_history_construction (fun h => forall n0, exists h', (prefix_history h' h \/ prefix_history h h') /\ Omegas n0 h') h m).
    - intros.
      destruct (le_dec n n0) as [?H | ?H].
      * destruct (RandomVarDomainStream_hered Omegas _ _ _ H1 H) as [h' [? ?]].
        exists h'; auto.
      * destruct (fun HH => RandomVarDomainStream_mono Omegas n0 n HH h H) as [h' [? ?]]; [omega |].
        exists h'; auto.
    - auto.
    - intros.
      destruct (classic (exists n0, ~ exists h', prefix_history h' h0 /\ Omegas n0 h')).
      * pose proof dec_inh_nat_subset_has_unique_least_element _ (fun n => classic (_ n)) H3.
        clear H3; destruct H4 as [n0 [[? ?] _]].
        destruct (H1 n0) as [h1 [? ?]].
        destruct H5; [exfalso; apply H3; exists h1; auto |].
        assert (h0 <> h1) by (intro; subst h1; apply H3; exists h0; split; auto; apply prefix_history_refl).
        destruct (prefix_not_equal_forward h0 h1 H5 H7) as [qa ?].
        exists qa.
        intros n1.
        destruct (le_dec n0 n1) as [?H | ?H].
        Focus 1. {
          destruct (RandomVarDomainStream_hered Omegas _ _ _ H9 H6) as [h2 [? ?]].
          exists h2; split; auto.
          right.
          apply prefix_history_trans with h1; auto.
        } Unfocus.
        Focus 1. {
          specialize (H4 n1).
          assert (exists h' : RandomHistory, prefix_history h' h0 /\ (Omegas n1) h') by tauto.
          destruct H10 as [h2 [? ?]].
          exists h2; split; auto.
          left.
          apply prefix_history_trans with h0; auto.
          apply prefix_app_history.
        } Unfocus.
      * exists (existT _ ro_default_question ro_default_answer).
        intros.
        pose proof not_ex_not_all _ _ H3; clear H1 H3; cbv beta in H4.
        destruct (H4 n0) as [h' [? ?]]; exists h'.
        split; auto.
        left.
        eapply prefix_history_trans; [eassumption | apply prefix_app_history].
  + destruct H1 as [h1 [? [? ?]]].
    exists h1; split; [| split]; auto.
    intros.
    pose proof proj1 (RandomVarDomainStream_same_covered Omegas n n0 _ H1).
    specialize (H4 (ex_intro _ h (conj (or_introl H2) H))).
    destruct H4 as [h2 [? ?]].
    exists h2; split; auto.
    destruct H4; auto.

    destruct H4 as [m0 [? ?]].
    specialize (H3 (max (S m0) m) (Max.le_max_r _ _) n0).
    assert (strict_conflict_history h2 (fstn_history (max (S m0) m) h1)).
    Focus 1. {
      exists m0; split.
      + apply history_coincide_trans with h1; auto.
        apply history_coincide_weaken with (max (S m0) m); [pose proof Max.le_max_l (S m0) m; omega |].
        apply fstn_history_coincide.
      + rewrite fstn_history_Some by (pose proof Max.le_max_l (S m0) m; omega).
        auto.
    } Unfocus.
    destruct H3 as [h3 [[? | ?] ?]].
    - exfalso.
      pose proof strict_conflict_backward_conflict_right _ _ _ H7 H3.
      apply (@rand_consi _ _ (raw_anti_chain_legal _) _ _ H9 H5 H8).
    - pose proof strict_conflict_forward_right _ _ _ H7 H3.
      apply strict_conflict_conflict in H9.
      exfalso.
      apply (@rand_consi _ _ (raw_anti_chain_legal _) _ _ H9 H5 H8).
Qed.

Definition MeasurableSubset_stream_proj (Omegas: RandomVarDomainStream) (n: nat) (P: MeasurableSubset (Omegas n)): MeasurableSubset (Omegas (S n)).
  exists (filter_anti_chain (fun h => covered_by h P) (Omegas (S n))).
  apply is_measurable_set_same_covered with (O1 := Omegas n) (P1 := P).
  + hnf; intro; apply MeasurableSubset_in_domain.
  + unfold Included, Ensembles.In; intros.
    destruct H; auto.
  + apply rdom_same_covered.
  + apply same_covered_future_anti_chain_subset1 with (d1 := Omegas n).
    - apply rdom_same_covered.
    - apply rdom_forward.
    - intro; apply MeasurableSubset_in_domain.
  + apply (proj2_sig P).
Defined.

Lemma ConvergeDir_mono: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} {l: ProgStateStream Omegas state} (dir: ConvergeDir l) (n1 n2: nat),
  n1 <= n2 ->
  future_anti_chain (dir n1) (dir n2).
Proof.
  intros.
  remember (n2 - n1) as Delta.
  assert (n2 = Delta + n1) by omega.
  subst n2; clear HeqDelta H.
  induction Delta.
  + apply future_anti_chain_refl.
  + apply future_anti_chain_trans with (dir (Delta + n1)); auto.
    apply rdir_forward.
Qed.

Lemma ConvergeDir_uncovered_mono: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} {l: ProgStateStream Omegas state} (dir: ConvergeDir l) (n1 n2: nat) h,
  n1 <= n2 ->
  ~ covered_by h (dir n1) ->
  ~ covered_by h (dir n2).
Proof.
  intros.
  remember (n2 - n1) as Delta eqn:?H.
  assert (n2 = Delta + n1) by omega.
  clear H1 H; subst n2.
  induction Delta; auto.
  
  intro; apply IHDelta; clear IHDelta.
  destruct H as [h' [? ?]].
  destruct (rdir_forward _ dir (Delta + n1) h' H1) as [h'' [? ?]].
  exists h''; split; auto.
  eapply prefix_history_trans; eauto.
Qed.

Lemma ProgStateStream_stable: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) (n n0: nat) h,
  n <= n0 ->
  ~ covered_by h (dir n) ->
  RandomVar_local_equiv (l n) (l n0) h h.
Proof.
  intros.
  remember (n0 - n) as Delta eqn:?H.
  assert (n0 = Delta + n) by omega.
  clear H1 H; subst n0.
  induction Delta.
  + hnf; intros; reflexivity.
  + hnf; intros.
    rewrite (IHDelta a).
    pose proof rdir_slow _ dir (Delta + n) h.
    destruct H; auto.
    exfalso.
    apply (ConvergeDir_uncovered_mono dir n (Delta + n)) in H0; [| omega].
    apply H0; exists h.
    split; auto.
    apply prefix_history_refl.
Qed.

Lemma RandomVarDomainStream_stable: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) (n n0: nat) h,
  n <= n0 ->
  ~ covered_by h (dir n) ->
  (Omegas n h <-> Omegas n0 h).
Proof.
  intros.
  pose proof ProgStateStream_stable l dir n n0 h H H0.
  clear - H1.
  split.
  + intros.
    destruct (PrFamily.rf_complete _ _ (l n) h H) as [s ?].
    rewrite (H1 s) in H0.
    apply (PrFamily.rf_sound _ _ (l n0) h s) in H0; auto.
  + intros.
    destruct (PrFamily.rf_complete _ _ (l n0) h H) as [s ?].
    rewrite <- (H1 s) in H0.
    apply (PrFamily.rf_sound _ _ (l n) h s) in H0; auto.
Qed.

Definition limit_raw_domain (Omegas: RandomVarDomainStream): RandomHistory -> Prop :=
  fun h => forall n m, exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ Omegas n' h'.

Lemma limit_raw_domain_covered: forall (Omegas: RandomVarDomainStream) h n, limit_raw_domain Omegas h -> covered_by h (Omegas n).
Proof.
  intros.
  rename h into h_limit.
  specialize (H n 0).
  destruct H as [n0 [h0 [? [? [? ?]]]]].
  
  destruct (fun HH => RandomVarDomainStream_mono Omegas n n0 HH h0 H2) as [h [? ?]]; [omega |].
  exists h.
  split; auto.
  apply prefix_history_trans with h0; auto.
Qed.

Lemma limit_raw_domain_legal: forall (Omegas: RandomVarDomainStream), LegalHistoryAntiChain (limit_raw_domain Omegas).
Proof.
  intros.
  constructor.
  hnf; intros.
  destruct H as [m [? ?]].
  destruct (H0 0 (S m)) as [n1 [h1' [? [? [? ?]]]]].
  destruct (H1 0 (S m)) as [n2 [h2' [? [? [? ?]]]]].

  destruct (raw_anti_chain_legal (Omegas (max n1 n2))) as [?H].
  destruct (limit_raw_domain_covered Omegas h1 (max n1 n2) H0) as [h1'' [? ?]].
  destruct (limit_raw_domain_covered Omegas h2 (max n1 n2) H1) as [h2'' [? ?]].

  assert (prefix_history (fstn_history (S m) h1) h1'').
  Focus 1. {
    apply prefix_history_trans with h1'; auto.
    apply (proj_in_anti_chain_unique (Omegas n1) h1' h1'' h1); auto.
    apply (RandomVarDomainStream_mono Omegas n1 (max n1 n2)); auto.
    apply Max.le_max_l.
  } Unfocus.

  assert (prefix_history (fstn_history (S m) h2) h2'').
  Focus 1. {
    apply prefix_history_trans with h2'; auto.
    apply (proj_in_anti_chain_unique (Omegas n2) h2' h2'' h2); auto.
    apply (RandomVarDomainStream_mono Omegas n2 (max n1 n2)); auto.
    apply Max.le_max_r.
  } Unfocus.

  apply (H11 h1'' h2''); auto.
  exists m.
  rewrite <- (n_conflict_proper_aux m h1 h1'' h2 h2''); auto.
  + apply squeeze_history_coincide; auto.
  + apply squeeze_history_coincide; auto.
Qed.

Lemma prefix_in_every_layer_prefix_in_limit: forall (Omegas: RandomVarDomainStream) h,
  is_inf_history h ->
  (forall n, exists h', prefix_history h' h /\ Omegas n h') ->
  exists h', prefix_history h' h /\ limit_raw_domain Omegas h'.
Proof.
  intros.
  destruct (classic (exists m, forall n, exists h', prefix_history h' (fstn_history m h) /\ Omegas n h')).
  + pose proof 
      dec_inh_nat_subset_has_unique_least_element _ (fun n => classic (_ n)) H1.
    clear H1; destruct H2 as [m [[? ?] _]].
    exists (fstn_history m h).
    split; [apply fstn_history_prefix |].
    assert (exists n, Omegas n (fstn_history m h)).
    Focus 1. {
      destruct m.
      + exists 0.
        destruct (H1 0) as [h' [? ?]].
        replace (fstn_history 0 h) with h'; auto.
        clear - H3.
        history_extensionality n; specialize (H3 n).
        destruct H3; auto.
        rewrite fstn_history_None; auto; omega.
      + apply NNPP; intro.
        specialize (H2 m).
        assert (~ S m <= m) as HH by omega; apply HH, H2; clear HH H2.
        intros n; specialize (H1 n); destruct H1 as [h' [? ?]].
        exists h'; split; auto.
        destruct (classic (h' = (fstn_history (S m) h))).
        - subst h'; exfalso.
          apply H3; exists n; auto.
        - apply prefix_not_equal_fstn_Sn; auto.
    } Unfocus.
    clear H2.
    destruct H3 as [n ?].
    hnf; intros.
    exists (max (S n0) n), (fstn_history m h).
    split; [| split; [| split]]; auto.
    - pose proof Max.le_max_l (S n0) n; omega.
    - apply fstn_history_prefix.
    - apply prefix_history_refl.
    - specialize (H1 (max (S n0) n)).
      destruct H1 as [h' [? ?]].
      destruct (RandomVarDomainStream_mono Omegas n (max (S n0) n) (Max.le_max_r _ _) _ H3) as [h'' [? ?]].
      pose proof prefix_history_trans _ _ _ H4 H1.
      pose proof anti_chain_not_comparable _ _ _ H5 H2 H6.
      subst h''.
      pose proof prefix_history_anti_sym _ _ H1 H4.
      subst h'.
      auto.
  + exists h.
    split; [apply prefix_history_refl |].
    hnf; intros.
    assert (exists n', n' > n /\ ~ exists h', prefix_history h' (fstn_history m h) /\ (Omegas n') h').
    Focus 1. {
      pose proof not_ex_all_not _ _ H1 m.
      clear H1; simpl in H2.
      pose proof not_all_ex_not _ _ H2; clear H2.
      destruct H1 as [n0 ?].
      exists (max (S n) n0).
      split; [pose proof Max.le_max_l (S n) n0; omega |].
      intro; apply H1; clear H1.
      destruct H2 as [h' [? ?]].
      destruct (RandomVarDomainStream_mono Omegas n0 _ (Max.le_max_r _ _) _ H2) as [h'' [? ?]].
      exists h''; split; auto.
      eapply prefix_history_trans; eauto.
    } Unfocus.
    destruct H2 as [n0 [? ?]].
    specialize (H0 n0); destruct H0 as [h0 [? ?]].
    pose proof prefix_history_comparable _ _ _ H0 (fstn_history_prefix m h).
    destruct H5.
    - exfalso.
      apply H3; exists h0; split; auto.
    - exists n0, h0; split; [| split]; auto.
Qed.

Definition limit_domain_anti_chain (Omegas: RandomVarDomainStream): HistoryAntiChain := Build_HistoryAntiChain _ (limit_raw_domain Omegas) (limit_raw_domain_legal Omegas).

Lemma limit_domain_anti_chain_hered: forall (Omegas: RandomVarDomainStream) (n: nat) h,
  Omegas n h ->
  exists h_limit,
  prefix_history h h_limit /\ limit_domain_anti_chain Omegas h_limit.
Proof.
  intros.
  assert (exists h1, is_inf_history h1 /\ prefix_history h h1 /\
            (forall n, exists h2, prefix_history h2 h1 /\ Omegas n h2)).
  Focus 1. {
    destruct (n_history_inf_history_decT h) as [[m ?H] | ?H].
    + apply (RandomVarDomainStream_non_conflict_inf_hered Omegas n h m); auto.
    + exists h.
      split; [auto | split; [apply prefix_history_refl |]].
      intros.
      destruct (le_dec n n0) as [?H | ?H].
      - destruct (RandomVarDomainStream_hered Omegas n n0 h H1 H) as [h3 [? ?]].
        pose proof inf_history_prefix _ _ H0 H2.
        subst h3.
        exists h; auto.
      - apply (fun HH => RandomVarDomainStream_mono Omegas n0 n HH _ H).
        omega.
  } Unfocus.
  destruct H0 as [h1 [? [? ?]]].
  destruct (prefix_in_every_layer_prefix_in_limit Omegas _ H0 H2) as [h2 [? ?]].
  exists h2; split; auto.

  pose proof prefix_history_comparable _ _ _ H1 H3.
  destruct H5; auto.
  pose proof limit_raw_domain_covered Omegas _ n H4.
  destruct H6 as [h3 [? ?]].
  pose proof anti_chain_not_comparable _ _ _ H7 H (prefix_history_trans _ _ _ H6 H5).
  subst h3; auto.
Qed.

Lemma limit_domain_anti_chain_covered_backward: forall (Omegas: RandomVarDomainStream) h,
  is_inf_history h ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ limit_domain_anti_chain Omegas h') ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ Omegas 0 h').
Proof.
  intros.
  destruct H0 as [h' [? ?]].
  pose proof limit_raw_domain_covered _ _ 0 H1.
  destruct H2 as [h'' [? ?]].
  exists h''; split; auto.
  eapply strict_conflict_or_prefix_backward_left; eauto.
Qed.

Lemma limit_domain_anti_chain_covered_forward: forall (Omegas: RandomVarDomainStream) h,
  is_inf_history h ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ Omegas 0 h') ->
  (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ limit_domain_anti_chain Omegas h').
Proof.
  intros.
  destruct (classic (exists n, exists h', strict_conflict_history h' h /\ (Omegas n) h')).
  + clear H0; destruct H1 as [n [h' [? ?]]].
    destruct (limit_domain_anti_chain_hered _ _ _ H1) as [h'' [? ?]].
    exists h''; split; auto.
    right.
    eapply strict_conflict_forward_left; eauto.
  + assert (forall n, exists h', prefix_history h' h /\ (Omegas n) h').
    Focus 1. {
      intros n.
      rewrite (RandomVarDomainStream_same_covered Omegas 0 n h H) in H0.
      destruct H0 as [h' [[? | ?] ?]].
      + exists h'; auto.
      + exfalso; apply H1.
        exists n, h'; auto.
    } Unfocus.
    clear H0 H1.
    pose proof prefix_in_every_layer_prefix_in_limit _ _ H H2.
    clear - H0.
    destruct H0 as [h' [? ?]]; exists h'; auto.
Qed.

Lemma limit_domain_anti_chain_same_covered: forall (Omegas: RandomVarDomainStream) n,
  same_covered_anti_chain (Omegas n) (limit_domain_anti_chain Omegas).
Proof.
  intros.
  rewrite (RandomVarDomainStream_same_covered _ n 0).
  hnf; intros; split.
  + apply limit_domain_anti_chain_covered_forward; auto.
  + apply limit_domain_anti_chain_covered_backward; auto.
Qed.

Definition limit_domain (Omegas: RandomVarDomainStream): RandomVarDomain.
  exists (limit_domain_anti_chain Omegas).
  eapply is_measurable_subspace_same_covered.
  + apply (limit_domain_anti_chain_same_covered _ 0).
  + apply (proj2_sig (Omegas 0)).
Defined.

Lemma ConvergeDir_uncovered_limit_domain_spec: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) n h,
  ~ covered_by h (dir n) ->
  (Omegas n h <-> limit_domain Omegas h).
Proof.
  intros.
  split; intros.
  + hnf; intros.
    exists (max (S n0) n), h.
    pose proof RandomVarDomainStream_stable l dir n (max (S n0) n) h.
    split; [| split; [| split]].
    - pose proof Max.le_max_l (S n0) n; omega.
    - apply fstn_history_prefix.
    - apply prefix_history_refl.
    - rewrite <- H1; auto.
      pose proof Max.le_max_r (S n0) n; omega.
  + destruct (H0 n 0) as [n0 [h' [? [? [? ?]]]]].
    assert (~ covered_by h' (dir n)) by (intro; apply H; apply (prefix_history_covered (dir n) h'); auto).
    assert (h' = h).
    Focus 2. {
      subst h'.
      rewrite (RandomVarDomainStream_stable l dir n n0) by (auto; omega).
      auto.
    } Unfocus.
    destruct (n_history_inf_history_decT h') as [[m ?H] | ?H].
    - destruct (H0 n0 (S m)) as [n1 [h'' [? [? [? ?]]]]].
      assert (h' = h'').
      Focus 1. {
        apply (ConvergeDir_uncovered_mono dir n n0) in H5; [| omega].
        rewrite (RandomVarDomainStream_stable l dir n0 n1 h') in H4 by (auto; omega).
        pose proof prefix_history_comparable _ _ _ H3 H9.
        apply (anti_chain_not_comparable' (Omegas n1)); auto.
      } Unfocus.
      subst h''.
      apply (coincide_more_than_length m (S m)); [auto | | omega].
      apply history_coincide_sym; apply squeeze_history_coincide; auto.
    - apply (inf_history_prefix _ _ H6 H3).
Qed.

Definition limit_raw_state {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) : RandomHistory -> MetaState state -> Prop :=
  fun h s =>
   (exists n, (l n) h s /\ ~ covered_by h (dir n)) \/
      (s = NonTerminating _ /\
       forall n m,
         exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ dir n' h').

Lemma limit_raw_state_pf: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l), forall h s1 s2, limit_raw_state l dir h s1 -> limit_raw_state l dir h s2 -> s1 = s2.
Proof.
  intros.
  hnf in H, H0.
  destruct H as [[n1 [? ?]] | ?], H0 as [[n2 [? ?]] | ?].
  + pose proof ProgStateStream_stable l dir n1 (max n1 n2) h (Max.le_max_l _ _) H1.
    pose proof ProgStateStream_stable l dir n2 (max n1 n2) h (Max.le_max_r _ _) H2.
    rewrite (H3 s1) in H.
    rewrite (H4 s2) in H0.
    apply (PrFamily.rf_partial_functionality _ _ (l (max n1 n2)) h); auto.
  + exfalso.
    destruct H0 as [_ ?].
    specialize (H0 n1 0).
    destruct H0 as [n2 [h' [? [? [? ?]]]]].
    apply (ConvergeDir_uncovered_mono dir n1 n2) in H1; [| omega].
    apply H1; exists h'.
    auto.
  + exfalso.
    destruct H as [_ ?].
    specialize (H n2 0).
    destruct H as [n1 [h' [? [? [? ?]]]]].
    apply (ConvergeDir_uncovered_mono dir n2 n1) in H1; [| omega].
    apply H1; exists h'.
    auto.
  + destruct H as [? _], H0 as [? _].
    congruence.
Qed.

Lemma limit_raw_state_complete: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l), forall h, limit_domain Omegas h -> exists s, limit_raw_state l dir h s.
Proof.
  intros.
  destruct (classic (exists n, ~ covered_by h (dir n))).
  + destruct H0 as [n ?].
    rewrite <- ConvergeDir_uncovered_limit_domain_spec in H by eauto.
    pose proof PrFamily.rf_complete _ _ (l n) h H.
    destruct H1 as [s ?]; exists s.
    left.
    exists n; auto.
  + exists (NonTerminating _).
    right.
    split; auto.
    intros.
    specialize (H n m).
    destruct H as [n' [h' [? [? [? ?]]]]].
    exists n', h'; split; [| split; [| split]]; auto.
    apply NNPP; intro; apply H0; clear H0.
    exists n'; intro.
    apply H4; clear H4.
    destruct H0 as [h'' [? ?]].
    assert (h' = h''); [| subst; auto].
    pose proof prefix_history_comparable _ _ _ H2 H0.
    apply (anti_chain_not_comparable' (Omegas n')); auto.
    eapply MeasurableSubset_in_domain, H4.
Qed.

Lemma limit_raw_state_sound: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l), forall h s, limit_raw_state l dir h s -> limit_domain Omegas h.
Proof.
  intros.
  destruct H as [[n [?H ?H]] | ?H].
  + hnf; intros.
    exists (max (S n0) n), h.
    split; [| split; [| split]].
    - pose proof Max.le_max_l (S n0) n; omega.
    - apply fstn_history_prefix.
    - apply prefix_history_refl.
    - pose proof PrFamily.rf_sound _ _ _ _ _ H.
      rewrite <- (RandomVarDomainStream_stable l dir _ _ h (Max.le_max_r (S n0) n) H0).
      auto.
  + destruct H as [_ ?].
    hnf; intros.
    specialize (H n m).
    destruct H as [n' [h' [? [? [? ?]]]]].
    exists n', h'; split; [| split; [| split]]; auto.
    eapply MeasurableSubset_in_domain, H2.
Qed.

Lemma limit_raw_state_inf_sound: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) h s, is_inf_history h -> (limit_raw_state l dir) h s -> s = NonTerminating _.
Proof.
  intros.
  destruct H0 as [[n [?H ?H]] | ?H].
  + apply (inf_history_sound _ _ (l n) h s); auto.
  + destruct H0; auto.
Qed.

Lemma TerminatingOrError_PreImage_is_countable_union: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) (P: sigma_algebra.measurable_set (MetaState state)),
  Included P (fun b => NonTerminating _ <> b) ->
  Same_set
     (fun a => (limit_domain Omegas) a /\ (forall b, limit_raw_state l dir a b -> P b))
     (Countable_Union _
        (fun i h => (Omegas i) h /\ ~ covered_by h (dir i) /\ (forall s, (l i) h s -> P s))).
Proof.
  intros.
  rewrite Same_set_spec; intros h.
  split; intros.
  + destruct H0.
    pose proof limit_raw_state_complete l dir h H0.
    destruct H2 as [s ?].
    specialize (H1 s H2).
    specialize (H _ H1); unfold Ensembles.In in H.
    destruct H2 as [[n [?H ?H]] | [?H _]]; [| congruence].
    exists n.
    split; [apply PrFamily.rf_sound in H2; auto |].
    split; [auto |].
    intros.
    pose proof PrFamily.rf_partial_functionality _ _ (l n) h s s0 H2 H4.
    subst s; auto.
  + destruct H0 as [n [? [? ?]]].
    pose proof PrFamily.rf_complete _ _ (l n) h H0 as [s ?].
    specialize (H2 _ H3).
    specialize (H _ H2); unfold Ensembles.In in H.
    split; [rewrite (ConvergeDir_uncovered_limit_domain_spec l dir n h) in H0; auto |].
    intros.
    assert (limit_raw_state l dir h s) by (left; exists n; auto).
    pose proof limit_raw_state_pf l dir h b s H4 H5.
    subst b; auto.
Qed.

Lemma stable_PreImage_limit_domain_measurable: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) (P: sigma_algebra.measurable_set (MetaState state)) n,
  PrFamily.is_measurable_set (fun h => (Omegas n) h /\ ~ covered_by h (dir n) /\ (forall s, (l n) h s -> P s)) (limit_domain Omegas). 
Proof.
  intros.
  change (fun h => (Omegas n) h /\ ~ covered_by h (dir n) /\ (forall s, (l n) h s -> P s))
    with (filter_anti_chain (fun h => ~ covered_by h (dir n) /\ forall s, (l n) h s -> P s) (Omegas n): _ -> Prop).
  eapply @is_measurable_set_same_covered; [| | apply (limit_domain_anti_chain_same_covered _ n) | reflexivity |].
  + intros h [? [? ?]]; auto.
  + intros h [? [? ?]].
    rewrite <- (ConvergeDir_uncovered_limit_domain_spec l dir n h H0); auto.
  + eapply PrFamily.is_measurable_set_proper; [| reflexivity | apply PrFamily.intersection_measurable].
    - rewrite Same_set_spec; intros h; rewrite Intersection_spec.
      instantiate (1 := Intersection _ (Omegas n) (Complement _ (dir n))).
      instantiate (1 := fun h => (Omegas n) h /\ (forall s, (l n) h s -> P s)).
      pose proof covered_by_is_element (dir n) (Omegas n) h.
      simpl.
      assert (Included (dir n) (Omegas n)) by (exact (MeasurableSubset_in_domain (Omegas n) (dir n))).
      rewrite Intersection_spec; unfold Complement, Ensembles.In.
      tauto.
    - apply (PrFamily.rf_preserve _ _ (l n) P).
    - apply PrFamily.complement_measurable.
      apply (proj2_sig (dir n)).
Qed.

Lemma limit_raw_state_measurable: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) (P: sigma_algebra.measurable_set (MetaState state)), PrFamily.is_measurable_set (fun h => (limit_domain Omegas) h /\ forall s, (limit_raw_state l dir) h s -> P s) (limit_domain Omegas).
Proof.
  intros.
  revert P.
  apply PrFamily.rf_preserve_proof_minus1 with (b0 := NonTerminating _).
  + simpl.
    eapply is_measurable_set_proper; [| apply empty_measurable].
    rewrite Same_set_spec; intros x.
    rewrite Empty_set_spec; simpl.
    split; [intros; congruence | intros []].
  + apply limit_raw_state_pf.
  + apply limit_raw_state_complete.
  + intros.
    eapply PrFamily.is_measurable_set_proper; [| reflexivity | apply PrFamily.countable_union_measurable].
    - apply TerminatingOrError_PreImage_is_countable_union; auto.
    - intros. cbv beta.
      apply stable_PreImage_limit_domain_measurable.
Qed.

Definition limit {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l): ProgState (limit_domain Omegas) state :=
  Build_ProgState _ _ _
    (PrFamily.Build_MeasurableFunction _ _ _
       (limit_raw_state l dir)
       (limit_raw_state_pf _ _)
       (limit_raw_state_complete _ _)
       (limit_raw_state_sound _ _)
       (limit_raw_state_measurable _ _))
     (limit_raw_state_inf_sound _ _).

End Limit.

(*
Section CutLimit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {state: Type} {state_sigma: SigmaAlgebra state}.

Variable (filter: measurable_set (MetaState state)).

Variables (Omegas: RandomVarDomainStream) (l: ProgStateStream Omegas state) (dir: ConvergeDir l).

Fixpoint left_raw_dir (n: nat): MeasurableSubset (Omegas n) :=
  match n as n_PAT return MeasurableSubset (Omegas n_PAT) with
  | 0 => PrFamily.Intersection_MSet (dir 0) (PrFamily.PreImage_MSet (l 0) filter)
  | S n0 => PrFamily.Intersection_MSet
              (MeasurableSubset_stream_proj Omegas n0 (left_raw_dir n0))
              (PrFamily.Intersection_MSet (dir (S n0)) (PrFamily.PreImage_MSet (l (S n0)) filter))
  end.

Fixpoint left_raw_domain (n: nat): HistoryAntiChain :=
  match n with
  | 0 => Omegas 0
  | S n0 => subst_anti_chain (left_raw_dir n0) (left_raw_domain n0) (Omegas n)
  end.

Fixpoint left_raw_state (n: nat): RandomHistory -> MetaState state -> Prop :=
  match n with
  | 0 => fun h s => l 0 h s
  | S n0 => fun h s => 
              left_raw_state n0 h s /\ ~ left_raw_dir n0 h \/
              l n h s /\ covered_by h (left_raw_dir n0)
  end.

Lemma left_raw_dir_in_left_raw_domain: forall n, Included (left_raw_dir n) (left_raw_domain n).
Proof.
  intros.
  induction n; unfold Included, Ensembles.In; intros.
  + apply (MeasurableSubset_in_domain (Omegas 0) _ x H).
  + Opaque PrFamily.Intersection_MSet MeasurableSubset_HistoryAntiChain. simpl in H. Transparent PrFamily.Intersection_MSet MeasurableSubset_HistoryAntiChain. (* should not need this Opaque-Transparent. *)
    rewrite !RV.Intersection_spec in H.
    destruct H as [[? ?] [? ?]].
    right.
    split.
    - eapply MeasurableSubset_in_domain; eauto.
    - replace (filter_anti_chain (left_raw_dir n) (left_raw_domain n)) with (left_raw_dir n: HistoryAntiChain); auto.
      anti_chain_extensionality h.
      simpl.
      specialize (IHn h). tauto.
Qed.

Lemma left_raw_dir_in_Omegas: forall n, Included (left_raw_dir n) (Omegas n).
Proof.
  intros n h; eapply MeasurableSubset_in_domain; eauto.
Qed.

Lemma left_raw_domain_same_covered: forall n, same_covered_anti_chain (left_raw_domain n) (left_raw_domain (S n)).
Proof.
  intros.
  simpl.
  apply subst_anti_chain_same_covered' with (P' := Omegas n); auto.
  + apply left_raw_dir_in_left_raw_domain.
  + apply left_raw_dir_in_Omegas.
  + apply rdom_same_covered.
  + apply rdom_forward.
Qed.

Lemma left_raw_domain_same_covered_with_head: forall n, same_covered_anti_chain (Omegas 0) (left_raw_domain n).
Proof.
  intros.
  induction n.
  + reflexivity.
  + transitivity (left_raw_domain n); auto.
    apply left_raw_domain_same_covered; auto.
Qed.

Lemma left_raw_domain_forward: forall n, future_anti_chain (left_raw_domain n) (left_raw_domain (S n)).
Proof.
  intros.
  simpl.
  apply subst_anti_chain_future.
Qed.

Lemma left_raw_domain_measurable: forall n, is_measurable_subspace (left_raw_domain n).
Proof.
  intros.
  eapply is_measurable_subspace_same_covered.
  + apply left_raw_domain_same_covered_with_head.
  + apply (proj2_sig (Omegas 0)).
Qed.

Lemma left_raw_dir_measurable: forall n, PrFamily.is_measurable_set (left_raw_dir n) (exist _ _ (left_raw_domain_measurable n)).
Proof.
  intros.
  eapply is_measurable_set_same_covered with (O1 := Omegas n) (P1 := left_raw_dir n).
  + apply left_raw_dir_in_Omegas.
  + apply left_raw_dir_in_left_raw_domain.
  + transitivity (Omegas 0).
    - apply RandomVarDomainStream_same_covered.
    - apply left_raw_domain_same_covered_with_head.
  + reflexivity.
  + apply (proj2_sig (left_raw_dir n)).
Qed.

Lemma left_raw_dir_forward: forall n, future_anti_chain (left_raw_dir n) (left_raw_dir (S n)).
Proof.
  intros.
  simpl.
  apply future_anti_chain_Included with (l1 := left_raw_dir n) (r1 := MeasurableSubset_stream_proj Omegas n (left_raw_dir n)).
  + apply Included_refl.
  + unfold Included, Ensembles.In; intros.
    rewrite RV.Intersection_spec in H.
    tauto.
  + hnf; intros.
    destruct H; auto.
Qed.

Definition left_domains: RandomVarDomainStream := Build_RandomVarDomainStream (fun n => exist _ _ (left_raw_domain_measurable n)) left_raw_domain_same_covered left_raw_domain_forward.

Lemma left_raw_state_partial_functionality_ind: forall n,
  (forall h b1 b2, left_raw_state n h b1 -> left_raw_state n h b2 -> b1 = b2) ->
  (forall h b, left_raw_state n h b -> left_domains n h) ->
  (forall h b1 b2, left_raw_state (S n) h b1 -> left_raw_state (S n) h b2 -> b1 = b2).
Proof.
  intros ? H_PF H_S; intros.
  destruct H as [[? ?] | [? ?]], H0 as [[? ?] | [? ?]].
  + apply (H_PF h); auto.
  + exfalso.
    destruct H2 as [h' [? ?]].
    pose proof H_S h _ H.
    pose proof left_raw_dir_in_left_raw_domain n _ H3.
    pose proof anti_chain_not_comparable _ h' h H5 H4 H2.
    subst h'; auto.
  + exfalso.
    destruct H1 as [h' [? ?]].
    pose proof H_S h _ H0.
    pose proof left_raw_dir_in_left_raw_domain n _ H3.
    pose proof anti_chain_not_comparable _ h' h H5 H4 H1.
    subst h'; auto.
  + apply (PrFamily.rf_partial_functionality _ _ (l (S n)) h); auto.
Qed.

Lemma left_raw_state_sound_ind: forall n,
  (forall h b, left_raw_state n h b -> left_domains n h) ->
  (forall h b, left_raw_state (S n) h b -> left_domains (S n) h).
Proof.
  intros n H_S; intros.
  destruct H as [[? ?] | [? ?]]; [left | right].
  + apply H_S in H.
    auto.
  + apply (PrFamily.rf_sound _ _ (l (S n))) in H.
    split; auto.
    destruct H0 as [h' [? ?]]; exists h'; split; auto.
    split; auto.
    apply (left_raw_dir_in_left_raw_domain n); auto.
Qed.

Lemma left_raw_state_complete_ind: forall n,
  (forall h, left_domains n h -> exists b, left_raw_state n h b) ->
  (forall h, left_domains (S n) h -> exists b, left_raw_state (S n) h b).
Proof.
  intros n H_COM; intros.
  destruct H as [[? ?] | [? ?]].
  + apply H_COM in H.
    destruct H as [b ?]; exists b; left.
    auto.
  + apply (PrFamily.rf_complete _ _ (l (S n))) in H.
    destruct H as [b ?]; exists b; right.
    split; auto.
    destruct H0 as [h' [? [? ?]]]; exists h'; auto.
Qed.


(*
Lemma left_raw_dir_slow: forall n h, left_raw_dir n h \/ RandomVar_local_equiv (l n) (l (S n)) h h
Proof.
  intros; simpl in H0.
  destruct (classic ((left_raw_dir n) h)); tauto.
Qed.
*)

(*
Definition left_dir: ConvergeDir left_domains := Build_ConvergeDir _ (fun n => exist (fun P => PrFamily.is_measurable_set P (left_domains n)) (left_raw_dir n) (left_raw_dir_measurable n)) (left_raw_dir_forward) (left_raw_dir_slow).

Definition right_raw_dir (n: nat): RandomHistory -> Prop :=
  fun h => exists m, covered_by h (left_raw_dir m) /\ ~ covered_by h (left_raw_dir (S m)) /\ MeasurableSubset_HistoryAntiChain (dir (n + S m)) h.
*)
End CutLimit.
*)
