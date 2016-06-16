Require Import RamifyCoq.lib.List_ext.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
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
  rewrite <- H0 in H; apply H; auto.
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

Record ConvergeDir (Omegas: RandomVarDomainStream): Type := {
  raw_direction: forall n, MeasurableSubset (Omegas n);
  rdir_forward: forall n, future_anti_chain (raw_direction n) (raw_direction (S n));
  rdir_slow: forall n h, Omegas n h -> ~ Omegas (S n) h -> raw_direction n h
}.

Global Coercion raw_direction: ConvergeDir >-> Funclass.

Definition ProgStateStream (Omegas: RandomVarDomainStream) (state: Type) {state_sigma: SigmaAlgebra state}: Type := forall n: nat, ProgState (Omegas n) state.

Definition is_limit_domain (Omegas: RandomVarDomainStream) (lim_Omega: RandomVarDomain) : Prop :=
  forall h,
    lim_Omega h <->
      (forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ Omegas n' h').

Definition is_limit {Omegas: RandomVarDomainStream} {lim_Omega: RandomVarDomain} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas) (lim: ProgState lim_Omega state) : Prop :=
  forall h s,
    lim h s <->
      (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n' h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h').

Definition limit_raw_domain (Omegas: RandomVarDomainStream): RandomHistory -> Prop :=
  fun h =>
    forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
      exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ Omegas n' h'.

Lemma RandomVarDomainStream_stable: forall (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas) (n: nat) h,
  Omegas n h ->
  (forall m, m >= n -> ~ dir m h) ->
  (forall m, m >= n -> Omegas m h).
Proof.
  intros.
  remember (m - n) as Delta eqn:?H.
  assert (m = Delta + n) by omega.
  clear H1 H2; subst m.
  induction Delta; auto.

  pose proof rdir_slow _ dir (Delta + n) h IHDelta.
  assert (Delta + n >= n) as HH by omega; specialize (H0 (Delta + n) HH); clear HH.
  destruct (classic ((Omegas (S Delta + n)) h)); tauto.
Qed.

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

Lemma limit_raw_domain_covered: forall (Omegas: RandomVarDomainStream) h n, limit_raw_domain Omegas h -> covered_by h (Omegas n).
Proof.
  intros.
  rename h into h_limit.
  assert (prefix_history (fin_history nil) h_limit) by (hnf; intros [|]; left; auto).
  specialize (H n (fin_history nil) (fin_history_fin _) H0); clear H0.
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
  destruct H as [n [? ?]].
  destruct (H0 0 (fstn_history (S n) h1) (fstn_history_finite _ _) (fstn_history_prefix _ _)) as [m1 [h1' [? [? [? ?]]]]].
  destruct (H1 0 (fstn_history (S n) h2) (fstn_history_finite _ _) (fstn_history_prefix _ _)) as [m2 [h2' [? [? [? ?]]]]].
  
  destruct (raw_anti_chain_legal (Omegas (max m1 m2))) as [?H].
  destruct (limit_raw_domain_covered Omegas h1 (max m1 m2) H0) as [h1'' [? ?]].
  destruct (limit_raw_domain_covered Omegas h2 (max m1 m2) H1) as [h2'' [? ?]].

  assert (prefix_history (fstn_history (S n) h1) h1'').
  Focus 1. {
    apply prefix_history_trans with h1'; auto.
    apply (proj_in_anti_chain_unique (Omegas m1) h1' h1'' h1); auto.
    apply (RandomVarDomainStream_mono Omegas m1 (max m1 m2)); auto.
    apply Max.le_max_l.
  } Unfocus.

  assert (prefix_history (fstn_history (S n) h2) h2'').
  Focus 1. {
    apply prefix_history_trans with h2'; auto.
    apply (proj_in_anti_chain_unique (Omegas m2) h2' h2'' h2); auto.
    apply (RandomVarDomainStream_mono Omegas m2 (max m1 m2)); auto.
    apply Max.le_max_r.
  } Unfocus.

  clear h1' h2' H4 H5 H6 H8 H9 H10.
  
  apply (H11 h1'' h2''); auto.
  exists n.
  rewrite <- (n_conflict_proper_aux n h1 h1'' h2 h2''); auto.
  + apply squeeze_history_coincide; auto.
  + apply squeeze_history_coincide; auto.
Qed.

Definition limit_domain_anti_chain (Omegas: RandomVarDomainStream): HistoryAntiChain := Build_HistoryAntiChain _ (limit_raw_domain Omegas) (limit_raw_domain_legal Omegas).

Lemma limit_domain_anti_chain_hered: forall (Omegas: RandomVarDomainStream) (n: nat) h,
  Omegas n h ->
  exists h_limit,
  prefix_history h h_limit /\ limit_domain_anti_chain Omegas h_limit.
Proof.
  intros.
  destruct (classic (exists l, prefix_history h (fin_history l) /\ forall n0, covered_by (fin_history l) (Omegas n0)));
  [| destruct (classic (exists init, h = fin_history init))].
  + (* when h_limit is finite *)
    destruct H0 as [l ?].
    pose proof 
      dec_inh_nat_subset_has_unique_least_element
        (fun m =>
           exists l0, length l0 = m /\
             prefix_history h (fin_history l0) /\
             forall n0, covered_by (fin_history l0) (Omegas n0))
        (fun n => classic (_ n))
        (ex_intro _ (length l) (ex_intro _ l (conj (@eq_refl _ (length l)) H0))).
    clear H0 l.
    destruct H1 as [m [[[l [? [? ?]]] ?] _]].
    exists (fin_history l).
    split; auto.

    assert (exists n0, Omegas n0 (fin_history l)) as HH; [| destruct HH as [n0 ?]].
    Focus 1. {
      destruct (cons_tail_dec l) as [? | [l0 [qa ?]]].
      + exists 0.
        subst l; destruct (H2 0) as [h' [? ?]].
        assert (h' = fin_history nil); [| subst; auto].
        clear - H4; history_extensionality n.
        specialize (H4 n); simpl in *.
        destruct H4, n; auto.
      + destruct (classic (exists n0, (Omegas n0) (fin_history l))); auto; exfalso.
        subst l m; rename l0 into l.
        specialize (H3 (length l)).
        assert (~ length (l +:: qa) <= length l) by (rewrite app_length; simpl; omega).
        apply H0, H3; clear H0 H3.
        exists l.
        split; auto.
        split.
        - eapply prefix_not_equal_history_backward; eauto.
          intro; apply H4; exists n; subst h; auto.
        - intros n0; specialize (H2 n0).
          destruct H2 as [h' [? ?]].
          exists h'; split; auto.
          eapply prefix_not_equal_history_backward; eauto.
          intro; apply H4; exists n0; subst h'; auto.
    } Unfocus.
    hnf; intros.
    exists (max (S n1) n0), (fin_history l).
    split; [pose proof Max.le_max_l (S n1) n0; omega |].
    split; [auto |].
    split; [apply prefix_history_refl |].

    clear - H2 H4.
    specialize (H2 (max (S n1) n0)); destruct H2 as [h [? ?]].
    destruct (RandomVarDomainStream_mono Omegas n0 (max (S n1) n0) (Max.le_max_r _ _) h H0) as [h0 [? ?]].
    assert (prefix_history h0 (fin_history l)) by (apply prefix_history_trans with h; auto).
    pose proof anti_chain_not_comparable (Omegas n0) _ _ H2 H4 H3.
    subst h0.
    pose proof prefix_history_anti_sym _ _ H H1.
    subst h.
    auto.

  + (* when h is finite but h_limit is infinite *)
    destruct H1 as [init ?]; subst h.
    pose proof (not_ex_all_not _ _ H0); clear H0; rename H1 into H0; simpl in H0.
    set (P h := prefix_history (fin_history init) h /\ exists n0 h1 h2, (Omegas n0) h1 /\ (Omegas (S n0)) h2 /\ prefix_history h1 h /\ prefix_history h h2 /\ h <> h2).
    assert (forall n l, Omegas n (fin_history l) -> prefix_history (fin_history init) (fin_history l) -> P (fin_history l)) as STRENTHEN; [| destruct (inf_history_construction P init) as [h [? ?]]].
    Focus 1. {
      clear n H.
      intros.
      destruct (dec_inh_nat_subset_has_unique_least_element (fun n0 => n0 > n /\ ~ (Omegas n0) (fin_history l)) (fun n => classic (_ n))) as [n0 [[? ?] _]].
      + specialize (H0 l).
        destruct (classic (exists n0 , n0 > n /\ ~ (Omegas n0) (fin_history l))); auto.
        exfalso.
        apply H0; split; auto.
        intros.
        destruct (lt_dec n n0).
        - exists (fin_history l); split; [apply prefix_history_refl |].
          destruct (classic ((Omegas n0) (fin_history l))); auto.
          exfalso; apply H2; exists n0; auto.
        - apply (RandomVarDomainStream_mono Omegas n0 n); auto; omega.
      + destruct H2.
        destruct n0 as [| n0]; [omega |].
        assert (Omegas n0 (fin_history l)).
        Focus 1. {
          specialize (H1 n0).
          destruct (classic ((Omegas n0) (fin_history l))); auto; exfalso.
          assert (~ S n0 <= n0) as HH by omega; apply HH, H3; clear HH H3.
          split; auto.
          destruct (NPeano.Nat.eq_dec n n0); [| omega].
          subst n0; exfalso; auto.
        } Unfocus.
        split; auto.
        destruct (RandomVarDomainStream_hered Omegas n0 (S n0) (fin_history l) (le_n_Sn _) H5) as [h2 [? ?]].
        exists n0, (fin_history l), h2.
        split; [| split; [| split; [| split]]]; auto.
        - apply prefix_history_refl.
        - intro; subst h2; auto.
    } Unfocus.
    Focus 1. {
      apply (STRENTHEN n); auto.
      apply prefix_history_refl.
    } Unfocus.
    Focus 1. {
      clear H n.
      intros.
      destruct H as [? [n0 [h1 [h2 [? [? [? [? ?]]]]]]]].
      destruct (prefix_not_equal_history_forward h2 l H4 H5) as [qa ?].
      exists qa.
      destruct (classic ((fin_history (l +:: qa)) = h2)).
      + subst h2.
        apply (STRENTHEN (S n0) (l +:: qa)); auto.
        eapply prefix_history_trans; eauto; apply prefix_history_fin_app.
      + split; [eapply prefix_history_trans; eauto; apply prefix_history_fin_app |].
        exists n0, h1, h2; split; [| split; [| split; [| split]]]; auto.
        eapply prefix_history_trans; eauto; apply prefix_history_fin_app.
    } Unfocus.
    Focus 1. {
      exists h.
      split.
      + specialize (H2 (length init)); destruct H2 as [? _]; [omega |].
        eapply prefix_history_trans; eauto.
        apply fstn_history_prefix.
      + hnf; intros.
        admit. (* TODO *)
    } Unfocus.
  + admit.
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
    admit.
Qed.

Definition limit_domain (Omegas: RandomVarDomainStream) (dir: ConvergeDir Omegas): RandomVarDomain.
  exists (limit_domain_anti_chain Omegas).
  eapply is_measurable_subspace_same_covered.
  + hnf; intros; split.
    - apply limit_domain_anti_chain_covered_forward; auto.
    - apply limit_domain_anti_chain_covered_backward; auto.
  + apply (proj2_sig (Omegas 0)).
Defined.

Definition limit {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas): ProgState (limit_domain Omegas dir) state.
  refine (Build_ProgState _ _ _
           (PrFamily.Build_MeasurableFunction _ _ _ (fun h s =>
   (exists n, (l n) h s /\ forall n', n' >= n -> ~ dir n' h) \/
      (s = NonTerminating _ /\
       forall n h_low, is_fin_history h_low -> prefix_history h_low h ->
         exists n' h', n' > n /\ prefix_history h_low h' /\ prefix_history h' h /\ dir n' h')) _ _ _ _ ) _).
  Admitted.

End Limit.

Section CutLimit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {state: Type} {state_sigma: SigmaAlgebra state}.

Variable (filter: measurable_set (MetaState state)).

Variables (Omegas: RandomVarDomainStream) (l: ProgStateStream Omegas state) (dir: ConvergeDir Omegas).

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
              (Intersection _ (Complement _ (left_raw_dir n0)) (left_raw_domain n0)) h /\
              left_raw_state n0 h s \/
              covered_by h (left_raw_dir n0) /\ l n h s
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
  + auto.
  + intros.
    rewrite RV.Intersection_spec in H.
    tauto.
  + hnf; intros.
    destruct H; auto.
Qed.

Lemma left_raw_dir_slow: forall n h, left_raw_domain n h -> ~ left_raw_domain (S n) h -> left_raw_dir n h.
Proof.
  intros; simpl in H0.
  destruct (classic ((left_raw_dir n) h)); tauto.
Qed.

Definition left_domains: RandomVarDomainStream := Build_RandomVarDomainStream (fun n => exist _ _ (left_raw_domain_measurable n)) left_raw_domain_same_covered left_raw_domain_forward.

Definition left_dir: ConvergeDir left_domains := Build_ConvergeDir _ (fun n => exist (fun P => PrFamily.is_measurable_set P (left_domains n)) (left_raw_dir n) (left_raw_dir_measurable n)) (left_raw_dir_forward) (left_raw_dir_slow).

Definition right_raw_dir (n: nat): RandomHistory -> Prop :=
  fun h => exists m, covered_by h (left_raw_dir m) /\ ~ covered_by h (left_raw_dir (S m)) /\ MeasurableSubset_HistoryAntiChain (dir (n + S m)) h.

End CutLimit.