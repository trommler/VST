Require Import RamifyCoq.lib.List_ext.
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
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Module Type STREAM_LIMIT.

Parameter limit_domain: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream), RandomVarDomain.

Axiom limit_domain_spec: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream) (h: RandomHistory),
  limit_domain Omegas h =
  forall n m, exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ Omegas n' h'.

Parameter limit: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l), ProgState (limit_domain Omegas) state.

Axiom limit_spec: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) h s,
  limit l dir h s =
   ((exists n, (l n) h s /\ ~ covered_by h (dir n)) \/
    (s = NonTerminating _ /\
     forall n m,
       exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ dir n' h')).

Axiom limit_domain_same_covered: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream) n,
  same_covered_anti_chain (Omegas n) (limit_domain Omegas).

Axiom limit_domain_forward: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream) n,
  future_anti_chain (Omegas n) (limit_domain Omegas).

(* TODO: change it to "slow" *)
Axiom ConvergeDir_uncovered_limit_domain_spec: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) n h,
  ~ covered_by h (dir n) ->
  (Omegas n h <-> limit_domain Omegas h).

End STREAM_LIMIT.

Module StreamLimit: STREAM_LIMIT.

Section StreamLimit.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

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

Lemma limit_domain_anti_chain_future: forall (Omegas: RandomVarDomainStream) n,
  future_anti_chain (Omegas n) (limit_domain_anti_chain Omegas).
Proof.
  intros.
  hnf; intros.
  destruct (H n 0) as [n' [h' [? [? [? ?]]]]].
  destruct (fun HH => RandomVarDomainStream_mono Omegas n n' HH h' H3) as [h'' [? ?]]; [omega |].
  exists h''; split; auto.
  eapply prefix_history_trans; eauto.
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

Lemma limit_domain_spec: forall (Omegas: RandomVarDomainStream) (h: RandomHistory),
  limit_domain Omegas h =
  forall n m, exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ Omegas n' h'.
Proof. intros; reflexivity. Qed.

Lemma limit_spec: forall {Omegas: RandomVarDomainStream} {state: Type} {state_sigma: SigmaAlgebra state} (l: ProgStateStream Omegas state) (dir: ConvergeDir l) h s,
  limit l dir h s =
   ((exists n, (l n) h s /\ ~ covered_by h (dir n)) \/
    (s = NonTerminating _ /\
     forall n m,
       exists n' h', n' > n /\ prefix_history (fstn_history m h) h' /\ prefix_history h' h /\ dir n' h')).
Proof. intros. reflexivity. Qed.

Lemma limit_domain_same_covered: forall (Omegas: RandomVarDomainStream) n,
  same_covered_anti_chain (Omegas n) (limit_domain Omegas).
Proof. intros; apply limit_domain_anti_chain_same_covered. Qed.

Lemma limit_domain_forward: forall (Omegas: RandomVarDomainStream) n,
  future_anti_chain (Omegas n) (limit_domain Omegas).
Proof. intros; apply limit_domain_anti_chain_future. Qed.

End StreamLimit.

End StreamLimit.

Export StreamLimit.

Lemma RandomVarDomainStream_limit_no_strict_conflict: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream) (n: nat) h1 h2,
  Omegas n h1 ->
  limit_domain Omegas h2 ->
  strict_conflict_history h1 h2 ->
  False.
Proof.
  intros.
  apply (same_covered_future_anti_chain_no_strict_conflict (Omegas n) (limit_domain Omegas) h1 h2); auto.
  + apply limit_domain_same_covered.
  + apply limit_domain_forward; auto.
Qed.

Lemma RandomVarDomainStream_and_limit_no_strict_conflict: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omegas: RandomVarDomainStream) h1 h2,
  (exists n, Omegas n h1) \/ limit_domain Omegas h1 ->
  (exists n, Omegas n h2) \/ limit_domain Omegas h2 ->
  strict_conflict_history h1 h2 ->
  False.
Proof.
  intros.
  destruct H as [[n1 ?H] | ?H], H0 as [[n2 ?H] | ?H].
  + apply (RandomVarDomainStream_no_strict_conflict Omegas n1 n2 h1 h2); auto.
  + apply (RandomVarDomainStream_limit_no_strict_conflict Omegas n1 h1 h2); auto.
  + apply (RandomVarDomainStream_limit_no_strict_conflict Omegas n2 h2 h1); auto.
    apply strict_conflict_history_sym; auto.
  + apply strict_conflict_conflict in H1.
    exact (@rand_consi _ _ (raw_anti_chain_legal (limit_domain Omegas)) _ _ H1 H H0).
Qed.
    