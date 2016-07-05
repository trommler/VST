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
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.

Section Stream.

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
  rdir_slow: forall n h, covered_by h (raw_direction n) \/ RandomVar_local_equiv (l n) (l (S n)) h h
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

Lemma RandomVarDomainStream_no_strict_conflict: forall (Omegas: RandomVarDomainStream) (n1 n2: nat) h1 h2,
  Omegas n1 h1 ->
  Omegas n2 h2 ->
  strict_conflict_history h1 h2 ->
  False.
Proof.
  intro.
  assert (forall n1 n2 h1 h2, n1 <= n2 -> Omegas n1 h1 ->
    Omegas n2 h2 ->
    strict_conflict_history h1 h2 ->
    False).
  Focus 2. {
    intros.
    destruct (le_dec n1 n2).
    + apply (H n1 n2 h1 h2); auto.
    + apply (H n2 n1 h2 h1); auto.
      omega.
      apply strict_conflict_history_sym; auto.
  } Unfocus.
  intros.
  apply (same_covered_future_anti_chain_no_strict_conflict (Omegas n1) (Omegas n2) h1 h2); auto.
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
    auto.
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

Definition lmap_states {Omegas: RandomVarDomainStream} {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) (l: ProgStateStream Omegas A): ProgStateStream Omegas B :=
  fun n => (ProgState_lift_mf f (l n)).

Definition lmap_dir {Omegas: RandomVarDomainStream} {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) {l: ProgStateStream Omegas A} (dir: ConvergeDir l): ConvergeDir (lmap_states f l).
  refine (Build_ConvergeDir _ _ _ _ (fun n => dir n) _ _).
  + apply rdir_forward.
  + intros.
    destruct (rdir_slow l dir n h); auto.
    right.
    Opaque RandomVarMap.
    hnf; intros [| | b]; split; intros; simpl in H0 |- *; rewrite @RandomVarMap_sound in H0 |- *;
    destruct H0 as [a [? ?]]; exists a.
    Transparent RandomVarMap.
    - split; auto.
      rewrite (H a) in H0; auto.
    - split; auto.
      rewrite (H a); auto.
    - split; auto.
      rewrite (H a) in H0; auto.
    - split; auto.
      rewrite (H a); auto.
    - split; auto.
      rewrite (H a) in H0; auto.
    - split; auto.
      rewrite (H a); auto.
Defined.

End Stream.
