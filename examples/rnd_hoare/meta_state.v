Require Import RamifyCoq.lib.List_ext.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.
Require Import RndHoare.history_anti_chain.
Require Import RndHoare.random_variable.

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
