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

Definition is_Terminating {state: Type}: Ensemble (MetaState state) :=
  fun s => match s with | Terminating _ => True | _ => False end.

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

Lemma NonTerminating_measurable: forall {A} {sA: SigmaAlgebra A}, is_measurable_set (eq (NonTerminating A)).
Proof.
  intros.
  simpl.
  eapply is_measurable_set_proper; [| apply empty_measurable].
  rewrite Same_set_spec; intros x.
  rewrite Empty_set_spec; simpl.
  split; [intros; congruence | intros []].
Qed.

Lemma Error_measurable: forall {A} {sA: SigmaAlgebra A}, is_measurable_set (eq (Error A)).
Proof.
  intros.
  simpl.
  eapply is_measurable_set_proper; [| apply empty_measurable].
  rewrite Same_set_spec; intros x.
  rewrite Empty_set_spec; simpl.
  split; [intros; congruence | intros []].
Qed.

Lemma is_Terminating_measurable: forall {A} {sA: SigmaAlgebra A}, is_measurable_set (@is_Terminating A).
Proof.
  intros.
  simpl.
  eapply is_measurable_set_proper; [| apply full_measurable].
  rewrite Same_set_spec; intros x.
  rewrite Full_set_spec; simpl.
  tauto.
Qed.

Definition NonTerminating_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ NonTerminating_measurable.

Definition Error_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ Error_measurable.

Definition is_Terminating_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ is_Terminating_measurable.

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
(*
Definition Terminating_equiv {Omega: RandomVarDomain} {state state': Type} {state_sigma: SigmaAlgebra state}  {state_sigma': SigmaAlgebra state'} (ps: ProgState Omega state) (ps': ProgState Omega state'): Prop :=
  forall h s s', ps h s -> ps' h s' -> (s = NonTerminating _ <-> s' = NonTerminating _) /\ (s = Error _ <-> s' = Error _).

Definition TerminatingShrink {O1 O2: RandomVarDomain} {A: Type} {SA: SigmaAlgebra A} (s1: ProgState O1 A) (s2: ProgState O2 A) : Prop := future_anti_chain (filter_anti_chain (fun h => forall s, s1 h s -> is_Terminating s) O1) (filter_anti_chain (fun h => forall s, s2 h s -> is_Terminating s) O2).

Definition post_dom_meta_state {state A: Type} (sample: MetaState state) (origin: MetaState A): MetaState A :=
  match sample with
  | NonTerminating => NonTerminating _ 
  | Error => Error _
  | _ => origin
  end.

Definition post_dom_var (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {state_sigma: SigmaAlgebra state} {SA: SigmaAlgebra A} (sample: RandomVariable O2 (MetaState state)): RandomVariable O1 (MetaState A) -> RandomVariable O2 (MetaState A).
  refine (fun f => PrFamily.Build_MeasurableFunction _ _ _
    (fun h a => exists h' a' s, prefix_history h' h /\ f h' a' /\ sample h s /\ post_dom_meta_state s a' = a) _ _ _ _).
  + intros h ? ? [h' [a' [s' [? [? [? ?]]]]]] [h'' [a'' [s'' [? [? [? ?]]]]]].
    pose proof PrFamily.rf_sound _ _ f _ _ H0.
    pose proof PrFamily.rf_sound _ _ f _ _ H4.
    pose proof anti_chain_not_comparable' O1 _ _ H7 H8 (prefix_history_comparable _ _ _ H H3).
    subst h''.
    pose proof PrFamily.rf_partial_functionality _ _ f _ _ _ H0 H4.
    pose proof PrFamily.rf_partial_functionality _ _ sample _ _ _ H1 H5.
    subst a'' s''.
    congruence.
  + intros h ?.
    destruct (Hf h H) as [h' [? ?]].
    destruct (PrFamily.rf_complete _ _ f _ H1) as [b ?].
    destruct (PrFamily.rf_complete _ _ sample _ H) as [s ?].
    exists (post_dom_meta_state s b), h', b, s; auto.
  + intros h ? [h' [a' [s' [? [? [? ?]]]]]].
    eapply (PrFamily.rf_sound _ _ sample); eauto.
  + intros.
    eapply PrFamily.is_measurable_set_proper; [| reflexivity |].
    - instantiate (1 := Union _ (Union _
           (Intersection _
             (fun _ => P (NonTerminating _))
             (fun h => O2 h /\ (forall b, sample h b -> NonTerminating _ = b)))
           (Intersection _
             (fun _ => P (Error _))
             (fun h => O2 h /\ (forall b, sample h b -> Error _ = b))))
           (Intersection _
             (fun h => O2 h /\ (forall b, sample h b -> is_Terminating b))
             (filter_anti_chain (fun h => covered_by h (filter_anti_chain (fun h => forall b, f h b -> P b) O1)) O2))).
      rewrite Same_set_spec; intro h; simpl.
      rewrite !Union_spec, !Intersection_spec.
      split.
      Focus 1. {
        intros [? ?].
        destruct (classic (P (NonTerminating A) /\ sample h (NonTerminating _)));
        [left; left | destruct (classic (P (Error A) /\ sample h (Error _))); [left; right | right]].
        + destruct H1.
          pose proof PrFamily.rf_sound _ _ sample _ _ H2.
          split; [| split]; auto.
          intros.
          exact (PrFamily.rf_partial_functionality _ _ sample _ _ _ H2 H4).
        + destruct H2.
          pose proof PrFamily.rf_sound _ _ sample _ _ H3.
          split; [| split]; auto.
          intros.
          exact (PrFamily.rf_partial_functionality _ _ sample _ _ _ H3 H5).
        + assert (forall b, sample h b -> is_Terminating b).
          - intros.
            destruct (Hf _ H) as [h' [? ?]].
            pose proof PrFamily.rf_complete _ _ f _ H5 as [a ?].
            assert (NonTerminating _ <> b /\ Error _ <> b) as HH;
             [| destruct b; simpl; destruct HH; auto; congruence].
            split; intro; subst b; [apply H1 | apply H2]; clear H1 H2;
            split; auto; apply H0; exists h', a; eauto.
          - split; [split |]; auto.
            destruct (Hf _ H) as [h' [? ?]].
            split; auto.
            exists h'; split; auto.
            split; auto.
            intros a ?; specialize (H0 a).
            apply H0.
            exists h', a.
            destruct (PrFamily.rf_complete _ _ sample _ H) as [b ?].
            specialize (H3 _ H7).
            exists b; split; [| split; [| split]]; auto.
            destruct b; auto; inversion H3.
      } Unfocus.
      Focus 1. {
        intros [[? | ?] | ?].
        + destruct H as [? [? ?]].
          split; auto; intros.
          destruct H2 as [_ [a [s [_ [_ [? ?]]]]]].
          apply H1 in H2; subst; auto.
        + destruct H as [? [? ?]].
          split; auto; intros.
          destruct H2 as [_ [a [s [_ [_ [? ?]]]]]].
          apply H1 in H2; subst; auto.
        + destruct H as [[? ?] [_ [h' [? [? ?]]]]].
          split; auto.
          intros b [h'' [a' [s [? [? [? ?]]]]]].
          specialize (H0 _ H6).
          assert (a' = b) by (destruct s; inversion H0; auto); subst a'.
          pose proof PrFamily.rf_sound _ _ f _ _ H5.
          pose proof anti_chain_not_comparable' O1 _ _ H2 H8 (prefix_history_comparable _ _ _ H1 H4).
          subst h''; auto.
      } Unfocus.
    - apply PrFamily.union_measurable; [apply PrFamily.union_measurable |];
      [ apply PrFamily.intersection_const_measurable
      | apply PrFamily.intersection_const_measurable
      | apply PrFamily.intersection_measurable;
        [| apply (is_measurable_set_same_covered O1 O2
                  (filter_anti_chain (fun h0 => forall b, f h0 b -> P b) O1))]].
      * apply (PrFamily.rf_preserve _ _ sample NonTerminating_MSet).
      * apply (PrFamily.rf_preserve _ _ sample Error_MSet).
      * apply (PrFamily.rf_preserve _ _ sample is_Terminating_MSet).
      * intros ? [? ?]; auto.
      * intros ? [? ?]; auto.
      * auto.
      * apply same_covered_future_anti_chain_subset1 with O1; auto.
        intros ? [? ?]; auto.
      * apply (PrFamily.rf_preserve _ _ f).
Defined.

Definition post_dom_prog_state (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {SA: SigmaAlgebra A} {state_sigma: SigmaAlgebra state} (sample: ProgState O2 state): ProgState O1 A -> ProgState O2 A.
  refine (fun f => Build_ProgState _ _ _ (post_dom_var O1 O2 Hf Hs sample f) _).
  intros.
  simpl in H0.
  destruct H0 as [h' [a' [s [? [? [? ?]]]]]].
  pose proof inf_history_sound _ _ sample _ _ H H2.
  subst.
  auto.
Defined.

Lemma post_dom_prog_state_NonTerminating_spec: forall (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {SA: SigmaAlgebra A} {state_sigma: SigmaAlgebra state} (sample: ProgState O2 state) (s: ProgState O1 A) h a, sample h (NonTerminating _) -> (post_dom_prog_state _ _ Hf Hs sample s h a <-> a = NonTerminating _).
Proof.
  intros.
  simpl.
  pose proof PrFamily.rf_sound _ _ sample _ _ H.
  destruct (Hf _ H0) as [h' [? ?]].
  destruct (PrFamily.rf_complete _ _ s _ H2) as [a' ?].
  split; [intros [h'' [a'' [a''' [? [? [? ?]]]]]]; subst | exists h', a'; eauto].
  pose proof PrFamily.rf_partial_functionality _ _ sample _ _ _ H H6; subst; auto.
Qed.

Lemma post_dom_prog_state_Error_spec: forall (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {SA: SigmaAlgebra A} {state_sigma: SigmaAlgebra state} (sample: ProgState O2 state) (s: ProgState O1 A) h a, sample h (Error _) -> (post_dom_prog_state _ _ Hf Hs sample s h a <-> a = Error _).
Proof.
  intros.
  simpl.
  pose proof PrFamily.rf_sound _ _ sample _ _ H.
  destruct (Hf _ H0) as [h' [? ?]].
  destruct (PrFamily.rf_complete _ _ s _ H2) as [a' ?].
  split; [intros [h'' [a'' [a''' [? [? [? ?]]]]]]; subst | exists h', a'; eauto].
  pose proof PrFamily.rf_partial_functionality _ _ sample _ _ _ H H6; subst; auto.
Qed.

Lemma post_dom_prog_state_Terminating_spec: forall (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {SA: SigmaAlgebra A} {state_sigma: SigmaAlgebra state} (sample: ProgState O2 state) (s: ProgState O1 A) h a0 a, sample h a0 -> is_Terminating a0 -> (post_dom_prog_state _ _ Hf Hs sample s h a <-> exists h', prefix_history h' h /\ s h' a).
Proof.
  intros.
  simpl.
  split.
  + intros [h' [a' [a'' [? [? [? ?]]]]]].
    exists h'; split; auto.
    pose proof PrFamily.rf_partial_functionality _ _ sample _ _ _ H H3; subst.
    destruct a''; auto; inversion H0.
  + intros [h' [? ?]].
    pose proof PrFamily.rf_sound _ _ sample _ _ H.
    destruct (Hf _ H3) as [h'' [? ?]].
    pose proof PrFamily.rf_sound _ _ s _ _ H2.
    pose proof anti_chain_not_comparable' O1 _ _ H6 H5 (prefix_history_comparable _ _ _ H1 H4).
    subst h''.
    exists h', a, a0; split; [| split; [| split]]; auto.
    destruct a0; auto; inversion H0.
Qed.

Lemma post_dom_prog_state_Terminating_equiv: forall (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {state A: Type} {SA: SigmaAlgebra A} {state_sigma: SigmaAlgebra state} (s1: ProgState O1 state) (s2: ProgState O2 state) (Hts: TerminatingShrink s1 s2) (a1: ProgState O1 A),
  Terminating_equiv s1 a1 ->
  Terminating_equiv s2 (post_dom_prog_state _ _ Hf Hs s2 a1).
Proof.
  intros.
  hnf; intros ?h ?x ?x ? ?.
  destruct x as [| | ?x] eqn:?H; auto.
  + rewrite post_dom_prog_state_Error_spec in H1 by (subst; auto).
    split; split; intros; congruence.
  + rewrite post_dom_prog_state_NonTerminating_spec in H1 by (subst; auto).
    split; split; intros; congruence.
  + rewrite post_dom_prog_state_Terminating_spec in H1 by (subst; simpl; eauto).
    destruct H1 as [h' [? ?]].
    destruct (Hts h) as [h'' [? [? ?]]]; [split |].
    - apply (PrFamily.rf_sound _ _ s2) in H0; auto.
    - intros.
      pose proof PrFamily.rf_partial_functionality _ _ s2 _ _ _ H0 H4; subst; simpl; auto.
    - pose proof PrFamily.rf_sound _ _ a1 _ _ H3.
      pose proof anti_chain_not_comparable' O1 _ _ H7 H5 (prefix_history_comparable _ _ _ H1 H4); subst h''.
      destruct (PrFamily.rf_complete _ _ s1 _ H5) as [?x ?].
      specialize (H6 _ H8).
      specialize (H h' _ _ H8 H3).
      clear - H H6.
      destruct H as [[? ?] [? ?]].
      destruct x2; try inversion H6; split; split; try congruence; intros.
      * apply H0 in H3; inversion H3.
      * apply H2 in H3; inversion H3.
Qed.
*)
End ProgState.
  


