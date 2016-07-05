Require Export Coq.Reals.Rdefinitions.
Require Export Coq.Reals.Rfunctions.
Require Import RndHoare.axiom.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.probability_measure.

Local Open Scope R.

Class SigmaAlgebraFamily (Omega: Type): Type := {
  is_measurable_subspace: (Ensemble Omega) -> Prop;
  measurable_subspace: Type := {P: Ensemble Omega | is_measurable_subspace P};
  is_measurable_subspace_proper: Proper (Same_set ==> iff) is_measurable_subspace;
  sub_sigma_algebra: forall P: measurable_subspace, SigmaAlgebra {o: Omega | proj1_sig P o};
  is_measurable_subspace_consi: forall P Q: measurable_subspace, Included (proj1_sig Q) (proj1_sig P) -> @is_measurable_set {x: Omega | proj1_sig P x} (sub_sigma_algebra P) (sig_Set (proj1_sig Q) (proj1_sig P))
}.

Class ProbabilityMeasureFamily (Omega: Type) {SigFamily : SigmaAlgebraFamily Omega}: Type := {
  sub_measure: forall P: measurable_subspace, @ProbabilityMeasure {o: Omega | proj1_sig P o} (sub_sigma_algebra P)
}.

Definition measurable_subspace_Ensemble {U} {SigF: SigmaAlgebraFamily U}: measurable_subspace -> Ensemble U := @proj1_sig _ _.

Global Coercion measurable_subspace_Ensemble: measurable_subspace >-> Ensemble.

Module PrFamily.

Section ProbabilityMeasureFamily.

Context {U: Type} {SigF: SigmaAlgebraFamily U}.

Definition is_measurable_set (P: Ensemble U) (Omega: measurable_subspace): Prop := Included P Omega /\ @is_measurable_set {x: U | Omega x} (sub_sigma_algebra Omega) (sig_Set P Omega).

Lemma is_measurable_subspace_consi: forall (Omega Omega': measurable_subspace), Included Omega' Omega -> is_measurable_set Omega' Omega.
Proof.
  intros.
  split; auto.
  apply is_measurable_subspace_consi; auto.
Qed.

Lemma is_measurable_set_proper: Proper (Same_set ==> eq ==> iff) is_measurable_set.
Proof.
  intros.
  hnf; intros; hnf; intros.
  subst y0; rename x0 into Omega.
  unfold is_measurable_set.
  apply Morphisms_Prop.and_iff_morphism.
  + rewrite H; reflexivity.
  + apply is_measurable_set_proper.
    rewrite Same_set_spec; intros [u ?H]; unfold sig_Set; simpl.
    rewrite Same_set_spec in H; auto.
Qed.

Lemma countable_union_measurable: forall (Omega: measurable_subspace) P, (forall i, is_measurable_set (P i) Omega) -> is_measurable_set (Countable_Union _ P) Omega.
Proof.
  intros.
  unfold is_measurable_set in *.
  split.
  + unfold Included, Ensembles.In, Countable_Union.
    intros x [i ?].
    specialize (H i).
    destruct H as [? _].
    apply H; auto.
  + change (sig_Set (Countable_Union U P) Omega) with (Countable_Union _ (fun i => sig_Set (P i) Omega)).
    apply countable_union_measurable.
    intros.
    specialize (H i).
    destruct H as [_ ?]; auto.
Qed.

Lemma complement_measurable: forall (Omega: measurable_subspace) P, is_measurable_set P Omega -> is_measurable_set (Intersection _ Omega (Complement _ P)) Omega.
Proof.
  intros.
  unfold is_measurable_set in *.
  split.
  + apply Intersection1_Included, Included_refl.
  + eapply sigma_algebra.is_measurable_set_proper with (Complement _ (sig_Set P Omega)).
    - rewrite Same_set_spec; intros [x ?].
      unfold Complement, Ensembles.In, sig_Set; simpl.
      rewrite Intersection_spec.
      tauto.
    - apply complement_measurable; tauto.
Qed.

Definition measurable_set (Omega: measurable_subspace): Type := {P: Ensemble U | is_measurable_set P Omega}.

Definition measurable_set_Ensemble (Omega: measurable_subspace): measurable_set Omega -> Ensemble U := @proj1_sig _ _.

Global Coercion measurable_set_Ensemble: measurable_set >-> Ensemble.

Definition measurable_set_inj {Omega: measurable_subspace} (P: measurable_set Omega): @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega) :=
  exist sigma_algebra.is_measurable_set (sig_Set (proj1_sig P) (proj1_sig Omega)) (proj2 (proj2_sig P)).

Definition measurable_set_inv {Omega: measurable_subspace} (P: @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega)): measurable_set Omega.
  exists (unsig_Set P).
  unfold is_measurable_set.
  split; [apply unsig_Set_Included |].
  unfold sig_Set, unsig_Set.
  destruct P as [P ?H]; simpl.
  eapply sigma_algebra.is_measurable_set_proper; [| eassumption].
  split; hnf; unfold In; intros.
  + destruct x, H0; simpl in *.
    assert (p = x0) by (apply proof_irrelevance; auto); subst; auto.
  + exists (proj2_sig x).
    destruct x; simpl; auto.
Defined.

Lemma measurable_set_inj_spec: forall {Omega: measurable_subspace} (P: measurable_set Omega) x, measurable_set_inj P x <-> P (proj1_sig x).
Proof.
  intros.
  split; intros.
  + destruct x; auto.
  + simpl. auto.
Qed.

Lemma measurable_set_inv_spec: forall {Omega: measurable_subspace} (P: @sigma_algebra.measurable_set _ (sub_sigma_algebra Omega)) x, measurable_set_inv P x <-> unsig_Set P x.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Record MeasurableFunction (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B}: Type := {
  raw_function: U -> B -> Prop;
  rf_partial_functionality: forall a b1 b2, raw_function a b1 -> raw_function a b2 -> b1 = b2;
  rf_complete: forall a, Omega a -> exists b, raw_function a b;
  rf_sound: forall a b, raw_function a b -> Omega a;
  rf_preserve: forall (P: sigma_algebra.measurable_set B), is_measurable_set (fun a => Omega a /\ forall b, raw_function a b -> P b) Omega
}.

Definition MeasurableFunction_raw_function (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B): U -> B -> Prop := raw_function _ _ f.

Coercion MeasurableFunction_raw_function: MeasurableFunction >-> Funclass.

Lemma MeasurableFunction_extensionality: forall {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f g: MeasurableFunction Omega B), (forall x b, f x b <-> g x b) -> f = g.
Proof.
  intros.
  destruct f as [f ?H ?H ?H ?H], g as [g ?H ?H ?H ?H].
  assert (f = g) by (extensionality x; extensionality b; apply prop_ext; auto); subst g.
  assert (H0 = H4) by (apply proof_irrelevance).
  assert (H1 = H5) by (apply proof_irrelevance).
  assert (H2 = H6) by (apply proof_irrelevance).
  assert (H3 = H7) by (apply proof_irrelevance).
  subst. reflexivity.
Qed.
  
Lemma rf_preserve_proof_minus1: forall (Omega: measurable_subspace) (B: Type) {SB: SigmaAlgebra B} (f: U -> B -> Prop) b0,
  let P0 := eq b0 in
  sigma_algebra.is_measurable_set P0 ->
  (forall x b1 b2, f x b1 -> f x b2 -> b1 = b2) ->
  (forall x, Omega x -> exists b, f x b) ->
  (forall (P: sigma_algebra.measurable_set B), Included P (fun b => b0 <> b) -> is_measurable_set (fun a => Omega a /\ forall b, f a b -> P b) Omega) ->
  (forall (P: sigma_algebra.measurable_set B), is_measurable_set (fun a => Omega a /\ forall b, f a b -> P b) Omega).
Proof.
  intros.
  destruct (classic (P b0)).
  Focus 2. {
    apply H2.
    unfold Included, Ensembles.In.
    intros; intro.
    subst x; auto.
  } Unfocus.
  unfold is_measurable_set.
  split.
  1: unfold Included, Ensembles.In; intros; simpl in H4; tauto.

  rename P0 into _P0.
  set (P0 := (exist _ _P0 H): sigma_algebra.measurable_set B).
  set (Pc := Intersection_MSet _ P (Complement_MSet _ P0)).
  apply sigma_algebra.is_measurable_set_proper 
    with (Union _
             (sig_Set (fun a => Omega a /\ (forall b : B, f a b -> Pc b)) Omega)
             (Complement _ (sig_Set (fun a => Omega a /\ (forall b : B, f a b -> (Complement_MSet _ P0) b)) Omega))).
  + rewrite Same_set_spec; intros x.
    rewrite Union_spec; unfold Complement, Ensembles.In.
    destruct x as [x ?H]; unfold sig_Set; simpl.
    assert ((forall b : B, f x b -> P b) <-> (forall b : B, f x b -> Intersection B P (Complement B _P0) b) \/ ~ (forall b : B, f x b -> (Complement_MSet _ P0) b)); [| tauto].
    split; intros.
    - destruct (classic (forall b, f x b -> b0 = b)).
      * right; intro.
        destruct (H1 x H4) as [b ?].
        specialize (H6 _ H8); specialize (H7 _ H8).
        subst b; auto.
        apply H7.
        subst P0 _P0; simpl; reflexivity.
      * left.
        intros.
        specialize (H5 _ H7).
        unfold P0; rewrite Intersection_spec; split; auto.
        intro; apply H6; intros.
        subst P0 _P0; simpl in H8. rewrite <- H8 in H7; clear b H5 H8.
        apply (H0 x b0 b1 H7 H9).
    - destruct H5.
      * specialize (H5 _ H6).
        rewrite Intersection_spec in H5.
        destruct H5; auto.
      * apply NNPP; intro.
        apply H5; intros.
        pose proof (H0 x b b1 H6 H8); subst b1.
        intro; apply H7.
        subst P0 _P0; simpl in H9.
        rewrite <- H9; auto.
  + apply union_measurable; [| apply sigma_algebra.complement_measurable].
    - apply H2.
      unfold Included, Ensembles.In; intros.
      subst Pc; simpl in H4.
      rewrite Intersection_spec in H4; destruct H4; auto.
    - apply H2.
      apply Included_refl.
Qed.

Definition MeasurableFunction_inj {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B): @measurable_function.MeasurableFunction _ B (sub_sigma_algebra Omega) _.
  apply (measurable_function.Build_MeasurableFunction _ _ _ _ (fun a b => f (proj1_sig a) b)).
  + intros [a ?] ? ? ? ?; simpl in *.
    apply (rf_partial_functionality _ _ f a b1 b2); auto.
  + intros [a ?]; simpl in *.
    destruct (rf_complete _ _ f a p) as [b ?H].
    exists b; auto.
  + intros; simpl.
    pose proof (rf_preserve _ _ f P).
    destruct H as [_ ?].
    eapply sigma_algebra.is_measurable_set_proper; [| eassumption].
    rewrite Same_set_spec; intros [a ?H]; unfold sig_Set; simpl.
    split; intros; auto.
    destruct H1; auto.
Defined.

Definition MeasurableFunction_inv {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: @measurable_function.MeasurableFunction _ B (sub_sigma_algebra Omega) _): MeasurableFunction Omega B.
  apply (Build_MeasurableFunction _ _ _ (fun a b => exists a0, proj1_sig a0 = a /\ f a0 b)).
  + intros ? ? ? [[? ?] [? ?]] [[? ?] [? ?]].
    simpl in *; subst.
    assert (p = p0) by (apply proof_irrelevance; auto); subst.
    apply (measurable_function.rf_functionality _ _ _ _ _ _ H0 H2).
  + intros ? ?.
    destruct (measurable_function.rf_complete _ _ f (exist _ a H)) as [b ?H].
    exists b, (exist _ a H); auto.
  + intros ? ? [[? ?] [? ?]].
    simpl in *; subst; auto.
  + intros.
    pose proof measurable_function.rf_preserve _ _ f P.
    unfold is_measurable_set.
    split.
    - unfold Included, Ensembles.In; simpl; intros. tauto.
    - eapply sigma_algebra.is_measurable_set_proper; [| eassumption].
      rewrite Same_set_spec; intros [a ?H]; unfold sig_Set; simpl.
      split; intros.
      * destruct H1 as [_ ?].
        apply H1.
        exists (exist _ a H0); split; auto.
      * split; auto.
        intros; apply H1.
        destruct H2 as [[? ?] [? ?]]; simpl in *.
        subst a; auto.
        assert (H0 = p) by (apply proof_irrelevance); subst p; auto.
Defined.

Lemma measurable_set_measurable_subspace: forall (Omega: measurable_subspace) (A: measurable_set Omega) x, A x -> Omega x.
Proof.
  intros.
  destruct A as [A [? ?]].
  auto.
Qed.

Definition Compose {Omega: measurable_subspace} {B C: Type} {SB: SigmaAlgebra B} {SC: SigmaAlgebra C} (g: measurable_function.MeasurableFunction B C) (f: MeasurableFunction Omega B): MeasurableFunction Omega C := MeasurableFunction_inv (measurable_function.Compose g (MeasurableFunction_inj f)).

Definition PreImage_MSet {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B) (P: sigma_algebra.measurable_set B): measurable_set Omega := measurable_set_inv (PreImage_MSet (MeasurableFunction_inj f) P).

Lemma PreImage_spec: forall {Omega: measurable_subspace} {B: Type} {SB: SigmaAlgebra B} (f: MeasurableFunction Omega B) (P: sigma_algebra.measurable_set B) x, PreImage_MSet f P x <-> Omega x /\ forall b, f x b -> P b.
Proof.
  intros.
  unfold PreImage_MSet.
  rewrite measurable_set_inv_spec.
  split; intros [? ?].
  + split; auto.
  + exists H; auto.
Qed.

Definition Intersection_MSet {Omega: measurable_subspace} (A B: measurable_set Omega): measurable_set Omega :=
  measurable_set_inv (sigma_algebra.Intersection_MSet _ (measurable_set_inj A) (measurable_set_inj B)).

Lemma Intersection_spec: forall {Omega: measurable_subspace} (A B: measurable_set Omega) x, Intersection_MSet A B x <-> A x /\ B x.
Proof.
  intros.
  unfold Intersection_MSet.
  rewrite measurable_set_inv_spec.
  split; intros [? ?].
  + simpl in H.
    rewrite Intersection_spec in H; destruct H.
    split; auto.
  + assert (Omega x) by (eapply measurable_set_measurable_subspace; eauto).
    exists H1.
    split; auto.
Qed.

Lemma intersection_measurable: forall (Omega: measurable_subspace) P Q, is_measurable_set P Omega -> is_measurable_set Q Omega -> is_measurable_set (Intersection _ P Q) Omega.
Proof.
  intros.
  pose (P' := exist _ P H: measurable_set Omega).
  pose (Q' := exist _ Q H0: measurable_set Omega).
  pose proof Intersection_spec P' Q'.
  eapply is_measurable_set_proper; [| reflexivity | apply (proj2_sig (Intersection_MSet P' Q'))].
  rewrite Same_set_spec; intro x.
  rewrite Ensembles_ext.Intersection_spec; specialize (H1 x). tauto.
Qed.

Definition Union_MSet {Omega: measurable_subspace} (A B: measurable_set Omega): measurable_set Omega :=
  measurable_set_inv (sigma_algebra.Union_MSet _ (measurable_set_inj A) (measurable_set_inj B)).

Lemma Union_spec: forall {Omega: measurable_subspace} (A B: measurable_set Omega) x, Union_MSet A B x <-> A x \/ B x.
Proof.
  intros.
  unfold Union_MSet.
  rewrite measurable_set_inv_spec.
  split.
  + intros [? ?].
    simpl in H.
    rewrite Union_spec in H; destruct H; [left | right]; auto.
  + intros [? | ?].
    - assert (Omega x) by (eapply measurable_set_measurable_subspace; eauto).
      exists H0.
      left; auto.
    - assert (Omega x) by (eapply measurable_set_measurable_subspace; eauto).
      exists H0.
      right; auto.
Qed.

Lemma union_measurable: forall (Omega: measurable_subspace) P Q, is_measurable_set P Omega -> is_measurable_set Q Omega -> is_measurable_set (Union _ P Q) Omega.
Proof.
  intros.
  pose (P' := exist _ P H: measurable_set Omega).
  pose (Q' := exist _ Q H0: measurable_set Omega).
  pose proof Union_spec P' Q'.
  eapply is_measurable_set_proper; [| reflexivity | apply (proj2_sig (Union_MSet P' Q'))].
  rewrite Same_set_spec; intro x.
  rewrite Ensembles_ext.Union_spec; specialize (H1 x). tauto.
Qed.

Definition Empty_MSet {Omega: measurable_subspace}: measurable_set Omega :=
  measurable_set_inv (sigma_algebra.Empty_MSet _).

Lemma Empty_set_spec: forall {Omega: measurable_subspace} x, @Empty_MSet Omega x <-> Empty_set _ x.
Proof.
  intros.
  unfold Empty_MSet.
  rewrite measurable_set_inv_spec.
  split.
  + intros [? ?].
    simpl in H.
    rewrite Empty_set_spec in H; inversion H.
  + intros [].
Qed.

Lemma empty_measurable: forall (Omega: measurable_subspace), is_measurable_set (Empty_set _) Omega.
Proof.
  intros.
  pose proof @Empty_set_spec Omega.
  eapply is_measurable_set_proper; [| reflexivity | apply (proj2_sig (@Empty_MSet Omega))].
  rewrite Same_set_spec; intro x.
  symmetry; exact (Empty_set_spec _).
Qed.

Lemma intersection_const_measurable: forall (Omega: measurable_subspace) (P: Prop) Q, is_measurable_set Q Omega -> is_measurable_set (Intersection _ (fun h => P) Q) Omega.
Proof.
  intros.
  destruct (classic P).
  + eapply is_measurable_set_proper; [| reflexivity | eassumption].
    rewrite Same_set_spec; intros h. rewrite Ensembles_ext.Intersection_spec; tauto.
  + eapply is_measurable_set_proper; [| reflexivity | apply empty_measurable].
    rewrite Same_set_spec; intros h. rewrite Ensembles_ext.Intersection_spec; tauto.
Qed.

Lemma Compose_spec: forall {Omega: measurable_subspace} {B C: Type} {SB: SigmaAlgebra B} {SC: SigmaAlgebra C} (g: measurable_function.MeasurableFunction B C) (f: MeasurableFunction Omega B) x c, Compose g f x c <-> exists b, f x b /\ g b c.
Proof.
  intros.
  unfold Compose.
  split; intros.
  + unfold MeasurableFunction_inv, MeasurableFunction_inj in H; simpl in H.
    destruct H as [[? ?] [? [? [? ?]]]].
    subst.
    exists x1; auto.
  + destruct H as [? [? ?]].
    pose proof rf_sound _ _ f x _ H.
    exists (exist _ x H1); simpl.
    split; auto.
    exists x0; auto.
Qed.

Lemma Compose_assoc: forall {Omega: measurable_subspace} {B C D: Type} {SB: SigmaAlgebra B} {SC: SigmaAlgebra C} {SD: SigmaAlgebra D} (h: measurable_function.MeasurableFunction C D) (g: measurable_function.MeasurableFunction B C) (f: MeasurableFunction Omega B), Compose h (Compose g f) = Compose (measurable_function.Compose h g) f.
Proof.
  intros.
  apply MeasurableFunction_extensionality; intros x d.
  rewrite !Compose_spec.
  split; intros.
  + destruct H as [c [? ?]].
    rewrite Compose_spec in H.
    destruct H as [b [? ?]].
    exists b.
    split; auto.
    exists c; auto.
  + destruct H as [b [? [c [? ?]]]].
    exists c; split; auto.
    rewrite Compose_spec; exists b; auto.
Qed.

Context {PrF: ProbabilityMeasureFamily U}.

Definition Probability {Omega: measurable_subspace} (P: measurable_set Omega): R := Probability (sub_measure Omega) (measurable_set_inj P).

Definition Expectation {Omega: measurable_subspace} (f: MeasurableFunction Omega R): R := Expectation (sub_measure Omega) (MeasurableFunction_inj f).

Definition GeneratedProbabilityMeasure {Omega: measurable_subspace} {A: Type} {sA: SigmaAlgebra A} (f: MeasurableFunction Omega A): ProbabilityMeasure A := GeneratedProbabilityMeasure (MeasurableFunction_inj f) (sub_measure Omega).

End ProbabilityMeasureFamily.

End PrFamily.

Global Coercion PrFamily.MeasurableFunction_raw_function: PrFamily.MeasurableFunction >-> Funclass.
Global Coercion PrFamily.measurable_set_Ensemble: PrFamily.measurable_set >-> Ensemble.

Class IsDisintegration {OMEGA} {SigF: SigmaAlgebraFamily OMEGA} {PrF: ProbabilityMeasureFamily OMEGA} (Omega: measurable_subspace) {A: Type} {SA: SigmaAlgebra A} (pi: PrFamily.MeasurableFunction Omega A) (E: PrFamily.measurable_set Omega) (A': measurable_set A): Type := {
  defined_almost_everywhere: Probability (PrFamily.GeneratedProbabilityMeasure pi) A' = 1;
  defined_MSS: forall a, A' a -> is_measurable_subspace (Intersection _ Omega (fun o => pi o a));
  proj_MSS := fun a def => exist is_measurable_subspace _ (defined_MSS a def) : measurable_subspace;
  defined_MS: forall a def, PrFamily.is_measurable_set (Intersection _ E (fun o => pi o a)) (proj_MSS a def);
  proj_MS := fun a def => exist (fun P => PrFamily.is_measurable_set P (proj_MSS a def)) _ (defined_MS a def): PrFamily.measurable_set (proj_MSS a def);
  defined_MF: exists (f: MeasurableFunction A R), (forall a (def: A' a), f a (PrFamily.Probability (proj_MS a def))) /\ Expectation (PrFamily.GeneratedProbabilityMeasure pi) f = PrFamily.Probability E
}.

Class ConsistentProbabilityMeasureFamily (OMEGA: Type) {SigF : SigmaAlgebraFamily OMEGA} {PrF: ProbabilityMeasureFamily OMEGA}: Type := {
  consi_disint: forall {Omega: measurable_subspace} {A: Type} {SA: SigmaAlgebra A} (pi: PrFamily.MeasurableFunction Omega A) (E: PrFamily.measurable_set Omega), exists A', IsDisintegration Omega pi E A'
}.

