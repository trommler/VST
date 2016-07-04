Require Import Coq.Sets.Ensembles.
Require Import RndHoare.axiom. Import RndHoare.axiom.NatChoice.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.
Require Import RndHoare.history_anti_chain.
Require Import RndHoare.max_anti_chain.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.

Class HistoryBasedSigF (ora: RandomOracle) {SFo: SigmaAlgebraFamily RandomHistory} := {
  measurable_subspace_legal: forall P, is_measurable_subspace P -> LegalHistoryAntiChain P;
  RandomVarDomain := measurable_subspace;
  RandomVarDomain_HistoryAntiChain (Omega: RandomVarDomain): HistoryAntiChain := Build_HistoryAntiChain _ (proj1_sig Omega) (measurable_subspace_legal _ (proj2_sig Omega));
  is_measurable_subspace_same_covered: forall P Q: HistoryAntiChain, same_covered_anti_chain P Q -> is_measurable_subspace P -> is_measurable_subspace Q;
  is_measurable_set_same_covered: forall (O1 O2: RandomVarDomain) (P1 P2: HistoryAntiChain), Included P1 (RandomVarDomain_HistoryAntiChain O1) -> Included P2 (RandomVarDomain_HistoryAntiChain O2) -> same_covered_anti_chain (RandomVarDomain_HistoryAntiChain O1) (RandomVarDomain_HistoryAntiChain O2) -> same_covered_anti_chain P1 P2 -> PrFamily.is_measurable_set P1 O1 -> PrFamily.is_measurable_set P2 O2;
  max_anti_chain_measurable: forall P, is_max_anti_chain P -> is_measurable_subspace P
}.

Lemma is_measurable_set_same_covered1: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain) (P1 P2: HistoryAntiChain), Included P1 (RandomVarDomain_HistoryAntiChain Omega) -> Included P2 (RandomVarDomain_HistoryAntiChain Omega) -> same_covered_anti_chain P1 P2 -> PrFamily.is_measurable_set P1 Omega -> PrFamily.is_measurable_set P2 Omega.
Proof.
  intros.
  eapply is_measurable_set_same_covered.
  + exact H.
  + exact H0.
  + reflexivity.
  + exact H1.
  + auto.
Qed.

Lemma is_measurable_set_same_covered2: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (O1 O2: RandomVarDomain) (P: Ensemble RandomHistory), Included P (RandomVarDomain_HistoryAntiChain O1) -> Included P (RandomVarDomain_HistoryAntiChain O2) -> same_covered_anti_chain (RandomVarDomain_HistoryAntiChain O1) (RandomVarDomain_HistoryAntiChain O2) -> PrFamily.is_measurable_set P O1 -> PrFamily.is_measurable_set P O2.
Proof.
  intros.
  assert (LegalHistoryAntiChain P).
  + eapply LegalHistoryAntiChain_Included; eauto.
    apply (raw_anti_chain_legal _).
  + change P with (Build_HistoryAntiChain _ P H3: Ensemble RandomHistory).
    eapply (is_measurable_set_same_covered O1 O2 (Build_HistoryAntiChain _ P H3)).
    - exact H.
    - exact H0.
    - auto.
    - reflexivity.
    - auto.
Qed.

Section RandomVariable.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory}.

Global Coercion RandomVarDomain_HistoryAntiChain: RandomVarDomain >-> HistoryAntiChain.

Lemma RandomVarDomain_extensionality {HBSFo: HistoryBasedSigF ora} (O1 O2: RandomVarDomain):
  (forall h, O1 h <-> O2 h) ->
  O1 = O2.
Proof.
  intros.
  destruct O1, O2.
  assert (x = x0).
  Focus 1. {
    extensionality h.
    apply prop_ext; auto.
  } Unfocus.
  subst.
  assert (i = i0) by (apply proof_irrelevance).
  subst.
  auto.
Qed.

Tactic Notation "RandomVarDomain_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply RandomVarDomain_extensionality; intro x
  end.

Definition RandomVariable {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain) (A: Type) {SA: SigmaAlgebra A}: Type := PrFamily.MeasurableFunction Omega A.

Global Identity Coercion RandomVariable_MeasurableFunction: RandomVariable >-> PrFamily.MeasurableFunction.

Definition MeasurableSubset {HBSFo: HistoryBasedSigF ora} (Omega: RandomVarDomain): Type := PrFamily.measurable_set Omega.

Definition MeasurableSubset_HistoryAntiChain {HBSFo: HistoryBasedSigF ora} {Omega: RandomVarDomain} (P: MeasurableSubset Omega): HistoryAntiChain.
  exists (PrFamily.measurable_set_Ensemble Omega P).
  assert (Included (PrFamily.measurable_set_Ensemble Omega P) Omega).
  + exact (PrFamily.measurable_set_measurable_subspace _ _).
  + eapply LegalHistoryAntiChain_Included; eauto.
    apply measurable_subspace_legal.
    destruct Omega; auto.
Defined.
Global Coercion MeasurableSubset_HistoryAntiChain: MeasurableSubset >-> HistoryAntiChain.

Context {HBSFo: HistoryBasedSigF ora}.

Lemma MeasurableSubset_in_domain: forall (Omega: RandomVarDomain) (P: MeasurableSubset Omega) h,
  P h ->
  Omega h.
Proof.
  intros.
  eapply PrFamily.measurable_set_measurable_subspace.
  exact H.
Qed.

(* TODO: check whether this is necessary. *)
Definition undistinguishable_sub_domain (O1 O2: RandomVarDomain): Prop :=
  Included O1 O2 /\
  ~ is_measurable_subspace (Intersection _ O2 (Complement _ O1)).

Definition RandomVar_local_equiv {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) (h1 h2: RandomHistory): Prop := forall a, v1 h1 a <-> v2 h2 a.

Lemma local_equiv_domain_equiv: forall {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) h1 h2, RandomVar_local_equiv v1 v2 h1 h2 -> (O1 h1 <-> O2 h2).
Proof.
  intros.
  split; intros.
  + apply (PrFamily.rf_complete _ _ v1) in H0.
    destruct H0 as [? ?].
    specialize (H x).
    rewrite H in H0.
    apply PrFamily.rf_sound in H0; auto.
  + apply (PrFamily.rf_complete _ _ v2) in H0.
    destruct H0 as [? ?].
    specialize (H x).
    rewrite <- H in H0.
    apply PrFamily.rf_sound in H0; auto.
Qed.

Definition RandomVar_global_equiv {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A): Prop := forall h, RandomVar_local_equiv v1 v2 h h.

Lemma global_equiv_domain_equal: forall {O1} {O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A), RandomVar_global_equiv v1 v2 -> O1 = O2.
Proof.
  intros.
  RandomVarDomain_extensionality h.
  split; intros.
  + apply (PrFamily.rf_complete _ _ v1) in H0.
    destruct H0 as [? ?].
    specialize (H h x).
    rewrite H in H0.
    apply PrFamily.rf_sound in H0; auto.
  + apply (PrFamily.rf_complete _ _ v2) in H0.
    destruct H0 as [? ?].
    specialize (H h x).
    rewrite <- H in H0.
    apply PrFamily.rf_sound in H0; auto.
Qed.

Lemma global_equiv_refl: forall {Omega} {A: Type} {SA: SigmaAlgebra A} (v: RandomVariable Omega A), RandomVar_global_equiv v v.
Proof.
  intros.
  hnf; intros.
  hnf; intros.
  reflexivity.
Qed.

Lemma global_equiv_sym: forall {O1 O2} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A), RandomVar_global_equiv v1 v2 -> RandomVar_global_equiv v2 v1.
Proof.
  intros.
  hnf; intros. specialize (H h).
  hnf; intros. specialize (H a).
  tauto.
Qed.

Lemma global_equiv_trans: forall {O1 O2 O3} {A: Type} {SA: SigmaAlgebra A} (v1: RandomVariable O1 A) (v2: RandomVariable O2 A) (v3: RandomVariable O3 A), RandomVar_global_equiv v1 v2 -> RandomVar_global_equiv v2 v3 -> RandomVar_global_equiv v1 v3.
Proof.
  intros.
  hnf; intros. specialize (H h). specialize (H0 h).
  hnf; intros. specialize (H a). specialize (H0 a).
  tauto.
Qed.

Definition unit_space_domain: RandomVarDomain :=
  exist is_measurable_subspace unit_space_anti_chain (max_anti_chain_measurable _ unit_anti_chain_max).
  
Definition constant_var (Omega: RandomVarDomain) {A: Type} (v: A) {SA: SigmaAlgebra A}: RandomVariable Omega A := PrFamily.MeasurableFunction_inv (ConstantFunction v).

Definition unit_space_var {A: Type} (v: A) {SA: SigmaAlgebra A}: RandomVariable unit_space_domain A := constant_var _ v.

Definition RandomVarMap {Omega: RandomVarDomain} {A B: Type} {SA: SigmaAlgebra A} {SB: SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A): RandomVariable Omega B := PrFamily.Compose f v.

Lemma RandomVarMap_sound: forall {Omega: RandomVarDomain} {A B: Type} {SA: SigmaAlgebra A} {SB: SigmaAlgebra B} (f: MeasurableFunction A B) (v: RandomVariable Omega A) h b,
  RandomVarMap f v h b <-> exists a, v h a /\ f a b.
Proof. intros. apply PrFamily.Compose_spec; auto. Qed.

Opaque RandomVarMap.

Definition post_dom_var (O1 O2: RandomVarDomain) (Hf: future_anti_chain O1 O2) (Hs: same_covered_anti_chain O1 O2) {A: Type} {SA: SigmaAlgebra A}: RandomVariable O1 A -> RandomVariable O2 A.
  refine (fun f => PrFamily.Build_MeasurableFunction _ _ _ (fun h a => O2 h /\ exists h', prefix_history h' h /\ f h' a) _ _ _ _).
  + intros h ? ? [? [h' [? ?]]] [_ [h'' [? ?]]].
    pose proof PrFamily.rf_sound _ _ f _ _ H1.
    pose proof PrFamily.rf_sound _ _ f _ _ H3.
    pose proof anti_chain_not_comparable' O1 _ _ H4 H5 (prefix_history_comparable _ _ _ H0 H2).
    subst h''.
    apply (PrFamily.rf_partial_functionality _ _ f _ _ _ H1 H3).
  + intros h ?.
    destruct (Hf h H) as [h' [? ?]].
    destruct (PrFamily.rf_complete _ _ f _ H1) as [b ?].
    exists b; split; [| exists h']; auto.
  + intros h ? [? [h' [? ?]]].
    auto.
  + intros.
    eapply PrFamily.is_measurable_set_proper; [| reflexivity |].
    - instantiate (1 := filter_anti_chain (fun h => covered_by h (filter_anti_chain (fun h => forall b, f h b -> P b) O1)) O2).
      rewrite Same_set_spec; intro h; simpl.
      split.
      * intros [? ?].
        split; auto.
        destruct (Hf _ H) as [h' [? ?]].
        exists h'; split; auto.
        split; auto.
        intros b ?; specialize (H0 b).
        apply H0; split; eauto.
      * intros [? [h' [? [? ?]]]].
        split; auto.
        intros b [? [h'' [? ?]]]; apply (H2 b); clear H2.
        pose proof PrFamily.rf_sound _ _ f _ _ H5.
        pose proof anti_chain_not_comparable' O1 _ _ H1 H2 (prefix_history_comparable _ _ _ H0 H4).
        subst h''; auto.
    - apply (is_measurable_set_same_covered O1 O2 (filter_anti_chain (fun h0 => forall b, f h0 b -> P b) O1)).
      * intros ? [? ?]; auto.
      * intros ? [? ?]; auto.
      * auto.
      * apply same_covered_future_anti_chain_subset1 with O1; auto.
        intros ? [? ?]; auto.
      * apply (PrFamily.rf_preserve _ _ f).
Qed.

Definition is_filter_var {Omega Omega': RandomVarDomain} {A: Type} {sA: SigmaAlgebra A} (v: RandomVariable Omega A) (v': RandomVariable Omega' A) :=
  forall h, Omega' h -> RandomVar_local_equiv v v' h h.
(*
Record HeredRandomVariable (A: Type) {SA: SigmaAlgebra A}: Type := {
  well_defined_dom: RandomVarDomain -> Prop;
  well_defined_mono: forall (O1 O2: RandomVarDomain), future_anti_chain O1 O2 -> well_defined_dom O1 -> well_defined_dom O2;
  ex_value: forall Omega: RandomVarDomain, well_defined_dom Omega -> RandomVariable Omega A;
  ex_value_hered: forall (O1 O2: RandomVarDomain) (H1: well_defined_dom O1) (H2: well_defined_dom O2) (h1: O1) (h2: O2),
    future_anti_chain O1 O2 ->
    prefix_history h1 h2 ->
    RandomVar_local_equiv (ex_value O1 H1) (ex_value O2 H2) h1 h2
}.
*)
End RandomVariable.

Module RV.

Section RV.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory}  {HBSFo: HistoryBasedSigF ora}.

Lemma PreImage_spec: forall {Omega: RandomVarDomain} {B: Type} {SB: SigmaAlgebra B} (f: RandomVariable Omega B) (P: sigma_algebra.measurable_set B) (h: RandomHistory), (PrFamily.PreImage_MSet f P: MeasurableSubset Omega) h <-> Omega h /\ forall b, f h b -> P b.
Proof. intros. apply PrFamily.PreImage_spec; auto. Qed.

Lemma Intersection_spec: forall {Omega: RandomVarDomain} (A B: MeasurableSubset Omega) (h: RandomHistory), (PrFamily.Intersection_MSet A B: MeasurableSubset Omega) h <-> A h /\ B h.
Proof. intros. apply PrFamily.Intersection_spec. Qed.

Lemma Union_spec: forall {Omega: RandomVarDomain} (A B: MeasurableSubset Omega) (h: RandomHistory), (PrFamily.Union_MSet A B: MeasurableSubset Omega) h <-> A h \/ B h.
Proof. intros. apply PrFamily.Union_spec. Qed.

End RV.

End RV.

Tactic Notation "RandomVarDomain_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply RandomVarDomain_extensionality; intro x
  end.


(*
Definition filter_var {ora: RandomOracle} {A: Type} (filter: RandomHistory -> Prop) (v: RandomVariable A): RandomVariable A.
  refine (Build_RandomVariable _ _
           (filter_domain filter (rv_domain _ v))
           (fun h a => raw_var _ v h a /\ filter h) _ _ _).
  + intros ? ? ? [? ?] [? ?].
    apply (raw_var_pf _ v h); auto.
  + intros ? ? [? ?].
    simpl; split; auto.
    apply (raw_var_sound _ v h a); auto.
  + intros ? [? ?].
    destruct (raw_var_complete _ v h H) as [a ?].
    exists a.
    split; auto.
Defined.

Definition preimage_domain {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): RandomVarDomain :=
  filter_domain (fun h => forall a, raw_var _ v h a -> P a) (rv_domain _ v).


*)