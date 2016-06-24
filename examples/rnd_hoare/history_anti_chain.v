Require Import Coq.omega.Omega.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RndHoare.axiom. Import RndHoare.axiom.NatChoice.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.

(* TODO: put this in lib *)
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Definition history_set_consi {ora: RandomOracle} (P: RandomHistory -> Prop) : Prop :=
  forall h1 h2,
    conflict_history h1 h2 ->
    P h1 ->
    P h2 ->
    False.

Class LegalHistoryAntiChain {ora: RandomOracle} (d: RandomHistory -> Prop) : Prop := {
  rand_consi: history_set_consi d
}.

Record HistoryAntiChain {ora: RandomOracle}: Type := {
  raw_anti_chain: RandomHistory -> Prop;
  raw_anti_chain_legal: LegalHistoryAntiChain raw_anti_chain
}.

Definition in_anti_chain {ora: RandomOracle} (d: HistoryAntiChain) (h: RandomHistory): Prop := raw_anti_chain d h.

Coercion in_anti_chain: HistoryAntiChain >-> Funclass.

Definition history_in_anti_chain{ora: RandomOracle} (d: HistoryAntiChain) : Type := {h: RandomHistory | d h}.

Coercion history_in_anti_chain: HistoryAntiChain >-> Sortclass.

Definition history_in_anti_chain_history {ora: RandomOracle} (d: HistoryAntiChain) : history_in_anti_chain d -> RandomHistory := @proj1_sig _ _.

Coercion history_in_anti_chain_history: history_in_anti_chain >-> RandomHistory.

Lemma anti_chain_extensionality {ora: RandomOracle}: forall d1 d2: HistoryAntiChain, (forall h, d1 h <-> d2 h) -> d1 = d2.
Proof.
  intros.
  destruct d1 as [d1 [?H]], d2 as [d2 [?H]]; simpl in *.
  assert (d1 = d2) by (extensionality h; apply prop_ext; auto).
  subst d2.
  assert (H0 = H1) by (apply proof_irrelevance).
  subst H1.
  auto.
Qed.

Tactic Notation "anti_chain_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply anti_chain_extensionality; intro x
  end.

Lemma LegalHistoryAntiChain_Included {ora: RandomOracle}: forall (d1 d2: RandomHistory -> Prop), (forall h, d1 h -> d2 h) -> LegalHistoryAntiChain d2 -> LegalHistoryAntiChain d1.
Proof.
  intros.
  destruct H0 as [?H].
  constructor.
  hnf; intros.
  specialize (H0 h1 h2).
  auto.
Qed.

(*
Definition join {ora: RandomOracle} {A: Type} (v1 v2 v: RandomVariable A): Prop :=
  forall h, (v1 h = None /\ v2 h = v h) \/ (v2 h = None /\ v1 h = v h).

Definition Forall_RandomHistory {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): Prop :=
  forall h,
    match v h with
    | None => True
    | Some a => P a
    end.
*)

Definition singleton_history_anti_chain {ora: RandomOracle} (h: RandomHistory): HistoryAntiChain.
  exists (fun h' => forall n, h n = h' n).
  constructor.
  hnf; intros; simpl in *.
  destruct H as [n [? ?]].
  specialize (H0 n).
  specialize (H1 n).
  hnf in H2.
  destruct (h n); rewrite <- H0, <- H1 in H2; auto.
Defined.

Definition unit_space_anti_chain {ora: RandomOracle}: HistoryAntiChain := singleton_history_anti_chain empty_history.

Definition filter_anti_chain {ora: RandomOracle} (filter: RandomHistory -> Prop) (d: HistoryAntiChain): HistoryAntiChain.
  exists (fun h => d h /\ filter h).
  constructor.
  destruct d as [d [H]].
  hnf; simpl; intros.
  apply (H h1 h2 H0); tauto.
Defined.

Definition covered_by {ora: RandomOracle} (h: RandomHistory) (d: HistoryAntiChain): Prop :=
  exists h', prefix_history h' h /\ d h'.

Definition n_bounded_covered_by {ora: RandomOracle} (n: nat) (h: RandomHistory) (d: HistoryAntiChain): Prop :=
  exists h', n_bounded_prefix_history n h' h -> d h'.

Definition future_anti_chain {ora: RandomOracle} (present future: HistoryAntiChain): Prop :=
  forall h, future h -> covered_by h present.

Definition n_bounded_future_anti_chain {ora: RandomOracle} (n: nat) (present future: HistoryAntiChain): Prop :=
  forall h, future h -> n_bounded_covered_by n h present.

Definition bounded_future_anti_chain {ora: RandomOracle} (present future: HistoryAntiChain): Prop :=
  exists n, n_bounded_future_anti_chain n present future.

Definition same_covered_anti_chain {ora: RandomOracle} (d1 d2: HistoryAntiChain): Prop :=
  forall h, is_inf_history h ->
    ((exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d1 h') <->
     (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d2 h')).

Definition subst_anti_chain {ora: RandomOracle} (P: RandomHistory -> Prop) (d1 d2: HistoryAntiChain): HistoryAntiChain.
  exists (fun h => d1 h /\ ~ P h \/ d2 h /\ covered_by h (filter_anti_chain P d1)).
  constructor.
  hnf; intros ? ? ? [? | ?] [? | ?].
  + apply (@rand_consi _ _ (raw_anti_chain_legal d1) h1 h2); tauto.
  + destruct H0 as [? ?], H1 as [? [h2' [? [? ?]]]].
    destruct (conflict_backward_right h1 h2' h2 H H3).
    - apply (@rand_consi _ _ (raw_anti_chain_legal d1) h1 h2'); tauto.
    - subst h2'; auto.
  + destruct H1 as [? ?], H0 as [? [h1' [? [? ?]]]].
    destruct (conflict_backward_left h2 h1' h1 H H3).
    - apply (@rand_consi _ _ (raw_anti_chain_legal d1) h1' h2); tauto.
    - subst h1'; auto.
  + apply (@rand_consi _ _ (raw_anti_chain_legal d2) h1 h2); tauto.
Defined.

Lemma anti_chain_not_comparable {ora: RandomOracle}: forall (d: HistoryAntiChain) h1 h2,
  d h1 ->
  d h2 ->
  prefix_history h1 h2 ->
  h1 = h2.
Proof.
  intros.
  pose proof (fun HH  => @rand_consi _ _ (raw_anti_chain_legal d) h1 h2 HH H H0).
  clear H H0.
  destruct (classic (exists n, h1 n <> h2 n)).
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n <> h2 n) (fun n => classic (_ n)) H.
    hnf in H0.
    destruct H0 as [n [[? ?] _]].
    exfalso; apply H2; clear H2.
    exists n; split.
    - hnf; intros.
      specialize (H3 m).
      destruct (classic (h1 m = h2 m)); auto.
      apply H3 in H4; omega.
    - destruct (H1 n); [| congruence].
      unfold n_conflict_history.
      rewrite H2.
      destruct (h2 n); auto; congruence.
  + history_extensionality n.
    destruct (classic (h1 n = h2 n)); auto; exfalso.
    apply H; exists n; auto.
Qed.

Lemma anti_chain_not_comparable' {ora: RandomOracle}: forall (d: HistoryAntiChain) h1 h2,
  d h1 ->
  d h2 ->
  prefix_history h1 h2 \/ prefix_history h2 h1 ->
  h1 = h2.
Proof.
  intros ? ? ? ? ? [? | ?]; [| symmetry]; apply (anti_chain_not_comparable d); auto.
Qed.

Lemma covered_by_is_element {ora: RandomOracle}: forall (d1 d2: HistoryAntiChain) h,
  d2 h ->
  Included d1 d2 ->
  (d1 h <-> covered_by h d1).
Proof.
  intros.
  split; intros.
  + exists h; split; auto.
    apply prefix_history_refl.
  + destruct H1 as [h' [? ?]].
    assert (d2 h') by (apply H0; auto).
    assert (h' = h) by (apply (anti_chain_not_comparable d2); auto).
    subst h'; auto.
Qed.

Instance same_covered_eq {ora: RandomOracle}: Equivalence same_covered_anti_chain.
Proof.
  constructor.
  + hnf; intros.
    hnf; intros.
    reflexivity.
  + hnf; intros.
    unfold same_covered_anti_chain in *; intros.
    specialize (H h H0); tauto.
  + hnf; intros.
    unfold same_covered_anti_chain in *; intros.
    specialize (H h H1); specialize (H0 h H1); tauto.
Qed.

Lemma prefix_history_covered {ora: RandomOracle}: forall d h1 h2,
  prefix_history h1 h2 ->
  covered_by h1 d ->
  covered_by h2 d.
Proof.
  intros.
  destruct H0 as [h0 [? ?]].
  exists h0; split; auto.
  eapply prefix_history_trans; eauto.
Qed.

Lemma future_anti_chain_refl {ora: RandomOracle}: forall d,
  future_anti_chain d d.
Proof.
  intros.
  unfold future_anti_chain.
  intros.
  exists h.
  split; auto.
  apply prefix_history_refl.
Qed.

Lemma future_anti_chain_trans {ora: RandomOracle}: forall d1 d2 d3,
  future_anti_chain d1 d2 ->
  future_anti_chain d2 d3 ->
  future_anti_chain d1 d3.
Proof.
  unfold future_anti_chain.
  intros.
  rename h into h3.
  destruct (H0 h3 H1) as [h2 [? ?]].
  apply (prefix_history_covered d1 h2 h3); auto.
Qed.

Lemma future_anti_chain_Included {ora: RandomOracle}: forall (l1 l2 r1 r2: HistoryAntiChain),
  Included l1 l2 ->
  Included r2 r1 ->
  future_anti_chain l1 r1 ->
  future_anti_chain l2 r2.
Proof.
  intros.
  hnf; intros.
  apply H0 in H2.
  apply H1 in H2.
  destruct H2 as [h' [? ?]].
  exists h'; split; auto.
  apply H; auto.
Qed.

Lemma proj_in_anti_chain_unique {ora: RandomOracle}: forall (d: HistoryAntiChain) h1 h2 h3,
  prefix_history h1 h3 ->
  prefix_history h2 h3 ->
  covered_by h2 d ->
  d h1 ->
  prefix_history h1 h2.
Proof.
  intros.
  pose proof prefix_history_comparable _ _ _ H H0.
  destruct H3; auto.
  destruct H1 as [h1' [? ?]].
  pose proof prefix_history_trans _ _ _ H1 H3.
  pose proof anti_chain_not_comparable _ _ _ H4 H2 H5.
  rewrite <- H6; auto.
Qed.

Lemma future_anti_chain_comparable_choice {ora: RandomOracle}: forall d1 d2 h1 h2,
  future_anti_chain d1 d2 ->
  d1 h1 ->
  d2 h2 ->
  prefix_history h1 h2 \/ prefix_history h2 h1 ->
  prefix_history h1 h2.
Proof.
  intros.
  destruct H2; auto.
  destruct (H h2 H1) as [h1' [? ?]].
  pose proof anti_chain_not_comparable d1 _ _ H4 H0 (prefix_history_trans _ _ _ H3 H2).
  subst h1'; auto.
Qed.

(* TODO: change these lemma name. not only spec/strong-spec. *)
Lemma same_covered_future_anti_chain_spec {ora: RandomOracle}: forall d1 d2,
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  forall h1, d1 h1 -> exists h2, prefix_history h1 h2 /\ d2 h2.
Proof.
  intros.
  set (h := app_history h1 default_inf_history).
  assert (is_inf_history h) by (apply app_history_inf_history_iff; right; apply default_inf_history_inf).

  pose proof proj1 (H h H2); clear H2; rename H3 into H2.
  assert (prefix_history h1 h) by apply prefix_app_history.
  assert (exists h' : RandomHistory, (prefix_history h' h \/ strict_conflict_history h' h) /\ d1 h').
  + clear H2.
    exists h1.
    split; [left |]; auto.
  + specialize (H2 H4); clear H4.
    destruct H2 as [h2 [? ?]].
    exists h2; split; [| auto].
    destruct (H0 h2 H4) as [h1' [? ?]].
    destruct H2.
    - apply (proj_in_anti_chain_unique d1 h1 h2 h); auto.
    - pose proof strict_conflict_backward_right h2 h1 h H2 H3.
      destruct H7; auto.
      pose proof strict_conflict_backward_conflict_left h1 h1' h2 H7 H5.
      pose proof @rand_consi _ _ (raw_anti_chain_legal d1) _ _ H8 H6 H1.
      inversion  H9.
Qed.

Lemma same_covered_future_anti_chain_strong_spec {ora: RandomOracle}: forall d1 d2,
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  forall h1 h,
  d1 h1 ->
  is_inf_history h ->
  prefix_history h1 h \/ strict_conflict_history h1 h ->
  exists h2, prefix_history h1 h2 /\ d2 h2 /\ (prefix_history h2 h \/ strict_conflict_history h2 h).
Proof.
  intros.
  destruct H3.
  + pose proof proj1 (H h H2) (ex_intro _ h1 (conj (or_introl H3) H1)).
    destruct H4 as [h2 [? ?]].
    exists h2.
    split; auto.
    pose proof H0 _ H5.
    destruct H6 as [h1' [? ?]].
    pose proof strict_conflict_or_prefix_backward_left _ _ _ H4 H6.
    destruct H8.
    - pose proof prefix_history_comparable _ _ _ H3 H8.
      apply comparable_conflict_or_equal in H9.
      destruct H9; [| subst h1'; auto].
      exfalso; apply (@rand_consi _ _ (raw_anti_chain_legal d1) _ _ H9 H1 H7).
    - pose proof strict_conflict_backward_right _ _ _ H8 H3.
      destruct H9.
      * pose proof anti_chain_not_comparable _ _ _ H1 H7 H9.
        subst h1; auto.
      * apply strict_conflict_conflict in H9.
        exfalso; apply (@rand_consi _ _ (raw_anti_chain_legal d1) _ _ H9 H7 H1).
  + pose proof same_covered_future_anti_chain_spec _ _ H H0 h1 H1.
    destruct H4 as [h2 [? ?]]; exists h2.
    split; [| split]; auto.
    right.
    eapply strict_conflict_forward_left; eauto.
Qed.  

Lemma same_covered_future_anti_chain_no_strict_conflict {ora: RandomOracle}: forall d1 d2 h1 h2,
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  d1 h1 ->
  d2 h2 ->
  strict_conflict_history h1 h2 ->
  False.
Proof.
  intros.
  destruct (same_covered_future_anti_chain_spec d1 d2 H H0 h1 H1) as [h2' [? ?]].
  pose proof strict_conflict_forward_left _ _ _ H3 H4.
  apply strict_conflict_conflict in H6.
  exact (@rand_consi _ _ (raw_anti_chain_legal d2) _ _ H6 H5 H2).
Qed.

Lemma same_covered_future_anti_chain_subset1 {ora: RandomOracle}: forall (d1' d1 d2: HistoryAntiChain),
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  Included d1' d1 ->
  same_covered_anti_chain d1' (filter_anti_chain (fun h => covered_by h d1') d2).
Proof.
  intros.
  hnf; intros h ?.
  split; intros [h' [? ?]].
  + pose proof same_covered_future_anti_chain_strong_spec d1 d2 H H0 h' h (H1 _ H4) H2 H3.
    destruct H5 as [h'' [? [? ?]]].
    exists h''; split; [| split]; auto.
    exists h'; auto.
  + destruct H4 as [? [h'' [? ?]]].
    exists h''; split; auto.
    eapply strict_conflict_or_prefix_backward_left; eauto.
Qed.

Lemma same_covered_future_anti_chain_subset2 {ora: RandomOracle}: forall (d1' d1 d2: HistoryAntiChain),
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  Included d1' d1 ->
  future_anti_chain d1' (filter_anti_chain (fun h => covered_by h d1') d2).
Proof.
  intros.
  hnf; intros.
  destruct H2 as [? [h' [? ?]]].
  exists h'; auto.
Qed.

Lemma subst_anti_chain_spec {ora: RandomOracle}: forall (P d1 d2: HistoryAntiChain) h,
  (forall h, P h -> d1 h) ->
  (subst_anti_chain P d1 d2 h <-> d1 h /\ ~ P h \/ d2 h /\ covered_by h P).
Proof.
  intros.
  simpl.
  apply Morphisms_Prop.or_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
  apply Morphisms_Prop.ex_iff_morphism; intros h'.
  apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
  simpl.
  specialize (H h'); tauto.
Qed.

Lemma subst_anti_chain_future {ora: RandomOracle}: forall P (d1 d2: HistoryAntiChain),
  future_anti_chain d1 (subst_anti_chain P d1 d2).
Proof.
  intros.
  hnf; intros.
  simpl in H.
  destruct H as [[? ?] | [? ?]].
  + exists h; split; auto.
    apply prefix_history_refl.
  + destruct H0 as [h' [? [? ?]]].
    exists h'; auto.
Qed.

Lemma subst_anti_chain_same_covered {ora: RandomOracle}: forall (P d1 d2: HistoryAntiChain),
  Included P d1 ->
  same_covered_anti_chain P (filter_anti_chain (fun h => covered_by h P) d2) ->
  same_covered_anti_chain d1 (subst_anti_chain P d1 d2).
Proof.
  intros.
  hnf; intros.
  split; intros [h' [? ?]].
  + destruct (classic (P h')).
    - pose proof proj1 (H0 _ H1).
      specialize (H5 (ex_intro _ h' (conj H2 H4))).
      destruct H5 as [h'' [? ?]].
      exists h''; split; auto.
      simpl in H6; right; auto.
      replace (filter_anti_chain P d1) with P; auto.
      anti_chain_extensionality h0; simpl.
      specialize (H h0); tauto.
    - exists h'; split; auto.
      left; auto.
  + destruct H3 as [[? ?] | [? ?]].
    - exists h'; auto.
    - destruct H4 as [h'' [? [? ?]]].
      exists h''; split; auto.
      eapply strict_conflict_or_prefix_backward_left; eauto.
Qed.

Lemma subst_anti_chain_same_covered' {ora: RandomOracle}: forall (P P' d1 d2: HistoryAntiChain),
  Included P d1 ->
  Included P P' ->
  same_covered_anti_chain P' d2 ->
  future_anti_chain P' d2 ->
  same_covered_anti_chain d1 (subst_anti_chain P d1 d2).
Proof.
  intros.
  apply subst_anti_chain_same_covered; auto.
  eapply same_covered_future_anti_chain_subset1; eauto.
Qed.

