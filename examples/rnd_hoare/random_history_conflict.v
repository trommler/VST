Require Import Coq.omega.Omega.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.List_ext.
Require Import RndHoare.axiom. Import RndHoare.axiom.NatChoice.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.

Definition history_coincide {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  forall m, m < n -> h1 m = h2 m.

Definition n_conflict_history {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  match h1 n, h2 n with
  | Some a1, Some a2 => projT1 a1 <> projT1 a2
  | Some _, None => True
  | None, Some _ => True
  | None, None => False
  end.

Definition conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n, history_coincide n h1 h2 /\ n_conflict_history n h1 h2.

Definition strict_conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    match h1 n, h2 n with
    | Some a1, Some a2 => projT1 a1 <> projT1 a2
    | _, _ => False
    end.

Lemma history_coincide_sym {ora: RandomOracle}: forall h1 h2 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h1.
Proof.
  intros.
  hnf; intros.
  specialize (H m H0); congruence.
Qed.

Lemma n_conflict_history_sym {ora: RandomOracle}: forall h1 h2 n,
  n_conflict_history n h1 h2 ->
  n_conflict_history n h2 h1.
Proof.
  intros.
  unfold n_conflict_history in *.
  destruct (h1 n), (h2 n); auto.
Qed.

Lemma conflict_history_sym {ora: RandomOracle}: forall h1 h2,
  conflict_history h1 h2 ->
  conflict_history h2 h1.
Proof.
  unfold conflict_history; intros.
  destruct H as [n [? ?]].
  exists n; split.
  + apply history_coincide_sym; auto.
  + hnf in H0 |- *; destruct (h1 n), (h2 n); auto.
Qed.

Lemma strict_conflict_history_sym {ora: RandomOracle}: forall h1 h2,
  strict_conflict_history h1 h2 ->
  strict_conflict_history h2 h1.
Proof.
  intros.
  destruct H as [n [? ?]].
  exists n; split; [apply history_coincide_sym; auto |].
  destruct (h1 n), (h2 n); auto.
Qed.

Lemma history_coincide_trans {ora: RandomOracle}: forall h1 h2 h3 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h3 ->
  history_coincide n h1 h3.
Proof.
  intros.
  hnf; intros.
  specialize (H m H1);
  specialize (H0 m H1); congruence.
Qed.

Lemma strict_conflict_conflict {ora: RandomOracle}: forall h1 h2,
  strict_conflict_history h1 h2 ->
  conflict_history h1 h2.
Proof.
  intros ? ? [n [? ?]]; exists n; split; auto.
  hnf; destruct (h1 n), (h2 n); auto.
Qed.

Lemma is_0_history_non_conflict {ora: RandomOracle}: forall h1 h2,
  is_n_history 0 h1 ->
  is_n_history 0 h2 ->
  conflict_history h1 h2 ->
  False.
Proof.
  intros.
  destruct H1 as [n [? ?]].
  destruct H as [? _], H0 as [? _].
  hnf in H2.
  rewrite (history_sound1 h1 0 n) in H2 by (auto; omega).
  rewrite (history_sound1 h2 0 n) in H2 by (auto; omega).
  auto.
Qed.

Lemma history_coincide_weaken {ora: RandomOracle}: forall n m h1 h2,
  n <= m ->
  history_coincide m h1 h2 ->
  history_coincide n h1 h2.
Proof.
  intros.
  intros n0 ?.
  apply H0.
  omega.
Qed.

Lemma fstn_history_coincide {ora: RandomOracle}: forall n h,
  history_coincide n h (fstn_history n h).
Proof.
  intros.
  intros m ?.
  rewrite fstn_history_Some by omega.
  auto.
Qed.

Lemma conflict_history_strict_conflict {ora: RandomOracle}: forall h h',
  conflict_history h' h ->
  prefix_history h h' \/ prefix_history h' h \/ strict_conflict_history h' h.
Proof.
  intros.
  destruct H as [n [? ?]].
  hnf in H0.
  destruct (h n) eqn:?H, (h' n) eqn:?H.
  + right; right.
    exists n.
    split; auto.
    rewrite H1, H2; auto.
  + right; left.
    hnf; intros.
    destruct (le_lt_dec n n0).
    - left.
      apply (history_sound1 h' n n0); auto.
    - right.
      apply H; auto.
  + left.
    hnf; intros.
    destruct (le_lt_dec n n0).
    - left.
      apply (history_sound1 h n n0); auto.
    - right.
      symmetry; apply H; auto.
  + inversion H0.
Qed.

Lemma conflict_history_inf_right {ora: RandomOracle}: forall h h',
  is_inf_history h ->
  conflict_history h' h ->
  prefix_history h' h \/ strict_conflict_history h' h.
Proof.
  intros.
  pose proof conflict_history_strict_conflict h h' H0.
  destruct H1; auto.
  exfalso.
  destruct H0 as [n [? ?]].
  specialize (H1 n).
  specialize (H n).
  hnf in H2.
  destruct (h n), (h' n), H1; auto; try congruence.
Qed.

Lemma n_conflict_proper_aux_right {ora: RandomOracle}: forall n h1 h2 h3,
  history_coincide (S n) h2 h3 ->
  (history_coincide n h1 h2 /\ n_conflict_history n h1 h2 <->
   history_coincide n h1 h3 /\ n_conflict_history n h1 h3).
Proof.
  intros.
  pose proof history_coincide_weaken n (S n) h2 h3 (le_n_Sn _) H.
  assert (history_coincide n h1 h2 <-> history_coincide n h1 h3).
  Focus 1. {
    split; intros; [apply history_coincide_trans with h2 | apply history_coincide_trans with h3]; auto.
    apply history_coincide_sym; auto.
  } Unfocus.
  assert (n_conflict_history n h1 h2 <-> n_conflict_history n h1 h3).
  Focus 1. {
    unfold n_conflict_history.
    specialize (H n (le_refl _)).
    rewrite H; reflexivity.
  } Unfocus.
  tauto.
Qed.

Lemma n_conflict_proper_aux_left {ora: RandomOracle}: forall n h1 h2 h3,
  history_coincide (S n) h2 h3 ->
  (history_coincide n h2 h1 /\ n_conflict_history n h2 h1 <->
   history_coincide n h3 h1 /\ n_conflict_history n h3 h1).
Proof.
  intros.
  pose proof n_conflict_proper_aux_right n h1 h2 h3 H.
  pose proof history_coincide_sym h1 h2 n.
  pose proof history_coincide_sym h2 h1 n.
  pose proof history_coincide_sym h1 h3 n.
  pose proof history_coincide_sym h3 h1 n.
  pose proof n_conflict_history_sym h1 h2 n.
  pose proof n_conflict_history_sym h2 h1 n.
  pose proof n_conflict_history_sym h1 h3 n.
  pose proof n_conflict_history_sym h3 h1 n.
  tauto.
Qed.

Lemma n_conflict_proper_aux {ora: RandomOracle}: forall n l1 l2 r1 r2,
  history_coincide (S n) l1 l2 ->
  history_coincide (S n) r1 r2 ->
  (history_coincide n l1 r1 /\ n_conflict_history n l1 r1 <->
   history_coincide n l2 r2 /\ n_conflict_history n l2 r2).
Proof.
  intros.
  rewrite (n_conflict_proper_aux_left n r1 l1 l2 H).
  apply n_conflict_proper_aux_right; auto.
Qed.

Lemma squeeze_history_coincide {ora: RandomOracle}: forall n h1 h2,
  prefix_history (fstn_history n h1) h2 ->
  prefix_history h2 h1 ->
  history_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m).
  rewrite fstn_history_Some in H by omega.
  destruct H, H0; congruence.
Qed.

Lemma comparable_conflict_or_equal {ora: RandomOracle}: forall h1 h2,
  prefix_history h1 h2 \/ prefix_history h2 h1 ->
  conflict_history h1 h2 \/ h1 = h2.
Proof.
  intros.
  destruct (classic (exists n, h1 n = None /\ h2 n <> None \/ h1 n <> None /\ h2 n = None)).
  + left.
    destruct (dec_inh_nat_subset_has_unique_least_element _ (fun n => (classic (_ n))) H0) as [n [[? ?] _]].
    clear H0.
    exists n; split.
    - hnf; intros.
      specialize (H2 m).
      destruct (h1 m) eqn:?H, (h2 m) eqn:?H.
      * destruct H; specialize (H m); rewrite H3, H4 in H; inversion H; auto; congruence.
      * assert (n <= m) by (apply H2; right; split; congruence); omega.
      * assert (n <= m) by (apply H2; left; split; congruence); omega.
      * auto.
    - hnf.
      destruct (h1 n) eqn:?H, (h2 n) eqn:?H; auto;
      inversion H1; inversion H4; congruence.
  + right.
    history_extensionality n.
    destruct (h1 n) eqn:?H, (h2 n) eqn:?H.
    - destruct H; specialize (H n); rewrite H1, H2 in H; inversion H; auto; congruence.
    - exfalso; apply H0; exists n; rewrite H1, H2; right; split; congruence.
    - exfalso; apply H0; exists n; rewrite H1, H2; left; split; congruence.
    - auto.
Qed.

Lemma strict_conflict_forward_left {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h1 h ->
  prefix_history h1 h2 ->
  strict_conflict_history h2 h.
Proof.
  intros.
  destruct H as [n [? ?]]; exists n; split.
  + apply history_coincide_trans with h1; auto.
    hnf; intros.
    specialize (H0 m).
    destruct H0; [| congruence].
    apply (history_sound1 h1 m n) in H0; [| omega].
    rewrite H0 in H1; inversion H1.
  + specialize (H0 n).
    destruct (h n), (h1 n), (h2 n); try solve [inversion H1].
    - destruct H0; [congruence | inversion H0; congruence].
    - inversion H0; congruence.
Qed.

Lemma strict_conflict_forward_right {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h h1 ->
  prefix_history h1 h2 ->
  strict_conflict_history h h2.
Proof.
  intros.
  apply strict_conflict_history_sym.
  apply strict_conflict_history_sym in H.
  eapply strict_conflict_forward_left; eauto.
Qed.

Lemma strict_conflict_backward_conflict_left {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h2 h ->
  prefix_history h1 h2 ->
  conflict_history h1 h.
Proof.
  intros.
  destruct H as [n [? ?]].
  destruct (h1 n) eqn:?H.
  + exists n.
    split.
    - apply history_coincide_trans with h2; auto.
      hnf; intros.
      specialize (H0 m).
      destruct H0; auto.
      apply (history_sound1 h1 m n) in H0; [| omega].
      congruence.
    - unfold n_conflict_history.
      specialize (H0 n).
      destruct H0; [congruence |].
      rewrite H2 in H0 |- *.
      rewrite <- H0 in H1.
      destruct (h n); auto.
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n = None) (fun n => classic (_ n)) (ex_intro _ n H2).
    destruct H3 as [m [[? ?] _]].
    exists m.
    split.
    - apply history_coincide_trans with h2; [| apply history_coincide_weaken with n; auto].
      hnf; intros.
      specialize (H0 m0); specialize (H4 m0).
      destruct H0; auto.
      apply H4 in H0.
      omega.
    - unfold n_conflict_history.
      rewrite H3.
      specialize (H4 _ H2).
      destruct (h m) eqn:?H; auto.
      apply (history_sound1 h m n H4) in H5.
      rewrite H5 in H1; destruct (h2 n); auto.
Qed.

Lemma strict_conflict_backward_conflict_right {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h h2 ->
  prefix_history h1 h2 ->
  conflict_history h h1.
Proof.
  intros.
  apply strict_conflict_history_sym in H.
  apply conflict_history_sym.
  eapply strict_conflict_backward_conflict_left; eauto.
Qed.

Lemma strict_conflict_backward_left {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h2 h ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h1 h.
Proof.
  intros.
  destruct H as [n [? ?]].
  destruct (h1 n) eqn:?H; [right | left].
  + exists n.
    split.
    - apply history_coincide_trans with h2; auto.
      hnf; intros.
      specialize (H0 m).
      destruct H0; auto.
      apply (history_sound1 h1 m n) in H0; [| omega].
      congruence.
    - unfold n_conflict_history.
      specialize (H0 n).
      destruct H0; [congruence |].
      rewrite H2 in H0 |- *.
      rewrite <- H0 in H1.
      destruct (h n); auto.
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n = None) (fun n => classic (_ n)) (ex_intro _ n H2).
    destruct H3 as [m [[? ?] _]].
    hnf; intros.
    destruct (le_dec m n0).
    - left; apply (history_sound1 h1 m n0 l); auto.
    - right.
      assert (h1 n0 <> None) by (destruct (h1 n0) eqn:?H; [| specialize (H4 _ H5)]; congruence).
      specialize (H0 n0); destruct H0; [congruence |].
      rewrite H0.
      apply H.
      destruct (le_dec n n0); [| omega].
      exfalso.
      apply H5.
      apply (history_sound1 h1 n n0 l); auto.
Qed.

Lemma strict_conflict_backward_right {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h h2 ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h h1.
Proof.
  intros.
  apply strict_conflict_history_sym in H.
  pose proof (strict_conflict_backward_left _ _ _ H H0).
  destruct H1; auto.
  apply strict_conflict_history_sym in H1; auto.
Qed.

Lemma strict_conflict_or_prefix_backward_left {ora: RandomOracle}: forall h h1 h2,
  prefix_history h2 h \/ strict_conflict_history h2 h ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h1 h.
Proof.
  intros.
  destruct H.
  + left; eapply prefix_history_trans; eauto.
  + eapply strict_conflict_backward_left; eauto.
Qed.

Lemma strict_conflict_or_prefix_backward_right {ora: RandomOracle}: forall h h1 h2,
  prefix_history h2 h \/ strict_conflict_history h h2 ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h h1.
Proof.
  intros.
  destruct H.
  + left; eapply prefix_history_trans; eauto.
  + eapply strict_conflict_backward_right; eauto.
Qed.

Lemma conflict_backward_left {ora: RandomOracle}: forall h h1 h2,
  conflict_history h2 h ->
  prefix_history h1 h2 ->
  conflict_history h1 h \/ h1 = h.
Proof.
  intros.
  destruct (conflict_history_strict_conflict _ _ H) as [? | [? | ?]].
  + pose proof prefix_history_comparable _ _ _ H0 H1.
    apply comparable_conflict_or_equal; auto.
  + apply comparable_conflict_or_equal; auto.
    left; apply prefix_history_trans with h2; auto.
  + left; eapply strict_conflict_backward_conflict_left; eauto.
Qed.

Lemma conflict_backward_right {ora: RandomOracle}: forall h h1 h2,
  conflict_history h h2 ->
  prefix_history h1 h2 ->
  conflict_history h h1 \/ h = h1.
Proof.
  intros.
  destruct (conflict_history_strict_conflict _ _ H) as [? | [? | ?]].
  + apply comparable_conflict_or_equal; auto.
    right; apply prefix_history_trans with h2; auto.
  + pose proof prefix_history_comparable _ _ _ H0 H1.
    rewrite or_comm in H2; apply comparable_conflict_or_equal; auto.
  + left; eapply strict_conflict_backward_conflict_right; eauto.
Qed.
