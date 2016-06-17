Require Import Coq.omega.Omega.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.List_ext.
Require Import RndHoare.axiom. Import RndHoare.axiom.NatChoice.
Require Import RndHoare.random_oracle.

Module Type RANDOM_HISTORY.

Section random_history.

Parameter RandomHistory: forall {ora: RandomOracle}, Type.

Parameter history_get: forall {ora: RandomOracle}, RandomHistory -> nat -> option RandomQA.

Coercion history_get: RandomHistory >-> Funclass.

Parameter fstn_history: forall {ora: RandomOracle}, nat -> RandomHistory -> RandomHistory.

Parameter empty_history: forall {ora: RandomOracle}, RandomHistory.

Parameter single_answer_history: forall {ora: RandomOracle}, RandomQA -> RandomHistory.

Parameter default_inf_history: forall {ora: RandomOracle}, RandomHistory.

Parameter app_history: forall {ora: RandomOracle}, RandomHistory -> RandomHistory -> RandomHistory.

Context {ora: RandomOracle}.

Definition is_n_history (n: nat) (h: RandomHistory): Prop :=
  h n = None /\ forall n', n' < n -> h n' <> None.

Definition is_inf_history (h: RandomHistory): Prop :=
  forall n, h n <> None.

Definition prefix_history (h1 h2: RandomHistory): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Axiom history_sound1: forall (h: RandomHistory) (x y: nat), x <= y -> h x = None -> h y = None.

Axiom history_sound2: forall (h: RandomHistory) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).

Axiom history_extensionality: forall h1 h2: RandomHistory, (forall n, h1 n = h2 n) <-> h1 = h2.

Tactic Notation "history_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply history_extensionality; intro x
  end.

Axiom fstn_history_None: forall n h m, n <= m -> fstn_history n h m = None.

Axiom fstn_history_Some: forall n h m, ~ n <= m -> fstn_history n h m = h m.

Axiom empty_history_spec: forall n, empty_history n = None.

Axiom single_answer_history_spec0: forall qa, single_answer_history qa 0 = Some qa.

Axiom single_answer_history_spec: forall qa n, n <> 0 -> single_answer_history qa n = None.

Axiom default_inf_history_spec: forall n, default_inf_history n = Some (existT _ ro_default_question ro_default_answer).

Axiom app_history_spec_inf: forall h1 h2, is_inf_history h1 -> app_history h1 h2 = h1.

Axiom app_history_spec_fin1: forall h1 h2 n, is_n_history n h1 -> forall m, app_history h1 h2 (n + m) = h2 m.

Axiom app_history_spec_fin2: forall h1 h2 n, is_n_history n h1 -> forall m, m < n -> app_history h1 h2 m = h1 m.

Axiom n_history_inf_history_decT: forall h, {n | is_n_history n h} + (is_inf_history h).

Axiom inf_history_construction: forall (P: RandomHistory -> Prop) (h0: RandomHistory) m0,
  P h0 ->
  is_n_history m0 h0 ->
  (forall h m, P h -> is_n_history m h -> exists qa, P (app_history h (single_answer_history qa))) ->
  exists h, is_inf_history h /\ prefix_history h0 h /\ (forall m, m0 <= m -> P (fstn_history m h)).

End random_history.

End RANDOM_HISTORY.

Module RandomHistory: RANDOM_HISTORY.

Definition RandomHistory {ora: RandomOracle}: Type := ((list RandomQA) + (nat -> RandomQA))%type.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) :=
  match h with
  | inl l => nth_error l n
  | inr f => Some (f n)
  end.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound1: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> h x = None -> h y = None.
Proof.
  intros ? [l | f] ? ? ? ?.
  + simpl in *.
    rewrite nth_error_None_iff in H0 |- *.
    omega.
  + inversion H0.
Qed.

Lemma history_sound2: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
  intros.
  pose proof history_sound1 h x y H.
  destruct (h x), (h y), H0; eauto.
  specialize (H1 eq_refl).
  congruence.
Qed.

Lemma history_extensionality {ora: RandomOracle}: forall h1 h2: RandomHistory, (forall n, h1 n = h2 n) <-> h1 = h2.
Proof.
  intros.
  split; intros.
  + destruct h1, h2; simpl in H.
    - f_equal.
      revert l0 H; induction l; intros.
      * specialize (H 0); simpl in H.
        destruct l0; auto; inversion H.
      * pose proof (H 0).
        destruct l0; [inversion H0 |].
        inversion H0; subst.
        f_equal.
        apply IHl.
        intros; apply (H (S n)); auto.
    - specialize (H (length l)).
      replace (nth_error l (length l)) with (@None RandomQA) in H
        by (symmetry; apply nth_error_None_iff; omega).
      inversion H.
    - specialize (H (length l)).
      replace (nth_error l (length l)) with (@None RandomQA) in H
        by (symmetry; apply nth_error_None_iff; omega).
      inversion H.
    - f_equal.
      extensionality n.
      specialize (H n); inversion H; auto.
  + rewrite H; auto.
Qed.

Tactic Notation "history_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply history_extensionality; intro x
  end.

Definition is_n_history {ora: RandomOracle} (n: nat) (h: RandomHistory): Prop :=
  h n = None /\ forall n', n' < n -> h n' <> None.

Definition is_inf_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  forall n, h n <> None.

Lemma n_history_inf_history_decT {ora: RandomOracle}: forall h, {n | is_n_history n h} + (is_inf_history h).
Proof.
  intros.
  destruct h; [left | right].
  + exists (length l).
    split.
    - apply nth_error_None_iff; omega.
    - intros; intro; simpl in *.
      rewrite nth_error_None_iff in H0.
      omega.
  + hnf; intros.
    simpl; congruence.
Qed.

Definition prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Definition fin_history {ora: RandomOracle} (h: list RandomQA) : RandomHistory := inl h.

Definition inf_history {ora: RandomOracle} (h: nat -> RandomQA) : RandomHistory := inr h.

Definition fstn_history {ora: RandomOracle} (n: nat) (h: RandomHistory) : RandomHistory :=
  match h with
  | inl l => inl (firstn n l)
  | inr f => inl (fisrtn_list_from_fun f n)
  end.

Definition empty_history {ora: RandomOracle} : RandomHistory := fin_history nil.

Definition single_answer_history {ora: RandomOracle} qa : RandomHistory := fin_history (qa :: nil).

Definition default_inf_history {ora: RandomOracle}: RandomHistory :=
  inr (fun _ => existT _ ro_default_question ro_default_answer).

Fixpoint app_fin_inf {A} (l: list A) (f: nat -> A) :=
  match l with
  | nil => f
  | qa :: l0 => fun n => 
                match n with
                | 0 => qa
                | S m => app_fin_inf l0 f m
                end
  end.

Lemma app_fin_inf_list : forall {A} (l: list A) h m, m < length l -> Some (app_fin_inf l h m) = nth_error l m.
Proof.
  intros.
  revert l H; induction m; intros; simpl.
  + destruct l; [simpl in H; omega |].
    simpl; auto.
  + destruct l; [simpl in H; omega |].
    simpl.
    apply IHm.
    simpl in H; omega.
Qed.

Lemma app_fin_inf_fun: forall {A} (l: list A) h m, length l <= m -> app_fin_inf l h m = h (m - length l).
Proof.
  intros.
  revert m H; induction l; intros; simpl.
  + f_equal; omega.
  + destruct m; [simpl in H; omega |].
    rewrite IHl by (simpl in H; omega).
    f_equal.
Qed.

Lemma length_firstn_list_from_fun: forall {A} (f: nat -> A) n, length (fisrtn_list_from_fun f n) = n.
Proof.
  intros.
  induction n; simpl; auto.
  rewrite app_length, IHn.
  simpl.
  omega.
Qed.

Lemma nth_error_firstn_list_from_fun: forall {A} (f: nat -> A) n m, m < n -> nth_error (fisrtn_list_from_fun f n) m = Some (f m).
Proof.
  intros.
  revert m H; induction n; intros; simpl.
  + omega.
  + destruct (le_dec n m).
    - assert (n = m) by omega; subst.
      replace m with (length (fisrtn_list_from_fun f m) + 0) at 3 by (rewrite length_firstn_list_from_fun; omega).
      rewrite nth_error_app.
      simpl; auto.
    - rewrite nth_error_app1 by (rewrite length_firstn_list_from_fun; omega).
      apply IHn; omega.
Qed.

Definition app_history {ora: RandomOracle} (h1 h2: RandomHistory): RandomHistory :=
  match h1 with
  | inl l1 =>
    match h2 with
    | inl l2 => inl (l1 ++ l2)
    | inr f2 => inr (app_fin_inf l1 f2)
    end
  | _ => h1
  end.
  
Section random_history.

Context {ora: RandomOracle}.

Lemma is_n_history_spec: forall n h, is_n_history n h <-> match h with | inl l => n = length l | _ => False end.
Proof.
  intros.
  destruct h; split; intros.
  + destruct H.
    simpl in H; rewrite nth_error_None_iff in H.
    destruct n; [omega |].
    specialize (H0 n).
    unfold not in H0; simpl in H0; rewrite nth_error_None_iff in H0.
    omega.
  + subst.
    split.
    - simpl; rewrite nth_error_None_iff; omega.
    - intros; intro.
      simpl in H0; rewrite nth_error_None_iff in H0; omega.
  + destruct H.
    inversion H.
  + inversion H.
Qed.

Lemma is_inf_history_spec: forall h, is_inf_history h <-> match h with | inl l => False | _ => True end.
Proof.
  intros.
  destruct h; split; intros; try tauto.
  + specialize (H (length l)).
    apply H; simpl.
    rewrite nth_error_None_iff; auto.
  + hnf; intros; intro.
    inversion H0.
Qed.
    
Lemma fstn_history_None: forall n h m, n <= m -> fstn_history n h m = None.
Proof.
  intros.
  destruct h; simpl.
  + apply nth_error_None_iff.
    rewrite firstn_length.
    pose proof Min.le_min_l n (length l); omega.
  + apply nth_error_None_iff.
    rewrite length_firstn_list_from_fun.
    auto.
Qed.

Lemma fstn_history_Some: forall n h m, ~ n <= m -> fstn_history n h m = h m.
Proof.
  intros.
  destruct h; simpl.
  + admit.
  + apply nth_error_firstn_list_from_fun.
    omega.
Qed.

Lemma empty_history_spec: forall n, empty_history n = None.
Proof.
  intros.
  simpl.
  destruct n; auto.
Qed.

Lemma single_answer_history_spec0: forall qa, single_answer_history qa 0 = Some qa.
Proof. intros. auto. Qed.

Lemma single_answer_history_spec: forall qa n, n <> 0 -> single_answer_history qa n = None.
Proof.
  intros.
  destruct n; [omega |].
  simpl.
  destruct n; auto.
Qed.

Lemma default_inf_history_spec: forall n, default_inf_history n = Some (existT _ ro_default_question ro_default_answer).
Proof. intros. reflexivity. Qed.

Lemma app_history_spec_inf: forall h1 h2, is_inf_history h1 -> app_history h1 h2 = h1.
Proof.
  intros.
  rewrite is_inf_history_spec in H.
  destruct h1; try inversion H.
  auto.
Qed.

Lemma app_history_spec_fin1: forall h1 h2 n, is_n_history n h1 -> forall m, app_history h1 h2 (n + m) = h2 m.
Proof.
  intros.
  rewrite is_n_history_spec in H.
  destruct h1; try inversion H.
  destruct h2.
  + simpl.
    subst.
    apply nth_error_app.
  + simpl.
    f_equal.
    rewrite app_fin_inf_fun by omega.
    f_equal; omega.
Qed.

Lemma app_history_spec_fin2: forall h1 h2 n, is_n_history n h1 -> forall m, m < n -> app_history h1 h2 m = h1 m.
Proof.
  intros.
  rewrite is_n_history_spec in H.
  destruct h1; try inversion H.
  destruct h2.
  + simpl.
    subst.
    apply nth_error_app1; omega.
  + simpl.
    rewrite app_fin_inf_list by omega.
    auto.
Qed.

(*
Lemma fin_history_fin: forall l, is_fin_history (fin_history l).
Proof.
  intros.
  exists (length l).
  simpl.
  rewrite nth_error_None_iff; auto.
Qed.
*)
Lemma inf_history_inf: forall f, is_inf_history (inf_history f).
Proof.
  intros; hnf; intros.
  simpl.
  congruence.
Qed.

Lemma fstn_app_inf_fin: forall l h n,
  n >= length l ->
  fstn_history n (inf_history (app_fin_inf l h)) = fin_history (l ++ fisrtn_list_from_fun h (n - length l)).
Proof.
  intros.
  history_extensionality m.
  destruct (le_dec n m).
  + rewrite fstn_history_None by auto.
    simpl.
    symmetry.
    apply nth_error_None_iff.
    rewrite app_length.
    rewrite length_firstn_list_from_fun.
    omega.
  + rewrite fstn_history_Some by omega.
    simpl.
    destruct (le_dec (length l) m).
    - rewrite app_fin_inf_fun by auto.
      replace m with (length l + (m - length l)) at 2 by omega.
      rewrite nth_error_app.
      rewrite nth_error_firstn_list_from_fun by omega.
      auto.
    - rewrite nth_error_app1 by omega.
      rewrite app_fin_inf_list by omega.
      auto.
Qed.

Lemma inf_history_construction: forall (P: RandomHistory -> Prop) (h0: RandomHistory) m0,
  P h0 ->
  is_n_history m0 h0 ->
  (forall h m, P h -> is_n_history m h -> exists qa, P (app_history h (single_answer_history qa))) ->
  exists h, is_inf_history h /\ prefix_history h0 h /\ (forall m, m0 <= m -> P (fstn_history m h)).
Proof.

  admit.
Qed.

End random_history.

End RandomHistory.

Export RandomHistory.

Tactic Notation "history_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply history_extensionality; intro x
  end.
(*
Definition history_app_cons {ora: RandomOracle} (h1: RandomHistory) (a: RandomQA) (h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    h1 n = None /\
    h2 n = Some a /\
    h2 (S n) = None.

Definition history_app {ora: RandomOracle} (h1 h2 h: RandomHistory): Prop :=
  exists n,
    h1 n = None /\
    history_coincide n h1 h /\
    (forall m, h (m + n) = h2 m).
*)
Definition is_fin_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  exists n, h n = None.

(*
Definition is_at_least_n_history {ora: RandomOracle} (n: nat) (h: RandomHistory): Prop :=
  forall n', n' < n -> h n' <> None.
*)
Definition strict_prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  prefix_history h1 h2 /\ exists n, h1 n <> h2 n.

Definition n_bounded_prefix_history {ora: RandomOracle} (m: nat) (h1 h2: RandomHistory): Prop :=
  forall n, (h1 n = None /\ h2 (n + m) = None) \/ h1 n = h2 n.

Lemma is_n_history_None {ora: RandomOracle}: forall n m h, n <= m -> is_n_history n h -> h m = None.
Proof.
  intros.
  destruct H0.
  apply (history_sound1 h n m); auto.
Qed.

Lemma fstn_history_is_n_history {ora: RandomOracle}: forall n m h,
  m <= n ->
  is_n_history n h ->
  is_n_history m (fstn_history m h).
Proof.
  intros.
  destruct H0.
  split.
  + rewrite fstn_history_None by auto; auto.
  + intros.
    rewrite fstn_history_Some by omega.
    apply H1; omega.
Qed.

Lemma prefix_history_refl {ora: RandomOracle}: forall h, prefix_history h h.
Proof.
  intros.
  hnf; intros.
  right; auto.
Qed.

Lemma prefix_history_trans {ora: RandomOracle}: forall h1 h2 h3, prefix_history h1 h2 -> prefix_history h2 h3 -> prefix_history h1 h3.
Proof.
  intros.
  hnf in H, H0 |- *; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0.
  + left; auto.
  + left; auto.
  + left; congruence.
  + right; congruence.
Qed.

Lemma prefix_history_anti_sym {ora: RandomOracle}: forall h1 h2, prefix_history h1 h2 -> prefix_history h2 h1 -> h1 = h2.
Proof.
  intros.
  history_extensionality n.
  hnf; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0; congruence.
Qed.

Lemma prefix_history_comparable {ora: RandomOracle}: forall h1 h2 h, prefix_history h1 h -> prefix_history h2 h -> prefix_history h1 h2 \/ prefix_history h2 h1.
Proof.
  intros.
  destruct (classic (exists n, h1 n <> h2 n /\ h1 n <> None)); [right | left].
  + hnf; intros.
    destruct H1 as [m [? ?]].
    destruct (H0 n); [auto |].
    destruct (H n); [| right; congruence].
    assert (m < n).
    Focus 1. {
      destruct (le_dec n m); try omega.
      exfalso; apply H2.
      eapply history_sound1; eauto.
    } Unfocus.
    destruct (H m); [congruence |].
    destruct (H0 m); [| congruence].
    left.
    apply history_sound1 with m; auto. omega.
  + hnf; intros n.
    destruct (classic (h1 n = None)), (classic (h1 n = h2 n)); try tauto.
    exfalso.
    apply H1.
    eexists; eauto.
Qed.

Lemma fstn_history_finite {ora: RandomOracle}: forall n h, is_fin_history (fstn_history n h).
Proof.
  intros.
  exists n.
  rewrite fstn_history_None; auto.
Qed.

Lemma fstn_history_prefix {ora: RandomOracle}: forall n h, prefix_history (fstn_history n h) h.
Proof.
  intros.
  hnf; intros m.
  destruct (le_dec n m).
  + rewrite fstn_history_None; auto.
  + rewrite fstn_history_Some; auto.
Qed.

Lemma fstn_fstn_history_prefix {ora: RandomOracle}: forall n m h, n <= m -> prefix_history (fstn_history n h) (fstn_history m h).
Proof.
  intros.
  hnf; intros x.
  destruct (le_dec n x); [destruct (le_dec m x) |].
  + rewrite !fstn_history_None; auto.
  + rewrite fstn_history_None by omega; auto.
  + rewrite !fstn_history_Some by omega; auto.
Qed.

Lemma app_history_inf_history_iff {ora: RandomOracle}: forall h1 h2,
  is_inf_history (app_history h1 h2) <-> is_inf_history h1 \/ is_inf_history h2.
Proof.
  intros.
  split; intros.
  + destruct (n_history_inf_history_decT h1) as [[n ?] | ?]; auto.
    right.
    hnf; intros; intro.
    specialize (H (n + n0)).
    rewrite (app_history_spec_fin1 _ _ n) in H by auto.
    auto.
  + destruct H; [rewrite app_history_spec_inf by auto; auto |].
    destruct (n_history_inf_history_decT h1) as [[n ?] | ?]; [| rewrite app_history_spec_inf by auto; auto].
    hnf; intros; intro.
    destruct (lt_dec n0 n).
    - rewrite (app_history_spec_fin2 _ _ n) in H0 by auto.
      destruct i as [_ ?H].
      apply (H1 n0); auto.
    - replace n0 with (n + (n0 - n)) in H0 by omega.
      rewrite (app_history_spec_fin1 _ _ n) in H0 by auto.
      specialize (H (n0 - n)).
      auto.
Qed.

Lemma default_inf_history_inf {ora: RandomOracle}: is_inf_history default_inf_history.
Proof.
  intros.
  hnf; intros.
  rewrite default_inf_history_spec.
  congruence.
Qed.

Lemma prefix_app_history {ora: RandomOracle}: forall h1 h2, prefix_history h1 (app_history h1 h2).
Proof.
  intros.
  destruct (n_history_inf_history_decT h1) as [[n ?] | ?].
  + hnf; intros.
    destruct (le_dec n n0).
    - left.
      destruct i.
      apply (history_sound1 h1 n n0); auto.
    - right.
      rewrite (app_history_spec_fin2 _ _ n); auto; omega.
  + rewrite app_history_spec_inf by auto.
    apply prefix_history_refl.
Qed.

Lemma prefix_empty_history {ora: RandomOracle}: forall h, prefix_history empty_history h.
Proof.
  intros; hnf; intros.
  left; rewrite empty_history_spec; auto.
Qed.

Lemma empty_history_fin {ora: RandomOracle}: is_fin_history empty_history.
Proof.
  exists 0; rewrite empty_history_spec; congruence.
Qed.

Lemma inf_history_prefix {ora: RandomOracle}: forall h1 h2, is_inf_history h1 -> prefix_history h1 h2 -> h1 = h2.
Proof.
  intros.
  history_extensionality n.
  specialize (H0 n); specialize (H n).
  destruct H0; congruence.
Qed.

Lemma prefix_not_equal_fstn_Sn {ora: RandomOracle}: forall h1 h2 m, is_inf_history h2 -> prefix_history h1 (fstn_history (S m) h2) -> h1 <> fstn_history (S m) h2 -> prefix_history h1 (fstn_history m h2).
Proof.
  intros.
  hnf; intros.
  destruct (lt_eq_lt_dec n m) as [[? | ?] | ?].
  + specialize (H0 n).
    rewrite fstn_history_Some in H0 |- * by omega; auto.
  + subst m.
    destruct (H0 n); auto.
    rewrite fstn_history_Some in H2 by omega.
    exfalso; apply H1.
    history_extensionality m.
    destruct (le_dec (S n) m).
    - specialize (H0 m).
      rewrite fstn_history_None in H0 |- * by omega; destruct H0; auto.
    - specialize (H0 m).
      rewrite fstn_history_Some in H0 |- * by omega; destruct H0; auto.
      apply (history_sound1 h1 m n) in H0; [| omega].
      rewrite H0 in H2; symmetry in H2.
      specialize (H n); congruence.
  + specialize (H0 n).
    rewrite fstn_history_None in H0 |- * by omega; auto.
Qed.      

Lemma prefix_not_equal_forward {ora: RandomOracle}: forall h1 h2, prefix_history h1 h2 -> h1 <> h2 -> exists qa, prefix_history (app_history h1 (single_answer_history qa)) h2.
Proof.
  intros.
  assert (exists n, h1 n <> h2 n).
  Focus 1. {
    apply NNPP; intro.
    apply H0.
    history_extensionality n.
    pose proof (not_ex_all_not _ _ H1).
    specialize (H2 n).
    apply NNPP; auto.
  } Unfocus.
  pose proof dec_inh_nat_subset_has_unique_least_element _ (fun n => classic (_ n)) H1.
  clear H1; destruct H2 as [n [[? ?] _]].
  pose proof (H n).
  destruct H3; [| congruence].
  destruct (h2 n) eqn:?H; [| congruence].
  exists r.
  hnf; intros.
  assert (is_n_history n h1).
  Focus 1. {
    split; auto.
    intros; intro.
    specialize (H2 n'); specialize (H n').
    assert (~ n <= n') by omega.
    apply H7, H2; clear H7 H2; intro.
    rewrite H2 in H6.
    assert (n' <= n) by omega.
    pose proof (history_sound1 h2 n' n H7 H6).
    congruence.
  } Unfocus.
  destruct (le_dec n n0) as [?H | ?H].
  + replace n0 with (n + (n0 - n)) at 1 2 by omega.
    rewrite (app_history_spec_fin1 _ _ n); auto.
    destruct (n0 - n) eqn:?H.
    - rewrite single_answer_history_spec0.
      replace n0 with n by omega.
      right; congruence.
    - left.
      rewrite single_answer_history_spec; auto.
  + rewrite (app_history_spec_fin2 _ _ n); auto.
    omega.
Qed.
  

(*
Lemma n_conflict_at_least_n_history1 {ora: RandomOracle}: forall n h1 h2,
  history_coincide n h1 h2 ->
  n_conflict_history n h1 h2 ->
  is_at_least_n_history n h1.
Proof.
  intros.
  intros m ? ?.
  pose proof H2.
  rewrite H in H2 by auto.
  unfold n_conflict_history in H0.
  rewrite (history_sound1 h1 m n) in H0 by (auto; omega).
  rewrite (history_sound1 h2 m n) in H0 by (auto; omega).
  auto.
Qed.

Lemma n_conflict_at_least_n_history2 {ora: RandomOracle}: forall n h1 h2,
  history_coincide n h1 h2 ->
  n_conflict_history n h1 h2 ->
  is_at_least_n_history n h2.
Proof.
  intros.
  intros m ? ?.
  pose proof H2.
  rewrite <- H in H2 by auto.
  unfold n_conflict_history in H0.
  rewrite (history_sound1 h1 m n) in H0 by (auto; omega).
  rewrite (history_sound1 h2 m n) in H0 by (auto; omega).
  auto.
Qed.

Lemma prefix_history_coincide {ora: RandomOracle}: forall n h1 h2,
  prefix_history h1 h2 ->
  is_at_least_n_history n h1 ->
  history_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m H1).
  tauto.
Qed.

Lemma is_at_least_n_history_fstn_history {ora: RandomOracle}: forall n m h, n <= m -> (is_at_least_n_history n (fstn_history m h) <-> is_at_least_n_history n h).
Proof.
  intros.
  split; intros; hnf; intros.
  + specialize (H0 n' H1).
    rewrite fstn_history_Some in H0 by omega.
    auto.
  + specialize (H0 n' H1).
    rewrite fstn_history_Some by omega.
    auto.
Qed.
*)

(*
Lemma prefix_not_equal_history_backward {ora: RandomOracle}: forall h l qa, prefix_history h (fin_history (l ++ qa :: nil)) -> h <> (fin_history (l ++ qa :: nil)) -> prefix_history h (fin_history l).
Proof.
  intros.
  hnf; intros.
  destruct (lt_eq_lt_dec n (length l)) as [[? | ?] | ?].
  + specialize (H n).
    simpl in H |- *.
    rewrite nth_error_app1 in H by auto.
    auto.
  + left.
    destruct (H n); auto.
    pattern n at 2 in H1.
    replace n with (length l + 0) in H1 by omega.
    simpl in H1; rewrite nth_error_app in H1.
    simpl in H1.
    exfalso.
    apply H0.
    history_extensionality m.
    destruct (le_dec (S n) m).
    - destruct (H m); auto.
      simpl.
      rewrite H2; symmetry; apply nth_error_None_iff.
      rewrite app_length; simpl. omega.
    - destruct (H m); auto.
      exfalso.
      assert (m <= n) by omega.
      pose proof history_sound1 h m n H3 H2.
      rewrite H4 in H1; inversion H1.
  + left.
    destruct (H n); auto.
    simpl in H1.
    rewrite H1.
    apply nth_error_None_iff.
    rewrite app_length; simpl; omega.
Qed.

Lemma prefix_not_equal_history_forward {ora: RandomOracle}: forall h l, prefix_history (fin_history l) h -> (fin_history l) <> h -> exists qa, prefix_history (fin_history (l ++ qa :: nil)) h.
Proof.
  intros.
  assert ((fin_history l) (length l) = None) by (apply nth_error_None_iff; omega).
  assert ((fin_history l) (length l) <> h (length l)).
  Focus 1. {
    intro.
    apply H0; history_extensionality n.
    destruct (le_dec (length l) n).
    + destruct (H n); auto.
      rewrite H2 in H1; symmetry in H1.
      rewrite H3; symmetry.
      apply (history_sound1 h (length l) n); auto.
    + destruct (H n); auto.
      exfalso.
      simpl in H3.
      destruct (nth_error_in_bounds l n); [omega |].
      rewrite H3 in H4; inversion H4.
  } Unfocus.
  destruct (h (length l)) eqn:?H; [| congruence]. clear H2.
  exists r.
  hnf; intros.
  destruct (lt_eq_lt_dec n (length l)) as [[? | ?] | ?].
  + specialize (H n).
    simpl in H |- *.
    rewrite nth_error_app1 by auto.
    auto.
  + subst n; simpl.
    right.
    replace (length l) with (length l + 0) at 1 by omega.
    rewrite nth_error_app; simpl.
    symmetry; auto.
  + left.
    apply nth_error_None_iff.
    rewrite app_length; simpl; omega.
Qed.

Lemma prefix_history_fin_app {ora: RandomOracle}: forall l1 l2, prefix_history (fin_history l1) (fin_history (l1 ++ l2)).
Proof.
  intros.
  hnf; intros.
  destruct (le_dec (length l1) n).
  + replace ((fin_history l1) n) with (@None RandomQA) by (symmetry; apply nth_error_None_iff; omega).
    left; auto.
  + right.
    simpl.
    rewrite nth_error_app1; auto.
    omega.
Qed.

Lemma conflict_history_spec {ora: RandomOracle}: forall h1 h2, conflict_history h1 h2 -> exists l, prefix_history (fin_history l) h1 /\ prefix_history (fin_history l) h2 /\ n_conflict_history (length l) h1 h2.
Proof.
  intros.
  apply (dec_inh_nat_subset_has_unique_least_element
    (fun n => history_coincide n h1 h2 /\ n_conflict_history n h1 h2)
    (fun n => classic (_ n))) in H.
  destruct H as [n [[[? ?] _] _]].
  assert (exists l,
            length l = n /\
            prefix_history (fin_history l) h1 /\
            prefix_history (fin_history l) h2) as HH;
  [| destruct HH as [l [? [? ?]]]; exists l; subst; auto].
  assert (forall m, m < n -> h1 m <> None).
  Focus 1. {
    intros; intro.
    specialize (H m H1).    
    rewrite H2 in H; symmetry in H.
    hnf in H0.
    rewrite (history_sound1 h1 m n) in H0 by (auto; omega).
    rewrite (history_sound1 h2 m n) in H0 by (auto; omega).
    auto.
  } Unfocus.
  clear H0.
  induction n.
  + exists nil; split; auto.
    split; hnf; intros; left; destruct n; auto.
  + destruct IHn as [l [? [? ?]]].
    1: eapply history_coincide_weaken; try eassumption. apply le_n_Sn.
    1: intros; apply H1; omega.
    pose proof (H1 n).
    specialize (H4 (lt_n_Sn _)).
    destruct (h1 n) eqn:?H; [| congruence]; clear H4.
    exists (l ++ r :: nil).
    split; [| split].
    - rewrite app_length; simpl; omega.
    - hnf; intros m.
      destruct (lt_eq_lt_dec m n) as [[?H | ?H] | ?H].
      * right; simpl.
        rewrite nth_error_app1 by omega.
        destruct (H2 m); auto; exfalso.
        simpl in H6; rewrite -> @nth_error_None_iff in H6; omega.
      * right; subst m n; rewrite H5.
        replace (length l) with (length l + 0) by omega; simpl.
        rewrite nth_error_app; auto.
      * left; simpl.
        apply nth_error_None_iff; rewrite app_length; simpl; omega.
    - rewrite H in H5 by omega.
      hnf; intros m.
      destruct (lt_eq_lt_dec m n) as [[?H | ?H] | ?H].
      * right; simpl.
        rewrite nth_error_app1 by omega.
        destruct (H3 m); auto; exfalso.
        simpl in H6; rewrite -> @nth_error_None_iff in H6; omega.
      * right; subst m n; rewrite H5.
        replace (length l) with (length l + 0) by omega; simpl.
        rewrite nth_error_app; auto.
      * left; simpl.
        apply nth_error_None_iff; rewrite app_length; simpl; omega.
Qed.

Lemma fstn_history_exists_fin_history {ora: RandomOracle}: forall h n, exists l, fstn_history n h = fin_history l.
Proof.
  intros.
  assert (exists l, fstn_history n h = fin_history l /\ length l <= n); [| firstorder].
  induction n.
  + exists nil; split; auto.
    history_extensionality n.
    simpl; destruct n; auto.
  + destruct IHn as [l [? ?]].
    destruct (h n) eqn:?.
    - assert (n = length l).
      Focus 1. {
        destruct (classic (length l < n)); [| omega].
        clear H0; exfalso.
        assert (fstn_history n h (length l) = fin_history l (length l)) by (f_equal; auto).
        simpl in H0.
        destruct (le_lt_dec n (length l)); try omega.
        replace (nth_error l (length l)) with (@None RandomQA) in H0 by (symmetry; apply nth_error_None_iff; omega).
        apply (history_sound1 h (length l) n) in H0; [| omega].
        congruence.
      } Unfocus.
      subst n.
      exists (l ++ r :: nil).
      split; [| rewrite app_length; simpl; omega].
      history_extensionality m.
      Opaque le_lt_dec. simpl. Transparent le_lt_dec.
      destruct (le_lt_dec (S (length l)) m) as [?H | ?H]; [| destruct (lt_dec m (length l)) as [?H | ?H]].
      * symmetry; apply nth_error_None_iff; rewrite app_length; simpl; omega.
      * rewrite nth_error_app1 by omega.
        assert (fstn_history (length l) h m = fin_history l m) by (f_equal; auto).
        simpl in H3; rewrite <- H3. 
        destruct (le_lt_dec (length l) m); auto; omega.
      * assert (m = length l) by omega; subst m.
        replace (length l) with (length l + 0) at 2 by omega.
        rewrite nth_error_app.
        auto.
    - exists l.
      split; [| omega].
      rewrite <- H.
      clear - Heqo; history_extensionality m.
      Opaque le_lt_dec. simpl. Transparent le_lt_dec.
      destruct (le_lt_dec (S n) m), (le_lt_dec n m); auto; try omega.
      apply (history_sound1 h n m); auto.
Qed.

Lemma prefix_inf_history_is_fstn_history {ora: RandomOracle}: forall l h,
  is_inf_history h ->
  prefix_history (fin_history l) h ->
  fin_history l = fstn_history (length l) h.
Proof.
  intros.
  rev_induction l.
  + history_extensionality n.
    simpl; destruct n; auto.
  + history_extensionality n.
    specialize (H0 (prefix_history_trans _ _ _ (prefix_history_fin_app _ _) H1)).
    assert (fin_history l n = fstn_history (length l) h n) by (f_equal; auto).
    specialize (H1 n).
    simpl in H1, H2 |- *.
    destruct (le_lt_dec (length l) n); [destruct (le_lt_dec (length (l +:: a)) n) |].
    - apply nth_error_None_iff; auto.
    - assert (nth_error (l +:: a) n = Some a).
      Focus 1. {
        replace n with (length l + 0) at 1 by (rewrite app_length in l1; simpl in l1; omega).
        rewrite nth_error_app; auto.
      } Unfocus.
      rewrite H3 in *.
      destruct H1; auto; congruence.
    - destruct (le_lt_dec (length (l +:: a)) n); [rewrite app_length in *; simpl in *; omega |].
      rewrite nth_error_app1 by omega; auto.
Qed.
*)
    
