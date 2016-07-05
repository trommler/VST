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

Definition Terminating_pred {state: Type} (P: Ensemble state): Ensemble (MetaState state) :=
  fun s => match s with | Terminating s => P s | _ => False end.

Definition partial_Terminating_pred {state: Type} (P: Ensemble state): Ensemble (MetaState state) :=
  fun s => match s with | Terminating s => P s | _ => True end.

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

Lemma Terminating_pred_measurable: forall {A} {sA: SigmaAlgebra A} (P: Ensemble A), is_measurable_set P -> is_measurable_set (Terminating_pred P).
Proof.
  intros.
  simpl.
  apply H.
Qed.

Definition NonTerminating_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ NonTerminating_measurable.

Definition Error_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ Error_measurable.

Definition is_Terminating_MSet {A} {sA: SigmaAlgebra A}: measurable_set (MetaState A) := exist _ _ is_Terminating_measurable.

Definition TerminatingP_MSet {A} {sA: SigmaAlgebra A} (P: measurable_set A): measurable_set (MetaState A) := exist _ _ (Terminating_pred_measurable P (proj2_sig P)).

(*
(* This is nicer and generic. But it needs cmd to be countable. *)
(* It is true, but I just do not want to spend time one this. *)
Inductive raw_MetaState_pair_left_func (cmd state: Type) {sigma_state: SigmaAlgebra state} (f: @MeasurableFunction state cmd _ (max_sigma_alg _)): MetaState state -> MetaState (cmd * state) -> Prop :=
  | Error_pair_left: raw_MetaState_pair_left_func cmd state f (Error _) (Error _)
  | NonTerminating_pair_left: raw_MetaState_pair_left_func cmd state f (NonTerminating _) (NonTerminating _)
  | Terminating_pair_left: forall s c, f s c -> raw_MetaState_pair_left_func cmd state f (Terminating _ s) (Terminating _ (c, s)).
*)

Inductive raw_lift_mf {A B} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B): MetaState A -> MetaState B -> Prop :=
  | Error_lift_mf: raw_lift_mf f (Error _) (Error _)
  | NonTerminating_lift_mf: raw_lift_mf f (NonTerminating _) (NonTerminating _)
  | Terminating_lift_mf: forall a b, f a b -> raw_lift_mf f (Terminating _ a) (Terminating _ b)
  .

Definition lift_mf {A B} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B): MeasurableFunction (MetaState A) (MetaState B).
  apply (Build_MeasurableFunction _ _ _ _ (raw_lift_mf f)).
  + intros.
    inversion H; inversion H0; try congruence.
    subst.
    inversion H5; subst.
    pose proof rf_functionality _ _ f _ _ _ H1 H4.
    subst; auto.
  + intros.
    destruct a.
    - exists (Error _); constructor.
    - exists (NonTerminating _); constructor.
    - destruct (rf_complete _ _ f a) as [b ?]; exists (Terminating _ b); constructor; auto.
  + simpl.
    intros P.
    destruct P as [P ?H].
    simpl in *.
    pose proof rf_preserve _ _ f (exist _ _ H).
    eapply is_measurable_set_proper; [| exact H0].
    simpl.
    split; hnf; unfold In; intros.
    - apply H1; constructor; auto.
    - inversion H2; auto.
Defined.

Lemma lift_mf_compose {A B C} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} {sC: SigmaAlgebra C} (f: MeasurableFunction A B) (g: MeasurableFunction B C): Compose (lift_mf g) (lift_mf f) = lift_mf (Compose g f).
Proof.
  intros.
  MeasurableFunction_extensionality a c.
  simpl.
  split; intros.
  + destruct H as [b [? ?]].
    destruct a, b, c; inversion H; inversion H0; constructor; subst.
    exists b; auto.
  + destruct a, c; inversion H; subst.
    - exists (Error _); split; auto; constructor.
    - exists (NonTerminating _); split; auto; constructor.
    - destruct H2 as [b [? ?]].
      exists (Terminating _ b); split; auto; constructor; auto.
Qed.
    
(*
Inductive raw_MetaState_pair_left_choice (cmd state: Type) {sigma_state: SigmaAlgebra state} (filter: measurable_set state) (c1 c2: cmd): MetaState state -> MetaState (cmd * state) -> Prop :=
  | Error_pair_left_choice: raw_MetaState_pair_left_choice cmd state filter c1 c2 (Error _) (Error _)
  | NonTerminating_pair_left_choice: raw_MetaState_pair_left_choice cmd state filter c1 c2 (NonTerminating _) (NonTerminating _)
  | Terminating_pair_left_true: forall s, filter s -> raw_MetaState_pair_left_choice cmd state filter c1 c2 (Terminating _ s) (Terminating _ (c1, s))
  | Terminating_pair_left_false: forall s, ~ filter s -> raw_MetaState_pair_left_choice cmd state filter c1 c2 (Terminating _ s) (Terminating _ (c2, s)).

Definition MetaState_pair_left_choice {cmd state: Type} {state_sig: SigmaAlgebra state} (filter: measurable_set state) (c1 c2: cmd): @MeasurableFunction (MetaState state) (MetaState (cmd * state)) _ (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)).
  apply (Build_MeasurableFunction _ _ _ _ (raw_MetaState_pair_left_choice cmd state filter c1 c2)).
  + intros.
    inversion H; inversion H0; try congruence.
  + intros.
    destruct a.
    - exists (Error _); constructor.
    - exists (NonTerminating _); constructor.
    - destruct (classic (filter s)).
      * exists (Terminating _ (c1, s)); constructor; auto.
      * exists (Terminating _ (c2, s)); constructor; auto.
  + simpl.
    intros.
    destruct P as [P ?H].
    simpl in *.
    eapply is_measurable_set_proper.
    Focus 2. {
      apply union_measurable; apply intersection_measurable.
      + apply (proj2_sig filter).
      + exact (H c1).
      + apply complement_measurable, (proj2_sig filter).
      + exact (H c2).
    } Unfocus.
    rewrite Same_set_spec; intros s.
    rewrite Union_spec, !Intersection_spec; unfold Complement, Ensembles.In.
    split; intros.
    - destruct (classic (filter s)); [left | right]; split; auto.
      * apply H0.
        constructor; auto.
      * apply H0.
        constructor; auto.
    - inversion H1; subst; tauto.
Defined.
*)

Definition MetaState_fun_left {cmd state: Type} {state_sig: SigmaAlgebra state} (f: cmd -> cmd): @MeasurableFunction (MetaState (cmd * state)) (MetaState (cmd * state)) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) :=
  lift_mf (LeftF_MFun f).

Definition MetaState_pair_left {cmd state: Type} {state_sig: SigmaAlgebra state} (c: cmd): @MeasurableFunction (MetaState state) (MetaState (cmd * state)) _ (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) :=
  lift_mf (LeftPair_MFun c).

Definition MetaState_snd {cmd state: Type} {state_sig: SigmaAlgebra state}: @MeasurableFunction (MetaState (cmd * state)) (MetaState state) (@MetaState_SigmaAlgebra _ (left_discreste_prod_sigma_alg cmd state)) _ :=
  lift_mf Snd_MFun.

(*
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
*)
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

Lemma ProgState_extensionality: forall (Omega: RandomVarDomain) (state: Type) {state_sigma: SigmaAlgebra state} (s1 s2: ProgState Omega state), (forall h a, s1 h a <-> s2 h a) -> s1 = s2.
Proof.
  intros.
  destruct s1 as [s1 ?H], s2 as [s2 ?H].
  assert (s1 = s2) by (RandomVariable_extensionality h a; auto); subst.
  assert (H0 = H1) by (apply proof_irrelevance); subst.
  auto.
Qed.

Tactic Notation "ProgState_extensionality" ident(x) ident(y) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply ProgState_extensionality; intros x y
  end.

Definition ProgState_lift_mf {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) {Omega: RandomVarDomain} (s: ProgState Omega A): ProgState Omega B.
  refine (Build_ProgState Omega _ _ (RandomVarMap (lift_mf f) (raw_state _ _ s)) _).
  intros.
  rewrite RandomVarMap_sound in H0.
  destruct H0 as [? [? ?]].
  pose proof inf_history_sound _ _ s h x H H0.
  inversion H1; subst; congruence.
Defined.

(*
Lemma ProgState_lift_mf_proper: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) {O1 O2: RandomVarDomain} (sa1: ProgState O1 A) (sa2: ProgState O2 A),
  RandomVar_global_equiv sa1 sa2 -> RandomVar_global_equiv (ProgState_lift_mf f sa1) (ProgState_lift_mf f sa2).
Proof.
  intros.
*)
Lemma ProgState_lift_mf_Terminating_spec: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) {Omega: RandomVarDomain} (s: ProgState Omega A) h b,
  ProgState_lift_mf f s h (Terminating _ b) <-> exists a, f a b /\ s h (Terminating _ a).
Proof.
  intros.
Opaque RandomVarMap. simpl. Transparent RandomVarMap. (* Should Opaque Always. *)
  rewrite RandomVarMap_sound.
  split; intros.
  + destruct H as [? [? ?]]; simpl in *.
    inversion H0; subst.
    eauto.
  + destruct H as [a ?]; simpl in *.
    exists (Terminating _ a).
    destruct H; subst; split; auto.
    simpl; constructor; auto.
Qed.

Lemma ProgState_lift_mf_rev_exists: forall {A B: Type} {sA: SigmaAlgebra A} {sB: SigmaAlgebra B} (f: MeasurableFunction A B) {Omega: RandomVarDomain} (sb: ProgState Omega B),
  (forall h mb, sb h mb -> exists ma, lift_mf f ma mb) ->
  exists sa, sb = ProgState_lift_mf f sa.
Proof.
  intros.
  admit. (* use choice axiom. *)
Qed.

(*
(* TODO: Define the following two using ProgState_lift_mf *)
Definition ProgState_pair_left_choice {cmd state: Type} {state_sigma: SigmaAlgebra state} (filter: measurable_set state) (c1 c2: cmd) {Omega: RandomVarDomain} (s: ProgState Omega state): @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state).
  refine (Build_ProgState Omega _ _ (RandomVarMap (MetaState_pair_left_choice filter c1 c2) (raw_state _ _ s)) _).
  intros.
  rewrite RandomVarMap_sound in H0.
  destruct H0 as [? [? ?]].
  pose proof inf_history_sound _ _ s h x H H0.
  inversion H1; subst; congruence.
Defined.
*)
Definition ProgState_fun_left {cmd state: Type} {state_sigma: SigmaAlgebra state} (f: cmd -> cmd) {Omega: RandomVarDomain} (s: @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state)): @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state)
  := ProgState_lift_mf (LeftF_MFun f) s.

Definition ProgState_pair_left {cmd state: Type} {state_sigma: SigmaAlgebra state} (c: cmd) {Omega: RandomVarDomain} (s: ProgState Omega state): @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state)
  := ProgState_lift_mf (LeftPair_MFun c) s.

Definition ProgState_snd {cmd state: Type} {state_sigma: SigmaAlgebra state} {Omega: RandomVarDomain} (s: @ProgState Omega (cmd * state) (left_discreste_prod_sigma_alg cmd state)): ProgState Omega state
  := ProgState_lift_mf Snd_MFun s.

Lemma ProgState_pair_left_Terminating_spec {cmd state: Type} {state_sigma: SigmaAlgebra state}: forall (c: cmd) {Omega: RandomVarDomain} (s: ProgState Omega state) h cc ss,
  ProgState_pair_left c s h (Terminating _ (cc, ss)) <-> cc = c /\ s h (Terminating _ ss).
Proof.
  intros.
  unfold ProgState_pair_left.
  rewrite ProgState_lift_mf_Terminating_spec.
  split; intros.
  + destruct H as [? [? ?]]; simpl in *.
    inversion H; subst; auto.
  + exists ss.
    destruct H; subst; split; auto.
    simpl; constructor.
Qed.

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

Definition is_Terminating_part {Omega Omega': RandomVarDomain} {A: Type} {sA: SigmaAlgebra A} (v: RandomVariable Omega (MetaState A)) (v': RandomVariable Omega' A) :=
  forall h, Omega' h -> (forall a, v h (Terminating _ a) <-> v' h a).
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
  
Tactic Notation "ProgState_extensionality" ident(x) ident(y) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply ProgState_extensionality; intros x y
  end.



