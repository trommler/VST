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
Require Import RndHoare.pstate_stream_limit.
Require Import RndHoare.probabilistic_pred.
Require Import RndHoare.imperative.
Require Import RndHoare.normal_imperative.
Import Randomized.

Module HyperHoare.

Section HyperHoareSound.

Context {Nimp: Normal.Imperative} {Nsss: Normal.SmallStepSemantics}.

Import PlainAssertion.
Local Open Scope logic.

Lemma ConsequenceRule: forall Gamma {sG: SigmaAlgebras Gamma} P P' Q Q' c, valid Gamma (imp P' P) -> valid Gamma (imp Q Q') -> triple Gamma P c Q -> triple Gamma P' c Q'.
Proof.
  intros.
  unfold triple in *.
  intros.
  rename H3 into H_acc.
  specialize (H _ (raw_state _ _ s1, gamma)); simpl in H.
  specialize (H0 _ (post_prod (oaccess_forward _ _ _ H_acc) (oaccess_same_covered _ _ _ H_acc)
                     (raw_state _ _ s2) (raw_state _ _ s1, gamma))); simpl in H0.
  rewrite imp_spec in H.
  rewrite imp_spec in H0.
  specialize (H1 o1 s1 gamma (H H2) o2 s2 H_acc).
  auto.
Qed.

Lemma RVExistentialRule: forall Gamma {sG: SigmaAlgebras Gamma} U {sU: SigmaAlgebra U} P Q c, triple (U :: Gamma) P c Q -> triple Gamma (expR U P) c (expR U Q).
Proof.
  intros.
  unfold triple in *.
  intros.
  rewrite (expR_spec _ _ _ P) in H0.
  destruct H0 as [u ?].
  specialize (H _ _ _ H0 o2 s2 H1).
  unfold post_prod.
  rewrite (expR_spec _ _ _ Q).
  exists (post_dom_var _ _ (oaccess_forward c s1 s2 H1)
        (oaccess_same_covered c s1 s2 H1) u); auto.
Qed.

Lemma ExistentialRule: forall Gamma {sG: SigmaAlgebras Gamma} U P Q c, (forall u, triple Gamma (P u) c (Q u)) -> triple Gamma (exp U P) c (exp U Q).
Proof.
  intros.
  unfold triple in *.
  intros.
  rewrite (exp_spec _ _ P) in H0.
  destruct H0 as [u ?].
  specialize (H _ _ _ _ H0 o2 s2 H1).
  rewrite (exp_spec _ _ Q).
  exists u.
  auto.
Qed.

(*
Lemma Sequence: forall P Q R c1 c2, triple P c1 Q -> triple Q c2 R -> triple P (Ssequence c1 c2) R.
Proof.
  intros ? ? ? ? ? TRIPLE1 TRIPLE2.
  unfold triple in *; intros.
  destruct H0 as [path [? ?]].
Abort.
*)
End HyperHoareSound.

End HyperHoare.

Module PartialrHoare.

Section PartialHoareSound.

Context {Nimp: Normal.Imperative} {Nsss: Normal.SmallStepSemantics}.

Import PlainAssertion.

Lemma ConsequenceRule: forall Gamma {sG: SigmaAlgebras Gamma} P P' Q Q' c, valid Gamma (imp P' P) -> valid Gamma (imp Q Q') -> partial_triple Gamma P c Q -> partial_triple Gamma P' c Q'.
Proof.
  intros.
  eapply HyperHoare.ConsequenceRule.
  + apply PartialMetaAssertion_imp; eauto.
  + apply PartialMetaAssertion_imp; eauto.
  + auto.
Qed.

End PartialHoareSound.

End PartialrHoare.