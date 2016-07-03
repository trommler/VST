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
Import Randomized.

Module Normal.

Class Imperative : Type := {
  acmd: Type;
  expr: Type
}.

Inductive cmd {imp: Imperative}: Type :=
  | Sifthenelse: expr -> cmd -> cmd -> cmd
  | Swhile: expr -> cmd -> cmd
  | Satomic: acmd -> cmd
  | Ssequence: cmd -> cmd -> cmd
  | Sskip: cmd.

Class SmallStepSemantics {imp: Imperative} : Type := {
  state: Type;
  state_sig: SigmaAlgebra state;
  cmd_state_sig := (left_discreste_prod_sigma_alg cmd state);
  ora: RandomOracle;
  SFo: SigmaAlgebraFamily RandomHistory;
  HBSFo: HistoryBasedSigF ora;
  eval_bool: state -> expr -> option bool;
  atomic_step: forall c: acmd, state -> forall {Omega: RandomVarDomain}, ProgState Omega state -> Prop
}.

Existing Instances state_sig cmd_state_sig ora SFo HBSFo.

Inductive step {imp: Imperative} {sss: SmallStepSemantics}: cmd * state -> forall {Omega: RandomVarDomain}, ProgState Omega (cmd * state)%type -> Prop :=
  | step_atomic: forall (ac: acmd) (s: state) (Omega: RandomVarDomain) (cs: ProgState Omega state),
      atomic_step ac s cs -> step (Satomic ac, s) (ProgState_pair_left Sskip cs)
  | step_if_true: forall e c1 c2 s, eval_bool s e = Some true -> step (Sifthenelse e c1 c2, s) (non_branch_tstate (c1, s))
  | step_if_false: forall e c1 c2 s, eval_bool s e = Some false -> step (Sifthenelse e c1 c2, s) (non_branch_tstate (c2, s))
  | step_while_true: forall e c s, eval_bool s e = Some true -> step (Swhile e c, s) (non_branch_tstate (Ssequence c (Swhile e c), s))
  | step_while_false: forall e c s, eval_bool s e = Some false -> step (Swhile e c, s) (non_branch_tstate (Sskip, s))
  | step_skip: forall c s, step (Ssequence Sskip c, s) (non_branch_tstate (c, s)).

End Normal.

Instance normal_imp {Nimp: Normal.Imperative}: Imperative := Build_Imperative Normal.cmd Normal.expr Normal.Sskip Normal.Ssequence.

Instance normal_sss {Nimp: Normal.Imperative} {Nsss: Normal.SmallStepSemantics}: SmallStepSemantics := Build_SmallStepSemantics normal_imp Normal.state Normal.state_sig Normal.ora Normal.SFo Normal.HBSFo Normal.step.

