Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_history_order.
Require Import RndHoare.random_history_conflict.
Require Import RndHoare.history_anti_chain.
Require Import RndHoare.random_variable.
Require Import RndHoare.meta_state.

Section PredicatesType.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Fixpoint _SigmaAlgebras (As: list Type): Type :=
  match As with 
  | nil => unit
  | cons A As0 => (_SigmaAlgebras As0 * SigmaAlgebra A)%type
  end.

Class SigmaAlgebras (As: list Type): Type := sigma_algebras: _SigmaAlgebras As.

Instance nil_SigmaAlgebras: SigmaAlgebras nil := tt.

Instance cons_SigmaAlgebras (A: Type) (As0: list Type) {sA: SigmaAlgebra A} {sAs: SigmaAlgebras As0}: SigmaAlgebras (cons A As0) := (@sigma_algebras _ sAs, sA).

Global Existing Instances nil_SigmaAlgebras cons_SigmaAlgebras.

Definition head_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebra A := snd sigma_algebras.

Definition tail_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebras As0 := fst sigma_algebras.

Fixpoint _RVProdType (Omega: RandomVarDomain) (As: list Type): forall {sAs: SigmaAlgebras As}, Type :=
  match As as As_PAT return SigmaAlgebras As_PAT -> Type with
  | nil => fun _ => unit
  | cons A As0 => fun sAs => (@_RVProdType Omega As0 (@tail_SigmaAlgebra _ _ sAs) *
                              @RandomVariable _ _ _ Omega A (@head_SigmaAlgebra _ _ sAs))%type
  end.

Definition RVProdType (Omega: RandomVarDomain) (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As}: Type := (RandomVariable Omega A0 * _RVProdType Omega As)%type.

(*
Fixpoint _RVProdMetaType {Omega: RandomVarDomain} {A0: Type} {sA0: SigmaAlgebra A0} (a0: ProgState Omega A0) (As: list Type): forall {sAs: SigmaAlgebras As}, Type :=
  match As as As_PAT return SigmaAlgebras As_PAT -> Type with
  | nil => fun _ => unit
  | cons A As0 => fun sAs => (@_RVProdMetaType Omega _ _ a0 As0 (@tail_SigmaAlgebra _ _ sAs) *
                              {a: @ProgState _ _ _ Omega A (@head_SigmaAlgebra _ _ sAs) | Terminating_equiv a0 a})%type
  end.

Definition RVProdMetaType (Omega: RandomVarDomain) (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As}: Type := sigT (fun a0: ProgState Omega A0 => _RVProdMetaType a0 As).

Definition _post_prod {Omega Omega': RandomVarDomain} {A0: Type} {sA0: SigmaAlgebra A0} (a0: ProgState Omega A0) (a0': ProgState Omega' A0) (Hf: future_anti_chain Omega Omega') (Hs: same_covered_anti_chain Omega Omega') (Hts: TerminatingShrink a0 a0') : forall {As: list Type} {sAs: SigmaAlgebras As} (rho: _RVProdMetaType a0 As), _RVProdMetaType a0' As :=
  fix PPV As: forall (sAs: SigmaAlgebras As) (rho: _RVProdMetaType a0 As), _RVProdMetaType a0' As :=
    match As as As_PAT
      return forall (sAs: SigmaAlgebras As_PAT) (rho: _RVProdMetaType a0 As_PAT), _RVProdMetaType a0' As_PAT
    with
    | nil => fun _ _ => tt
    | A :: As0 => fun sAs rho => (PPV As0 (tail_SigmaAlgebra A As0) (fst rho),
                                  exist _
                                    (post_dom_prog_state _ _ Hf Hs a0'  (proj1_sig (snd rho)))
                                    (post_dom_prog_state_Terminating_equiv _ _ Hf Hs a0 a0' Hts (proj1_sig (snd rho)) (proj2_sig (snd rho))))
    end.

Definition post_prod {Omega Omega': RandomVarDomain} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (rho: RVProdMetaType Omega A0 As) (a0': ProgState Omega' A0) (Hf: future_anti_chain Omega Omega') (Hs: same_covered_anti_chain Omega Omega') (Hts: TerminatingShrink (projT1 rho) a0') : RVProdMetaType Omega' A0 As := existT _ a0' (_post_prod (projT1 rho) a0' Hf Hs Hts (projT2 rho)).
*)

Definition _post_prod {Omega Omega': RandomVarDomain} (Hf: future_anti_chain Omega Omega') (Hs: same_covered_anti_chain Omega Omega') : forall {As: list Type} {sAs: SigmaAlgebras As} (rho: _RVProdType Omega As), _RVProdType Omega' As :=
  fix PPV As: forall (sAs: SigmaAlgebras As) (rho: _RVProdType Omega As), _RVProdType Omega' As :=
    match As as As_PAT
      return forall (sAs: SigmaAlgebras As_PAT) (rho: _RVProdType Omega As_PAT), _RVProdType Omega' As_PAT
    with
    | nil => fun _ _ => tt
    | A :: As0 => fun sAs rho => (PPV As0 (tail_SigmaAlgebra A As0) (fst rho), post_dom_var _ _ Hf Hs (snd rho))
    end.

Definition post_prod {Omega Omega': RandomVarDomain} (Hf: future_anti_chain Omega Omega') (Hs: same_covered_anti_chain Omega Omega') {A0: Type} {sA0: SigmaAlgebra A0} (a': RandomVariable Omega' A0) {As: list Type} {sAs: SigmaAlgebras As} (rho: RVProdType Omega A0 As): RVProdType Omega' A0 As :=
  (a', _post_prod Hf Hs (snd rho)).

Definition _is_filter_prod {Omega Omega': RandomVarDomain}: forall {As: list Type} {sAs: SigmaAlgebras As} (rho: _RVProdType Omega As) (rho': _RVProdType Omega' As), Prop :=
  fix IFP (As: list Type): forall (sAs: SigmaAlgebras As) (rho: _RVProdType Omega As) (rho': _RVProdType Omega' As), Prop :=
    match As as As_PAT
      return forall (sAs: SigmaAlgebras As_PAT) (rho: _RVProdType Omega As_PAT) (rho': _RVProdType Omega' As_PAT), Prop
    with
    | nil => fun _ _ _ => True
    | A :: As0 => fun sAs rho rho' => IFP As0 (tail_SigmaAlgebra A As0) (fst rho) (fst rho') /\ is_filter_var (snd rho) (snd rho')
    end.

Definition is_conditional_prod {Omega Omega': RandomVarDomain} (A: Ensemble RandomHistory) {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (rho: RVProdType Omega A0 As) (rho': RVProdType Omega' A0 As): Prop := Same_set Omega' (Intersection _ Omega A) /\ is_filter_var (fst rho) (fst rho') /\ _is_filter_prod (snd rho) (snd rho').

Definition is_Terminating_prod {Omega Omega': RandomVarDomain} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (rho: RVProdType Omega (MetaState A0) As) (rho': RVProdType Omega' A0 As): Prop := Same_set Omega' (Intersection _ Omega (fun h => forall a, fst rho h a -> is_Terminating a)) /\ is_Terminating_part (fst rho) (fst rho') /\ _is_filter_prod (snd rho) (snd rho').

End PredicatesType.

Module Type ASSERTION.

Parameter random_value: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As} (t: Type) {sT: SigmaAlgebra t}, Type.

Parameter local_eval: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {t: Type} {sT: SigmaAlgebra t} {Omega: RandomVarDomain} (rho: RVProdType Omega A0 As) (h: RandomHistory) (X: random_value A0 As t), t.

Parameter event: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As}, Type.

Parameter rv_event: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {t: Type} {sT: SigmaAlgebra t} (T': measurable_set t) (X: random_value A0 As t), event A0 As.

Parameter local_satisfy: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {Omega: RandomVarDomain} (rho: RVProdType Omega A0 As) (h: RandomHistory) (A: event A0 As), Prop.

Parameter value: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As} (t: Type), Type.

Parameter eval: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {t: Type} {Omega: RandomVarDomain} (rho: RVProdType Omega A0 As) (e: value A0 As t), t.

Parameter assertion: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As}, Type.

Parameter satisfy: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {Omega: RandomVarDomain} (rho: RVProdType Omega A0 As) (P: assertion A0 As), Prop.

Parameter andp: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (P Q: assertion A0 As), assertion A0 As.

Parameter orp: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (P Q: assertion A0 As), assertion A0 As.

Parameter imp: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (P Q: assertion A0 As), assertion A0 As.

Parameter allp: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (B: Type) (P: B -> assertion A0 As), assertion A0 As.

Parameter exp: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (B: Type) (P: B -> assertion A0 As), assertion A0 As.

Parameter expR: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (B: Type) {sB: SigmaAlgebra B} (P: assertion A0 (B :: As)), assertion A0 As.

Parameter conditional: forall {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} (P: assertion A0 As) (A: event A0 As), assertion A0 As.

Definition rv_conditional {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As} {t: Type} {sT: SigmaAlgebra t} (P: assertion A0 As) (X: random_value A0 As t): assertion A0 As := allp _ (fun T': measurable_set t => conditional P (rv_event T' X)).

Definition valid {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As} (P: assertion A0 As): Prop := forall Omega (rho: RVProdType Omega A0 As), satisfy rho P.

Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Infix "-->" := imp (at level 55, right associativity) : logic.
Notation "rho |== P" := (satisfy rho P) (at level 60, no associativity) : logic.
Local Open Scope logic.

Section ASSERTION.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora} {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As}.

Axiom rv_event_spec: forall {t: Type} {sT: SigmaAlgebra t} {Omega} (rho: RVProdType Omega A0 As) (h: RandomHistory) (T': measurable_set t) (X: random_value A0 As t), local_satisfy rho h (rv_event T' X) <-> T' (local_eval rho h X).

Axiom andp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P && Q <-> rho |== P /\ rho |== Q.

Axiom orp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P || Q <-> rho |== P \/ rho |== Q.

Axiom imp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P --> Q <-> rho |== P -> rho |== Q.

Axiom exp_spec: forall {Omega} (U: Type) (rho: RVProdType Omega A0 As) (P: U -> assertion A0 As), rho |== exp U P <-> exists u, rho |== P u.

Axiom expR_spec: forall {Omega} (U: Type) {sU: SigmaAlgebra U} (a: RandomVariable Omega A0) (gamma: _RVProdType Omega As) (P: assertion A0 (U :: As)), (a, gamma) |== expR U P <-> exists u, ((a, (gamma, u)): RVProdType _ A0 (U :: As)) |== P.

Axiom conditional_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P: assertion A0 As) (A: event A0 As), rho |== conditional P A <-> (forall Omega' (rho': RVProdType Omega' A0 As), is_conditional_prod (fun h => local_satisfy rho h A) rho rho' -> rho' |== P).

End ASSERTION.

End ASSERTION.

Module PlainAssertion: ASSERTION.

Section PlainAssertion.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Definition assertion (A0: Type) {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As}: Type := forall (Omega: RandomVarDomain), RVProdType Omega A0 As -> Prop.

Section Definitions.

Context {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As}.

Definition andp (P Q: @assertion A0 sA0 As sAs): assertion A0 As := fun Omega rho => P Omega rho /\ Q Omega rho.

Definition orp (P Q: @assertion A0 sA0 As sAs): assertion A0 As := fun Omega rho => P Omega rho \/ Q Omega rho.

Definition imp (P Q: @assertion A0 sA0 As sAs): assertion A0 As := fun Omega rho => P Omega rho -> Q Omega rho.

Definition exp (B: Type) (P: B -> @assertion A0 sA0 As sAs): assertion A0 As := fun Omega rho => exists b: B, P b Omega rho.

Definition expR (B: Type) {sB: SigmaAlgebra B} (P: @assertion A0 sA0 (B :: As) (sAs, sB)): assertion A0 As := fun Omega rho => exists b: RandomVariable Omega B, P Omega (fst rho, (snd rho, b)).

Definition satisfy {Omega: RandomVarDomain} (rho: RVProdType Omega A0 As) (P: assertion A0 As): Prop := P Omega rho.

Definition valid {A0: Type} {sA0: SigmaAlgebra A0} (As: list Type) {sAs: SigmaAlgebras As} (P: assertion A0 As): Prop := forall Omega (rho: RVProdType Omega A0 As), P Omega rho.

End Definitions.

Section Lemmas.

Context {A0: Type} {sA0: SigmaAlgebra A0} {As: list Type} {sAs: SigmaAlgebras As}.

Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Infix "-->" := imp (at level 55, right associativity) : logic.
Notation "rho |== P" := (satisfy rho P) (at level 60, no associativity) : logic.
Local Open Scope logic.

Lemma andp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P && Q <-> rho |== P /\ rho |== Q.
Proof.
  intros.
  unfold satisfy, andp.
  tauto.
Qed.

Lemma orp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P || Q <-> rho |== P \/ rho |== Q.
Proof.
  intros.
  unfold satisfy, orp.
  tauto.
Qed.

Lemma imp_spec: forall {Omega} (rho: RVProdType Omega A0 As) (P Q: assertion A0 As), rho |== P --> Q <-> rho |== P -> rho |== Q.
Proof.
  intros.
  unfold satisfy, imp.
  tauto.
Qed.

Lemma exp_spec: forall {Omega} (U: Type) (rho: RVProdType Omega A0 As) (P: U -> assertion A0 As), rho |== exp U P <-> exists u, rho |== P u.
Proof.
  intros.
  unfold satisfy, exp.
  reflexivity.
Qed.

Lemma expR_spec: forall {Omega} (U: Type) {sU: SigmaAlgebra U} (a: RandomVariable Omega A0) (gamma: _RVProdType Omega As) (P: assertion A0 (U :: As)), (a, gamma) |== expR U P <-> exists u, 
@satisfy A0 sA0 (U :: As) (cons_SigmaAlgebras U As) Omega (a, (gamma, u)) P.
Proof.
  intros.
  unfold satisfy, expR.
  simpl.
  reflexivity.
Qed.

End Lemmas.

End PlainAssertion.

End PlainAssertion.


