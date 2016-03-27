(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Open Local Scope nat_scope.

Require Import msl.ageable.
Require Import msl.functors.
Require Import msl.predicates_hered.

Module Type TY_FUNCTOR_PROP.
  Parameter F : Type -> Type.
  Parameter f_F : functor F.
  Existing Instance f_F.

  Parameter other : Type.
End TY_FUNCTOR_PROP.

Module Type KNOT_HERED.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter knot:Type.
  Parameter ag_knot : ageable knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition predicate := pred (knot * other).

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fst (fmap (approx n, approx n)) f).

  Axiom approx_spec : forall n p k,
    (approx n p) k = (level k < n /\ p k).

  Axiom knot_level : forall k:knot, level k = fst (unsquash k).

  Axiom knot_age1 : forall k,
    age1 k = 
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

End KNOT_HERED.

Module KnotHered (TF':TY_FUNCTOR_PROP) : KNOT_HERED with Module TF:=TF'.
  Module TF:=TF'.
  Import TF.

  Definition sinv_prod X := prod X (F X * other -> Prop).

  Record guppy_ty: Type := {
    GT_type: Type;
    GT_prop: sinv_prod GT_type -> Prop;
    GT_func: GT_type -> sinv_prod GT_type;
    GT_sound: forall x: GT_type, GT_prop (GT_func x)
  }.

  Section Guppy_Step.

    Variable Z: guppy_ty.
   
    Definition GS_type: Type := sig (GT_prop Z).

    Definition backward: GS_type -> GT_type Z := fun k => fst (proj1_sig k).

    Definition forward: GT_type Z -> GS_type := fun k => exist _ (GT_func Z k) (GT_sound Z k).
   
    Definition GS_prop: sinv_prod GS_type -> Prop :=
      fun (k: GS_type * (F GS_type * other -> Prop)) =>
        let k': GT_type Z * (F (GT_type Z) * other -> Prop) := proj1_sig (fst k) in
        forall (xf : F GS_type) (o:other),
          let xf' : F (GT_type Z) := fst (fmap (backward, forward)) xf in
          (snd k) (xf, o) -> (snd k') (xf', o).

(*
    Definition GS_func: GS_type -> sinv_prod GS_type :=
      fun k =>
        (k,
          fun xfo: F GS_type * other =>
            let (xf, o) := xfo in
            let xf' : F (GT_type Z) := fst (fmap (backward, forward)) xf in
            let p : F (GT_type Z) * other -> Prop := snd (proj1_sig k) in
              p (xf', o)
        ).

    Lemma GS_sound: forall k: GS_type, GS_prop (GS_func k).
    Proof. intros. unfold GS_prop, GS_func. auto. Qed.
*)

    Definition GS_func: GS_type -> sinv_prod GS_type :=
      fun k => (k, fun _ => False).

    Lemma GS_sound: forall k: GS_type, GS_prop (GS_func k).
    Proof. intros. unfold GS_prop, GS_func. intros. inversion H. Qed.

    Definition guppy_step: guppy_ty := Build_guppy_ty GS_type GS_prop GS_func GS_sound.

  End Guppy_Step.

  Definition guppy_base : guppy_ty := Build_guppy_ty unit (fun _ => True) (fun k => (k, fun _ => False)) (fun x => I).

  Fixpoint guppy (n:nat) : guppy_ty :=
    match n with
    | 0    => guppy_base
    | S n' => guppy_step (guppy n')
    end.

  Definition sinv (n:nat) : Type := GT_type (guppy n).
  Definition sinv_prop (n:nat) : prod (sinv n) (F (sinv n) * other -> Prop) -> Prop := GT_prop (guppy n).

  Lemma fst_GT_func: forall n k, fst (GT_func (guppy n) k) = k.
  Proof. intros. destruct n; reflexivity. Qed.

  Lemma snd_GT_func: forall n k k', snd (GT_func (guppy n) k) k' = False.
  Proof. intros. destruct n; reflexivity. Qed.

  Fixpoint floor (m:nat) (n:nat) (p:sinv (m+n)) : sinv n :=
    match m as m' return forall (p : sinv (m'+n)), sinv n with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst (proj1_sig p))
    end p.

  Definition knot := { n:nat & F (sinv n) }.

  Definition fmap_backward (n: nat): F (sinv (S n)) -> F (sinv n) := fst (@fmap F f_F _ _ (backward (guppy n), forward (guppy n))).

  Definition fmap_forward (n: nat): F (sinv n) -> F (sinv (S n)) := snd (@fmap F f_F _ _ (backward (guppy n), forward (guppy n))).

  Definition k_age1 (k:knot) : option (knot) :=
    match k with
      | (existT 0 f) => None
      | (existT (S m) f) => Some
          (existT (F oo sinv) m (fmap_backward m f))
    end.

  Definition k_age (k1 k2:knot) := k_age1 k1 = Some k2.

  Definition ko_age1 (x:knot * other) :=
    match k_age1 (fst x) with
    | None => None
    | Some a' => Some (a',snd x)
    end.
  Definition ko_age x y := ko_age1 x = Some y.

  Definition predicate := { p:knot * other -> Prop | hereditary ko_age p }.

  Definition app_sinv (n:nat) (p:sinv (S n)) (x:F (sinv n) * other) :=
    snd (proj1_sig p) x.


  Lemma app_sinv_age : forall n (p:sinv (S (S n))) (f:F (sinv (S n)) * other),
    app_sinv (S n) p f ->
    app_sinv n (fst (proj1_sig p)) (fmap_backward n (fst f), snd f).
  Proof.
    intros.
    unfold app_sinv in *.
    destruct p; simpl in *; fold guppy in *.
    apply g; auto.
    destruct f; auto.
  Qed.

  Section stratifies.
    Variable Q:knot * other -> Prop.
    Variable HQ:hereditary ko_age Q.

    Fixpoint stratifies (n:nat) : sinv n -> Prop :=
    match n as n' return sinv n' -> Prop with
    | 0 => fun _ => True
    | S n' => fun (p:sinv (S n')) =>
          stratifies n' (fst (proj1_sig p)) /\
          forall (k:F (sinv n')) (o:other), snd (proj1_sig p) (k,o) <-> Q (existT (F oo sinv) n' k,o)
    end.

    Lemma stratifies_unique : forall n p1 p2,
      stratifies n p1 ->
      stratifies n p2 ->
      p1 = p2.
    Proof.
      induction n; simpl; intuition.
      destruct p1; destruct p2; auto.
      destruct p1; destruct p2.
      simpl in *; fold guppy in *.
      cut (x = x0).
      intros.
      revert g g0 H2 H3.
      rewrite <- H0.
      intros.
      replace g0 with g by (apply proof_irr); auto.
      destruct x; destruct x0; simpl in *.
      apply injective_projections; simpl.
      apply IHn; auto.
      extensionality; intros.
      simpl in *.
      destruct (H2 (fst x) (snd x)); destruct (H3 (fst x) (snd x)).
      apply prop_ext; destruct x; intuition.
    Qed.

    Definition stratify (n:nat) : { x:sinv n | stratifies n x }.
    Proof.
      induction n.
      exists tt; simpl; exact I.
      assert (HX:
        GT_prop (guppy n)
        (projT1 IHn, fun v : F (sinv n) * other => Q (existT (F oo sinv) n (fst v),snd v))).
      destruct n.
      simpl; exact I.
      simpl; intros.
      destruct IHn; simpl.
      simpl in s; destruct s.
      destruct x; simpl in *; fold guppy in *.
      destruct x; simpl in *.
      hnf; simpl; intros.
      rewrite H0.
      eapply HQ.
      2: apply H1.
      simpl; reflexivity.
      exists ((exist (fun x => GT_prop (guppy n) x) ( projT1 IHn, fun v:F (sinv n) * other => Q (existT (F oo sinv) n (fst v),snd v) ) HX)).
      simpl; split.
      destruct IHn; auto.
      unfold app_sinv; simpl; intros.
      split; trivial.
    Qed.
  End stratifies.

  Lemma decompose_nat : forall (x y:nat), { m:nat & y = (m + S x) } + { ge x y }.
  Proof.
    intros x y; revert x; induction y; simpl; intros.
    right; auto with arith.
    destruct (IHy x) as [[m H]|H].
    left; exists (S m); omega.
    destruct (eq_nat_dec x y).
    left; exists O; omega.
    right; omega.
  Qed.

  Definition unstratify (n:nat) (p:sinv n) : knot * other -> Prop := fun w =>
    match w with (existT nw w',o) =>
      match decompose_nat nw n with
        | inleft (existT m Hm) => snd (proj1_sig (floor m (S nw) (eq_rect  n _ p (m + S nw) Hm))) (w',o)
        | inright H => False
      end
    end.

  Lemma floor_shuffle:
    forall (m1 n : nat)
      (p1 : sinv (m1 + S n)) (H1 : (m1 + S n) = (S m1 + n)),
      floor (S m1) n (eq_rect (m1 + S n) sinv p1 (S m1 + n) H1) = fst (proj1_sig (floor m1 (S n) p1)).
  Proof.
    intros.
    remember (fst (proj1_sig (floor m1 (S n) p1))) as p.
    fold guppy in *.
    revert n p1 H1 p Heqp.
    induction m1; simpl; intros.
    replace H1 with (refl_equal (S n)) by (apply proof_irr); simpl; auto.
    assert (m1 + S n = S m1 + n) by omega.
    destruct p1 as [[p1 f'] Hp1]; simpl in *; fold guppy in *.
    generalize (IHm1 n p1 H p Heqp).
    clear.
    revert Hp1 H1; generalize H.
    revert p1 f'.
    rewrite H.
    simpl; intros.
    replace H1 with (refl_equal (S (S (m1 + n)))) by (apply proof_irr).
    simpl.
    replace H0 with (refl_equal (S (m1+n))) in H2 by (apply proof_irr).
    simpl in H2.
    trivial.
  Qed.

  Lemma unstratify_hered : forall n p,
    hereditary ko_age (unstratify n p).
  Proof.
    intros.
    hnf; intros k k'; intros.
    unfold ko_age in H.
    destruct k.
    destruct k.
    destruct x.
    discriminate.
    destruct k' as [k' o'].
    assert (o = o').
    Focus 1. {
      hnf in H.
      simpl in H.
      inv H. auto.
    } Unfocus.
    subst o'.
    replace k' with (existT (F oo sinv) x (fmap_backward x f)).
    2: inversion H; auto.
    clear H.
    case_eq (decompose_nat x n); intros.
    destruct s.
    case_eq (decompose_nat (S x) n); intros.
    destruct s.
    destruct n.
    elimtype False; omega.
    assert (S x1 = x0) by omega; subst x0.
    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1.
    generalize e e0; revert p; rewrite e0; intros.
    rewrite floor_shuffle.
    replace e2 with (refl_equal (x1 + S (S x))) in H0;
      simpl eq_rect in H0.
    2: apply proof_irr.
    change f with (fst (f,o)).
    change o with (snd (f,o)).
    eapply app_sinv_age; apply H0.

    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1.
    intuition.

    case_eq (decompose_nat (S x) n); intros.
    destruct s.
    elimtype False; omega.
    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1; auto.
  Qed.

  Lemma unstratify_Q : forall n (p:sinv n) Q,
    stratifies Q n p ->
    forall (k:knot) o,
      projT1 k < n ->
      (unstratify n p (k,o) <-> Q (k,o)).
  Proof.
    intros.
    unfold unstratify.
    destruct k.
    destruct (decompose_nat x n).
    destruct s.
    simpl in H0.
    2: simpl in *; elimtype False; omega.
    clear H0.
    revert p H.
    generalize e.
    rewrite e.
    intros.
    replace e0 with (refl_equal (x0 + S x)) by apply proof_irr.
    simpl.
    clear e e0.
    revert p H.
    induction x0; simpl; intros.
    destruct H.
    auto.
    destruct H.
    apply IHx0.
    auto.
  Qed.

  Lemma stratifies_unstratify_more : 
    forall (n m1 m2:nat) (p1:sinv (m1+n)) (p2:sinv (m2+n)),
      floor m1 n p1 = floor m2 n p2 ->
      (stratifies (unstratify (m1+n) p1) n (floor m1 n p1) ->
       stratifies (unstratify (m2+n) p2) n (floor m2 n p2)).
  Proof.
    induction n; intuition.
    split.
    assert (m2 + S n = S m2 + n) by omega.
    erewrite <- floor_shuffle.
    instantiate (1:=H1).
    replace (unstratify (m2 + S n) p2)
      with (unstratify (S m2 + n) (eq_rect (m2 + S n) sinv p2 (S m2 + n) H1)). 
    assert (m1 + S n = S m1 + n) by omega.
    eapply (IHn (S m1) (S m2)
      (eq_rect (m1 + S n) sinv p1 (S m1 + n) H2)).
    rewrite floor_shuffle.
    rewrite floor_shuffle.
    rewrite H; auto.
    clear - H0.
    rewrite floor_shuffle.
    simpl in H0.
    destruct H0.
    clear H0.
    revert p1 H.
    generalize H2.
    rewrite <- H2.
    intros.
    replace H0 with (refl_equal (m1 + S n)) by apply proof_irr; auto.
    clear.
    revert p2.
    generalize H1.
    rewrite H1.
    intros.
    replace H0 with (refl_equal (S m2 + n)) by apply proof_irr; auto.

    intros.
    simpl.
    destruct (decompose_nat n (m2 + S n)).
    destruct s.
    assert (m2 = x).
    omega.
    subst x.
    replace e with (refl_equal (m2 + S n)).
    simpl; tauto.
    apply proof_irr.
    elimtype False; omega.
  Qed.

  Lemma stratifies_unstratify: forall n (p: sinv n), stratifies (unstratify n p) n p.
  Proof.
    induction n.
    simpl; intros; auto.
    intros.
    simpl; split.

    assert (stratifies (unstratify n (fst (proj1_sig p))) n (fst (proj1_sig p))).
    apply IHn.
    apply (stratifies_unstratify_more n 0 1 (fst (proj1_sig p)) p).
    simpl; auto.
    auto.

    intros.
    destruct (decompose_nat n (S n)).
    destruct s.
    assert (x = 0) by omega.
    subst x.
    simpl.
    simpl in e.
    replace e with (refl_equal (S n)) by apply proof_irr.
    simpl.
    split; auto.
    elimtype False; omega.
  Qed.

  Lemma stratify_unstratify : forall n p H,
    proj1_sig (stratify (unstratify n p) H n) = p.
  Proof.
    intros.
    apply stratifies_unique with (unstratify n p).
    + destruct (stratify _ H n).
      simpl; auto.
    + apply stratifies_unstratify.
  Qed.

  Definition strat (n:nat) (p:predicate) : sinv n :=
    proj1_sig (stratify (proj1_sig p) (proj2_sig p) n).

  Definition unstrat (n:nat) (p:sinv n) : predicate :=
    exist (hereditary ko_age) (unstratify n p) (unstratify_hered n p).

  Definition squash (x:nat * F predicate) : knot :=
    match x with (n,f) => existT (F oo sinv) n (fst (fmap (strat n, unstrat n)) f) end.

  Definition unsquash (k:knot) : nat * F predicate :=
    match k with existT n f => (n, fst (fmap (unstrat n, strat n)) f) end.

  Definition level (x:knot) : nat := fst (unsquash x).
  Program Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => level (fst w) < n /\ p w.
  Next Obligation.
    hnf; simpl; intros.
    intuition.
    unfold level in *.
    unfold unsquash in *.
    destruct a0; simpl in H.
    destruct x; try discriminate.
    inv H.
    simpl in *; omega.
    destruct p; simpl in *.
    eapply h; eauto.
  Qed.

  Lemma strat_unstrat : forall n,
    strat n oo unstrat n = id (sinv n).
  Proof.
    intros; extensionality p.
    unfold compose, id.
    unfold strat, unstrat.
    simpl.
    rewrite stratify_unstratify.
    auto.
  Qed.

  Lemma predicate_eq : forall (p1 p2:predicate),
    proj1_sig p1 = proj1_sig p2 ->
    p1 = p2.
  Proof.
    intros; destruct p1; destruct p2; simpl in H.
    subst x0.
    replace h0 with h by apply proof_irr.
    auto.
  Qed.

  Lemma unstrat_strat : forall n,
    unstrat n oo strat n = approx n.
  Proof.
    intros.
    extensionality.
    unfold compose.
    unfold unstrat, strat.
    unfold approx.
    apply predicate_eq.
    simpl.
    extensionality k.
    apply prop_ext; intuition.
    unfold unstratify in H.
    destruct a.
    destruct (decompose_nat x0 n).
    unfold level.
    simpl.
    destruct s.
    omega.
    elim H.
    rewrite <- unstratify_Q.
    apply H.
    destruct (stratify (proj1_sig x) (proj2_sig x) n); auto.
    unfold unstratify in H.
    destruct a; simpl.
    destruct (decompose_nat x0 n).
    destruct s; omega.
    elim H.
    rewrite unstratify_Q.
    apply H1.
    destruct (stratify (proj1_sig x) (proj2_sig x) n); auto.
    unfold level in H0.
    destruct a; simpl in *.
    auto.
  Qed.

  Lemma squash_unsquash : forall k, squash (unsquash k) = k.
  Proof.
    intros.
    destruct k; simpl.
    rewrite fmap_app.
    unfold double_compose.
    rewrite strat_unstrat.
    rewrite fmap_id.
    reflexivity.
  Qed.

  Lemma unsquash_squash : forall n f,
    unsquash (squash (n,f)) = (n, fst (fmap (approx n, approx n)) f).
  Proof.
    intros.
    unfold unsquash, squash.
    rewrite fmap_app.
    unfold double_compose.
    rewrite unstrat_strat.
    reflexivity.
  Qed.

  Lemma unstrat_strat_Sx : forall x,
    forward (guppy x) = strat (S x) oo unstrat x.
  Proof.
    intros.
    extensionality k.
    change (sinv x) in k.
    unfold compose.
    unfold strat, unstrat.
    simpl.
    change (GS_type (guppy x)) with (sinv (S x)).
    apply stratifies_unique with (unstratify (S x) (forward _ k)).
    + simpl.
      destruct (decompose_nat x (S x)); [| exfalso; omega].
      destruct s.
      assert (x0 = 0) by omega; subst; simpl.
      rewrite <- eq_rect_eq; clear e.
      simpl.
      split; [| intros; tauto].
      eapply (stratifies_unstratify_more x 0 1 ).
      1: reflexivity.
      simpl.
      apply stratifies_unstratify.
    + destruct ((stratify (unstratify x k) (unstratify_hered x k) (S x))).
      simpl.
      destruct (decompose_nat x (S x)); [| exfalso; omega].
      destruct s0.
      assert (x1 = 0) by omega; subst; simpl.
      rewrite <- eq_rect_eq; clear e.
      cut (x0 = forward _ k); intros.
      - subst x0.
        split; [| intros; tauto].
        eapply (stratifies_unstratify_more x 0 1).
        1: simpl; reflexivity.
        simpl.
        apply stratifies_unstratify.
      - eapply stratifies_unique.
        apply s.
        simpl.
        split.
        * rewrite fst_GT_func.
          apply stratifies_unstratify.
        * intros.
          destruct (decompose_nat x x) as [[? ?] |]; [exfalso; omega |].
          rewrite snd_GT_func.
          tauto.
  Qed.
    
  Lemma strat_unstrat_Sx : forall x,
    backward (guppy x) = strat x oo unstrat (S x).
  Proof.
    intros.
    extensionality k.
    change (sinv (S x)) in k.
    unfold compose.
    unfold strat, unstrat.
    simpl.
    apply stratifies_unique with (unstratify x (fst (proj1_sig k))).
    + revert k; induction x; simpl; auto.
      intros.
      split.
      - eapply (stratifies_unstratify_more x 0 1 ).
        1: simpl; reflexivity.
        simpl.
        apply IHx.
      - intros.
        destruct (decompose_nat x (S x)).
        * destruct s.
          assert (x0 = 0) by omega; subst x0.
          simpl in *.
          replace e with (refl_equal (S x)) by apply proof_irr; simpl.
          tauto.
        * elimtype False; omega.
    + destruct (stratify (unstratify (S x) k) (unstratify_hered (S x) k) x).
      1: simpl; auto.
      cut (x0 = (fst (proj1_sig k))); intros.
      - subst x0.
        eapply (stratifies_unstratify_more x 1 0).
        1: simpl; reflexivity.
        simpl; auto.
      - eapply stratifies_unique.
        apply s.
        eapply (stratifies_unstratify_more x 0 1).
        1: simpl; reflexivity.
        simpl.
        generalize (fst (proj1_sig k) : sinv x).
        clear.
        induction x; simpl; intuition.
        * eapply (stratifies_unstratify_more x 0 1).
          1: simpl; reflexivity.
          simpl.
          apply IHx.
        * destruct (decompose_nat x (S x)); [| omega].
          destruct s0.
          assert (x0 = 0) by omega; subst.
          simpl in *.
          replace e with (refl_equal (S x)); simpl; auto.
          apply proof_irr.
        * destruct (decompose_nat x (S x)); [| elim H].
          destruct s0.
          assert (x0 = 0) by omega; subst.
          simpl in *.
          replace e with (refl_equal (S x)) in H; simpl; auto.
          apply proof_irr.
  Qed.

  Lemma double_compose_strat_unstrat_Sx : forall x,
    (backward (guppy x), forward (guppy x)) = (strat x, unstrat x) oooo (unstrat (S x), strat (S x)).
  Proof.
    intros.
    simpl.
    rewrite strat_unstrat_Sx, unstrat_strat_Sx.
    auto.
  Qed.
  
  Lemma unsquash_inj : forall k k',
    unsquash k = unsquash k' -> k = k'.
  Proof.
    intros.
    rewrite <- (squash_unsquash k).
    rewrite <- (squash_unsquash k').
    congruence.
  Qed.

  Lemma knot_age_age1 : forall k k',
    k_age1 k = Some k' <->
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end = Some k'.
  Proof.
    split; intros.
    unfold k_age1 in H.
    unfold unsquash in H.
    destruct k.
    destruct x; auto.
    inv H.
    simpl.
    rewrite fmap_app.
    rewrite <- (double_compose_strat_unstrat_Sx x).
    reflexivity.

    simpl in H.
    destruct k.
    destruct x.
    discriminate.
    inv H.
    hnf; simpl.
    unfold k_age1.
    rewrite fmap_app.
    rewrite <- (double_compose_strat_unstrat_Sx x).
    auto.
  Qed.

  Program Instance ag_knot : ageable knot :=
  { age1 := k_age1
  ; level := level
  }.
  Next Obligation.
    econstructor.
    + (* unage *)
      intros.
      case_eq (unsquash x'); intros.
      exists (squash (S n, f)). 
      rewrite knot_age_age1.
      rewrite unsquash_squash.
      f_equal.
      apply unsquash_inj.
      rewrite unsquash_squash.
      rewrite H.
      f_equal.
      cut (f = fst (fmap (approx n, approx n)) f).
      - intros.
        rewrite fmap_app.
        pattern f at 2. rewrite H0.
        f_equal.
        f_equal.
        simpl.
        f_equal; extensionality p.
        * apply predicate_eq.
          extensionality w.
          simpl. apply prop_ext.
          intuition.
        * apply predicate_eq.
          extensionality w.
          simpl. apply prop_ext.
          intuition.
      - generalize H; intro.
        rewrite <- (squash_unsquash x') in H.
        rewrite H0 in H.
        rewrite unsquash_squash in H.
        congruence.
      
    + (* level 0 *)
      intro x. destruct x; simpl.
      destruct x; intuition; discriminate.
      
    + (* level S *)
      intros. destruct x; simpl in *.
      destruct x. discriminate.
      inv H. simpl. auto.
  Qed.

  Existing Instance ag_prod.

  Lemma approx_spec : forall n p (k:knot * other),
    proj1_sig (approx n p) k = (ageable.level k < n /\ proj1_sig p k).
  Proof.
    intros.
    apply prop_ext.
    unfold approx; simpl.
    intuition; simpl in *; auto.
  Qed.

  Lemma knot_level : forall k:knot, level k = fst (unsquash k).
  Proof. reflexivity. Qed.

  Lemma knot_age1 : forall k,
    age1 k = 
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intros. simpl.
    case_eq (k_age1 k). intros.
    rewrite knot_age_age1 in H.
    auto.
    destruct k; simpl. destruct x. auto.
    intros. discriminate.
  Qed.

End KnotHered.
