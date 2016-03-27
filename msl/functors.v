(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.

Set Implicit Arguments.

Local Open Scope type.

Record functorFacts (PS : Type -> Type)
    (fmap : forall A B (f : A <--> B), PS A <--> PS B)
    : Type := FunctorFacts
{
  ff_id : forall A, fmap _ _ (id A, id A) = (id (PS A), id (PS A));
  ff_comp : forall A B C (f : B <--> C) (g : A <--> B), fmap _ _ f oooo fmap _ _ g = fmap _ _ (f oooo g)
}.

(* Parameterized structures *)
Class functor (F : Type -> Type) 
                        : Type := Functor {
  fmap : forall A B (f : A <--> B), F A <--> F B;
  functor_facts : functorFacts F fmap
}.

Lemma fmap_id {F} `{functor F} : forall A, (fmap (id A, id A)) = (id (F A), id (F A)).
Proof. intros. destruct H. simpl. destruct functor_facts0. rewrite ff_id0. auto. Qed.

Lemma fmap_comp {F} `{functor F} : forall A B C (f : B <--> C) (g : A <--> B),
  fmap f oooo fmap g = fmap (f oooo g).
Proof. intros. destruct H. destruct functor_facts0. simpl. rewrite ff_comp0. auto. Qed.

Lemma fmap_app {F} `{functor F} : forall A B C (f : B <--> C) (g : A <--> B) x,
  fst (fmap f) (fst (fmap g) x) = fst (fmap (f oooo g)) x.
Proof. intros. rewrite <- fmap_comp; destruct (fmap f), (fmap g); auto. Qed.

(* GENERATORS *)

Section ConstFunctor.
  Variable T : Type.

  Definition fconst (A : Type) : Type := T.
  Definition fconst_fmap (A B : Type) (f : A <--> B): fconst A <--> fconst B :=
    (id _, id _).

  Lemma ff_const : functorFacts fconst fconst_fmap.
  Proof with auto.
    constructor...
  Qed.

  Definition f_const : functor fconst := Functor ff_const.
  Existing Instance f_const.
End ConstFunctor.

Section IdentityFunctor.
  Definition fidentity (A : Type) : Type := A.
  Definition fidentity_fmap (A B : Type) (f : A <--> B) : fidentity A <--> fidentity B := 
    f.
  
  Lemma ff_identity : functorFacts fidentity fidentity_fmap.
  Proof with auto.
    constructor...
  Qed.
  
  Definition f_identity : functor fidentity := Functor ff_identity.
  Existing Instance f_identity.
End IdentityFunctor.  

Section PairFunctor.
  Variables F1 : Type -> Type.
  Variable fF1 : functor F1.
  Variable F2 : Type -> Type.
  Variable fF2 : functor F2.
  
  Definition fpair (A : Type) : Type := (F1 A * F2 A)%type.
  Definition fpair_fmap (A B : Type) (f : A <--> B): (fpair A <--> fpair B) :=
    (fun pA => match pA with (p1, p2) => (fst (fmap f) p1, fst (fmap f) p2) end,
     fun pB => match pB with (p1, p2) => (snd (fmap f) p1, snd (fmap f) p2) end).
  
  Lemma ff_pair : functorFacts fpair fpair_fmap.
  Proof with auto.
    constructor; intros.
    + unfold fpair_fmap; f_equal; extensionality p; destruct p;
      rewrite fmap_id; rewrite fmap_id...
    + unfold fpair_fmap; simpl; f_equal; extensionality p; destruct p; simpl;
      rewrite <- !fmap_comp; 
      destruct (@fmap F1 fF1 _ _ f), (@fmap F2 fF2 _ _ f),  (@fmap F1 fF1 _ _ g),  (@fmap F2 fF2 _ _ g); auto.
  Qed.

  Definition f_pair : functor fpair := Functor ff_pair.
  Existing Instance f_pair.
End PairFunctor.

Section OptionFunctor.
  Variable F:Type -> Type.
  Variable fF: functor F.

  Definition foption A := option (F A).
  Definition foption_fmap (A B : Type) (f : A <--> B): (foption A <--> foption B) :=
    (option_map (fst (fmap f)), option_map (snd (fmap f))).

  Lemma ff_option : functorFacts foption foption_fmap.
  Proof.
    constructor; intros.
    + unfold foption_fmap. simpl. 
      rewrite fmap_id. simpl.
      f_equal; extensionality p; destruct p; auto.

    + unfold foption_fmap. simpl. 
      rewrite <- !fmap_comp. simpl.
      f_equal; extensionality p; destruct p; simpl; destruct (fmap f), (fmap g); auto.
  Qed.

  Definition f_option : functor foption := Functor ff_option.
  Existing Instance f_option.
End OptionFunctor.

Section CoFunFunctor.
(* TODO: Maybe it should be called FunFunctor now. *)
(* For the domain, we require the constant to avoid covariance.  Maybe
    there is a nicer way to do this, but for now... 
  Variable dom : Type -> Type. 
  Variable ps_dom : pstruct dom.
  Definition pfun_fmap (A B:Type) (f:A->B) (g : B -> A) (x: pfun A) : pfun B := 
    (fmap f) oo (x oo fmap g).
*)
  Variable Dom : Type -> Type.
  Variable Rng : Type -> Type.  
  Variable fDom : functor Dom.
  Variable fRng : functor Rng.
  
  Definition ffun (A : Type) : Type := Dom A -> Rng A.
  Definition ffun_fmap (A B:Type) (f:A<-->B): (ffun A <--> ffun B) := 
    (fun fA => (fst (fmap f)) oo fA oo (snd (fmap f)), fun fB => (snd (fmap f)) oo fB oo (fst (fmap f))).

  Lemma ff_fun : functorFacts ffun ffun_fmap.
  Proof with auto.
    constructor; unfold ffun_fmap; intros.
    + rewrite !fmap_id.
      auto.
    + rewrite <- !fmap_comp. unfold double_compose.
      f_equal;
      extensionality x y; destruct (@fmap Rng fRng _ _ f), (@fmap Dom fDom _ _ f), (@fmap Rng fRng _ _ g), (@fmap Dom fDom _ _ g); auto.
  Qed.
  
  Definition f_fun : functor ffun := Functor ff_fun.
  Existing Instance f_fun.
End CoFunFunctor.

(*
Section SigmaFunctor.
  Variable I:Type.
  Variable F: I -> Type -> Type.
  Variable fF : forall i , functor (F i).
  
  Definition fsig X := @sigT I (fun i => F i X).

  Definition fsigma_map (A B:Type) (f:A -> B) (x:fsig A) : fsig B :=
    match x with
    | existT i x' => existT (fun i => F i B) i (fmap f x')
    end.

  Definition ff_sigma : functorFacts fsig fsigma_map.
  Proof.
    constructor; unfold fsigma_map; simpl; intros.
    extensionality x. destruct x. simpl.
    rewrite fmap_id. auto.
    extensionality x. destruct x. simpl.
    rewrite <- fmap_comp.
    auto.
  Qed.

  Definition f_sigma : functor fsig := Functor ff_sigma.
  Existing Instance f_sigma.
End SigmaFunctor.
  
Section SubsetFunctor.
  Variable F:Type -> Type.
  Variable fF: functor F.

  Variable P : forall A, F A -> Prop.

  Variable HPfmap1 : forall A B (f:A->B) x, 
    P x -> P (fmap f x).

  Definition subset A := { x:F A | P x }.
  
  Definition subset_fmap (A B:Type) (f:A->B) (x:subset A) : subset B :=
    match x with
    | exist x' H => exist (fun x => P x) (fmap f x') (HPfmap1 f H)
    end.

  Lemma ff_subset : functorFacts subset subset_fmap.
  Proof.
    constructor; unfold subset_fmap; intros.
    extensionality. destruct x; simpl.
    generalize (HPfmap1 (id A) p).
    rewrite fmap_id; intros.
    unfold id; simpl.
    replace p0 with p by apply proof_irr; auto.
    extensionality. destruct x; simpl.
    unfold compose at 1.
    generalize (HPfmap1 (f oo g) p).
    rewrite <- fmap_comp.
    intros.
    replace p0 with
      (HPfmap1 f (HPfmap1 g p))
      by apply proof_irr; auto.
  Qed.

  Definition f_subset : functor subset := Functor ff_subset.
  Existing Instance f_subset.
End SubsetFunctor.
*)
Unset Implicit Arguments.
