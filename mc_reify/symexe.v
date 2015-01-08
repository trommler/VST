Require Export mc_reify.reify.
Import floyd.proofauto.
Require Export mc_reify.bool_funcs.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.func_defs.

Local Open Scope logic.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Lemma local2ptree_eq :
forall (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (T1 : PTree.t val)
         (T2 : PTree.t (type * val)) (Q' : list (environ -> Prop)),
       local2ptree Q T1 T2 Q' ->
       PROPx P (LOCALx Q (SEPx R))
       = PROPx P (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Admitted.

Ltac do_local2ptree := do 2 (erewrite local2ptree_eq; [ | repeat constructor ]);
repeat rewrite LocalD_to_localD.

Ltac pull_sep_lift R :=
match R with
| ((`?H) :: ?T) => let rest := pull_sep_lift T in constr:(cons H rest)
| (@nil _) => constr:(@nil mpred)
end.

Ltac extract_sep_lift_semax :=
  match goal with
      [ |- context [semax _ (*(PROP (?P1) (LOCALx ?Q1 SEP (?R1)))*) 
                 (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ 
                 (normal_ret_assert (*(PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))))*) _)]] =>
      let R1' := pull_sep_lift R1 in
      (*let R2' := pull_sep_lift R2 in*)
      try (change (PROPx (P1) (LOCALx Q1 (SEPx (R1)))) 
      with (assertD nil Q1 R1'))(*;
      try  (change (PROPx (P2) (LOCALx Q2 (SEPx (R2)))) 
      with (assertD nil Q2 R2'))*)
end.

Ltac hnf_tycontext :=
match goal with
[ |- context [semax ?s _ _ _] ] => let ss := eval hnf in s in change s with ss
end.

Ltac prepare_reify :=
do_local2ptree;
extract_sep_lift_semax;
hnf_tycontext.


Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Section tbled.

Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Lemma semax_seq_reif c1 c2 : forall  (Espec : OracleKind) 
         (P : environ -> mpred)  (P' : environ -> mpred)
          (Q : ret_assert) (Delta : tycontext) ,
       @semax Espec Delta P c1 (normal_ret_assert P') ->
       @semax Espec (update_tycon Delta c1) P' c2 Q ->
       @semax Espec Delta P (Ssequence c1 c2) Q.
intros.
eapply semax_seq'; eauto.
Qed.

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Fixpoint get_delta_statement (e : expr typ func)  :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) 
                     (App (Inj (inr (Smx (ftycontext t v r gt)))) gs)) _) 
           (Inj (inr (Smx (fstatement s))))) _ => Some ((t,v,r,gt), s)
| App _ e 
| Abs _ e => get_delta_statement e
| _ => None
end.

Definition skip_lemma : my_lemma.
reify_lemma reify_vst 
@semax_skip.
Defined. 

Definition seq_lemma (s1 s2: statement)  : my_lemma.
reify_lemma reify_vst (semax_seq_reif s1 s2).
Defined.

Definition set_lemma (id : positive) (e : Clight.expr) (t : PTree.t (type * bool))
         (v : PTree.t type) (r : type) (gt : PTree.t type): my_lemma.
reify_lemma reify_vst (semax_set_localD id e t v r gt).
Defined.

Print set_lemma.


Definition THEN' (r1 r2 : rtac typ (expr typ func)) := THEN r1 (runOnGoals r2).

Definition THEN (r1 r2 : rtac typ (expr typ func)) := 
  THEN' r1 (THEN' (INSTANTIATE typ func) r2).

Definition update_tycon_tac (l : list (option (expr typ func)))
(e : expr typ func) (args : list (expr typ func))
	: expr typ func :=
match e with
    | (Inj (inr (Smx (fupdate_tycon)))) => 
      match args with
          | [App (Inj (inr (Smx (ftycontext t v r gt)))) gs; (Inj (inr (Smx (fstatement s))))] => 
            App (Inj (inr (Smx (ftycontext (update_temp t s) v r gt)))) gs
          | _ =>  AppN.apps e args
      end
    | _ => AppN.apps e args
end.


Definition SIMPL_DELTA : rtac typ (ExprCore.expr typ func) :=
SIMPLIFY (fun _ _ _ _=>beta_all update_tycon_tac).

Definition INTROS := (REPEAT 10 (INTRO typ func)).

Definition APPLY_SKIP :=  (APPLY typ func  skip_lemma).

Definition run_tac (t: rtac typ (ExprCore.expr typ func)) e := 
  t nil nil 0%nat 0%nat (CTop nil nil) (ctx_empty (expr := expr typ func)) e.

Definition run_tac_intros e :=
run_tac (THEN INTROS e).

Definition APPLY_SEQ' s1 s2 := (EAPPLY typ func (seq_lemma s1 s2)).

Definition APPLY_SEQ s1 s2 := THEN (APPLY_SEQ' s1 s2) (SIMPL_DELTA).

Definition APPLY_SET' id e t v r gt:=
EAPPLY typ func  (set_lemma id e t v r gt).

Definition SYMEXE_STEP
: rtac typ (expr typ func)  :=
  AT_GOAL  
    (fun c s e => 
         match (get_delta_statement e) with
           | Some ((t, v, r, gt) , st) =>  
             match st with 
               | Sskip => APPLY_SKIP 
               | Ssequence s1 s2 => APPLY_SEQ s1 s2  
               | Sset id exp => THEN (APPLY_SET' id exp t v r gt) 
                                     (TRY (FIRST [(REFLEXIVITY_BOOL tbl);
                                                   (REFLEXIVITY tbl)])) 
               | _ => FAIL
             end
           | None => FAIL
         end).

Existing Instance func_defs.Expr_ok_fs.


Definition SYMEXE_TAC := THEN INTROS (REPEAT 1000 (SYMEXE_STEP)).

Definition SYMEXE1_TAC := THEN INTROS (SYMEXE_STEP).

Definition rreflexivity e :=
run_tac (REFLEXIVITY tbl) e.

Definition symexe e :=
run_tac (SYMEXE_TAC ) e .

Definition symexe1 e  :=
run_tac (SYMEXE1_TAC ) e.

Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ ExprD.Expr_expr (expr typ func)
          (fun tus tvs e => ExprDsimul.ExprDenote.exprD' tus tvs typrop e)
          _
          nil nil.


Require Import MirrorCharge.RTac.Cancellation.



Fixpoint is_pure (e : expr typ func) := 
match e with 
| App e1 e2 => is_pure e1
| (Inj (inr (Sep fprop))) => true
| _ => false
end.

Definition CANCEL e := run_tac (THEN INTROS (CANCELLATION typ func tympred is_pure)) e.
Locate data_at.

Parameter f : nat -> nat.

Goal f = f.
reify_expr_tac.
(* App(App (Inj (inr (Other (feq (tyArr tynat tynat))))) (Ext 1%positive))
         (Ext 1%positive) *)
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITY tbl)) e.
(*     = Solved (TopSubst (expr typ func) [] []) *)
Abort.

Goal forall n, f n = f n.
reify_expr_tac.
(*App (ILogicFunc.fForall tynat typrop)
         (Abs tynat
            (App
               (App (Inj (inr (Other (feq tynat))))
                  (App (Ext 1%positive) (ExprCore.Var 0%nat)))
               (App (Ext 1%positive) (ExprCore.Var 0%nat)))) *)
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITY tbl)) e.
(*    = Fail *)
Abort.

Goal forall (sh : share) (v1 v2 : val), False.
intros.
reify_vst (data_at sh tint v1 v2).
Abort.

Goal forall sh v1 v2, (data_at sh tint v1 v2) |-- (data_at sh tint v1 v2).
intros. simpl reptype in *.
reify_expr_tac.
Eval vm_compute in CANCEL e.
Abort.

Goal forall P Q b,  !!b && P * Q |-- !!b && Q * P .
reify_expr_tac.
Abort.

Goal forall (sh : share), sh = sh.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITYTAC tbl)) e.
Abort.


Goal forall sh ty v1 v2, mapsto sh ty v1 v2 = mapsto sh ty v1 v2.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITYTAC tbl)) e.
Eval vm_compute in run_tac (THEN INTROS (CANCELLATION typ func tympred is_pure)) e.
Abort.

Let Expr_expr := (Expr_expr_fs tbl).
Existing Instance Expr_expr.

Definition exprD_Prop (uvar_env var_env : env) (e : expr typ func) :=
  match exprD uvar_env var_env e typrop with
    | Some e' => e' 
    | None => True
  end.

Definition goalD_Prop (uvar_env var_env : env) goal :=
  let (tus, us) := split_env uvar_env in
  let (tvs, vs) := split_env var_env in
  match goalD tus tvs goal with
    | Some e => e us vs
    | None => False
  end.

Definition goalD_aux tus tvs goal (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) :=
  match goalD tus tvs goal with
    | Some e => Some (e us vs)
    | None => None
  end.

Definition run_tac' tac goal :=
  runOnGoals tac nil nil 0 0 (CTop nil nil) 
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Lemma run_rtac_More tac s goal e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac' tac (GGoal e) = More_ s goal) :
  goalD_Prop nil nil goal -> exprD_Prop nil nil e.
Proof.
  intros He'.
  apply runOnGoals_sound_ind with (g := GGoal e) (ctx := CTop nil nil) 
  	(s0 := TopSubst (expr typ func) nil nil) in Hsound.
  unfold rtac_spec in Hsound. simpl in Hsound.
  unfold run_tac' in Hres. simpl in Hres.
  rewrite Hres in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound H1 H2).
  destruct Hsound as [Hwfs [Hwfg Hsound]].
  unfold propD, exprD'_typ0 in Hsound.
  simpl in Hsound. unfold exprD_Prop, exprD; simpl.
  Require Import ExtLib.Tactics.
  forward; inv_all; subst.

  destruct Hsound.
  inversion Hwfs; subst.
  simpl in H0; inv_all; subst.
  unfold pctxD in H0; inv_all; subst.
  apply H5.
  unfold goalD_Prop in He'. simpl in He'. forward; inv_all; subst.
Qed.

Lemma run_rtac_Solved tac s e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac' tac (GGoal e) = Solved s) :
  exprD_Prop nil nil e.
Proof.
  unfold run_tac' in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs Hsound].
  simpl in Hsound.
  unfold propD, exprD'_typ0 in Hsound.
  unfold exprD_Prop.
  
  simpl in Hsound. unfold exprD. simpl. forward.
  destruct Hsound. 
  inversion Hwfs; subst. simpl in H8. inv_all; subst.
  admit.
Qed.

End tbled.

Require Import denote_tac.

Ltac run_rtac reify term_table tac_sound :=
  match type of tac_sound with
    | rtac_sound ?tac =>
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux reify term_table P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac' tac (GGoal name)) in 
	          let result := eval vm_compute in goal_result in
	          match result with
	            | More_ ?s ?g => 
	              cut (goalD_Prop nil nil g); [
	                let goal_resultV := g in
	               (* change (goalD_Prop nil nil goal_resultV -> exprD_Prop nil nil name);*)
	                exact_no_check (@run_rtac_More tac _ _ _ tac_sound
	                	(@eq_refl (Result (CTop nil nil)) (More_ s goal_resultV) <:
	                	   run_tac' tac (GGoal goal) = (More_ s goal_resultV)))
	                | cbv_denote
	              ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved tac s name tac_sound 
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac' tac (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.