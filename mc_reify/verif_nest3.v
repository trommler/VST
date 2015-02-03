Require Import floyd.proofauto.
Require Import progs.nest3.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  [] 
        PROP  ()
        LOCAL (var _p t_struct_c p)
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tint ]
        PROP  ()
        LOCAL (var _p t_struct_c p; temp 1%positive (Vint (snd (snd (snd v)))))
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p)).

Definition update222 (i: int) (v: reptype' t_struct_c) : reptype' t_struct_c :=
   (fst v, (fst (snd v), (fst (snd (snd v)), i))).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c, p : val
  PRE  [ _i OF tint ] 
        PROP ()
        LOCAL(temp _i (Vint i); var _p t_struct_c p)
        SEP(`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tvoid ]
        `(data_at Ews t_struct_c (repinj _ (update222 i v)) p).

Definition multi_command_spec :=
 DECLARE _multi_command
  WITH i111: int,
       i112: int,
       i121: int,
       i122: int,
       i211: int,
       i212: int,
       i221: int,
       i222: int,
       p: val
  PRE  []
        PROP ()
        LOCAL(var _p t_struct_c p)
        SEP(`(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)), ((i211, i212), (i221, i222)))) p))
  POST [ tvoid ]
            `(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)),
                          ((Int.add i122 (Int.repr 4), Int.add i121 (Int.repr 3)),
                           (Int.add i112 (Int.repr 2), Int.add i111 (Int.repr 1))))) p).

(* The following specs are not in super canonical form. *)
Definition get_spec2 :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  [] 
        PROP  ()
        LOCAL (var _p t_struct_c p)
        SEP   (`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))
  POST [ tint ]
        PROP  ()
        LOCAL (`(eq p) (eval_var _p t_struct_c); 
               `(eq (Vint (snd (snd (snd v))))) (eval_id 1%positive))
        SEP   (`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c)).

Definition get_spec3 :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  [] 
        PROP  ()
        LOCAL ()
        SEP   (`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))
  POST [ tint ]
        PROP  ()
        LOCAL (`(eq (Vint (snd (snd (snd v))))) (eval_id 1%positive))
        SEP   (`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c)).

Definition set_spec2 :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c
  PRE  [ _i OF tint ] 
         PROP () LOCAL(temp _i (Vint i))
        SEP(`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))
  POST [ tvoid ]
        `(data_at Ews t_struct_c (repinj _ (update222 i v))) (eval_var _p t_struct_c).

Definition Vprog : varspecs := (_p, t_struct_c)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::multi_command_spec::nil.

Require Import Timing.
Clear Timing Profile.

Lemma body_multi_command: semax_body Vprog Gprog f_multi_command multi_command_spec.
Proof.
  start_function.
start_timer "Folded".
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "Folded".
  forward.forward. (* return *)
Qed.

Lemma body_multi_command2: semax_body Vprog Gprog f_multi_command multi_command_spec.
Proof.
  start_function.
  unfold_data_at 1%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 5%nat.
  unfold_field_at 7%nat.
start_timer "Unfolded".
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "Unfolded".
  forward.forward. (* return *)
  unfold_data_at 1%nat.
  unfold_field_at 9%nat.
  unfold_field_at 11%nat.
  unfold_field_at 9%nat.
  unfold_field_at 11%nat.
  unfold_field_at 13%nat.
  unfold_field_at 15%nat.
  entailer!.
Qed.

Print Timing Profile.
