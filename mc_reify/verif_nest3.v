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

Definition multi_command_s_spec :=
 DECLARE _multi_command_s
  WITH p0: val,
       p1: val,
       p2: val,
       p3: val,
       p4: val,
       p5: val,
       p6: val,
       p7: val
  PRE  []
        PROP ()
        LOCAL(var _p0 t_struct_c p0;
              var _p1 t_struct_c p1;
              var _p2 t_struct_c p2;
              var _p3 t_struct_c p3;
              var _p4 t_struct_c p4;
              var _p5 t_struct_c p5;
              var _p6 t_struct_c p6;
              var _p7 t_struct_c p7)
        SEP(`(data_at Ews tint (Vint (Int.repr 0)) p0);
            `(data_at Ews tint (Vint (Int.repr 0)) p1);
            `(data_at Ews tint (Vint (Int.repr 0)) p2);
            `(data_at Ews tint (Vint (Int.repr 0)) p3);
            `(data_at Ews tint (Vint (Int.repr 0)) p4);
            `(data_at Ews tint (Vint (Int.repr 0)) p5);
            `(data_at Ews tint (Vint (Int.repr 0)) p6);
            `(data_at Ews tint (Vint (Int.repr 0)) p7))
  POST [ tvoid ]
        PROP ()
        LOCAL(var _p0 t_struct_c p0;
              var _p1 t_struct_c p1;
              var _p2 t_struct_c p2;
              var _p3 t_struct_c p3;
              var _p4 t_struct_c p4;
              var _p5 t_struct_c p5;
              var _p6 t_struct_c p6;
              var _p7 t_struct_c p7)
        SEP(`(data_at Ews tint (Vint (Int.repr 0)) p0);
            `(data_at Ews tint (Vint (Int.repr 0)) p1);
            `(data_at Ews tint (Vint (Int.repr 0)) p2);
            `(data_at Ews tint (Vint (Int.repr 0)) p3);
            `(data_at Ews tint (Vint (Int.repr 4)) p4);
            `(data_at Ews tint (Vint (Int.repr 3)) p5);
            `(data_at Ews tint (Vint (Int.repr 2)) p6);
            `(data_at Ews tint (Vint (Int.repr 1)) p7)).

Definition Vprog : varspecs := (_p, t_struct_c)::nil.

Definition Gprog : funspecs := 
    multi_command_s_spec::multi_command_spec::nil.

Require Import Timing.
Clear Timing Profile.

Lemma body_multi_command_s: semax_body Vprog Gprog f_multi_command_s multi_command_s_spec.
Proof.
  start_function.
start_timer "Folded".
eapply semax_seq'.
eapply semax_seq'.
+
hoist_later_in_pre.

eapply sc_set_load_store.semax_SC_field_load with (e1 := (Evar _p0 tint)) (efs := nil) (tts := nil)
(gfs := nil) (gfs0 := nil) (gfs1 := nil) (e := Struct_env) (t_root := tint) (n := 0%nat) (lr := LLLL).
reflexivity.
reflexivity.
reflexivity.
Locate legal_nested_efield.
Print compute_lr.
reflexivity.





  forward.forward. [entailer! | solve_legal_nested_field_in_entailment' |].
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
