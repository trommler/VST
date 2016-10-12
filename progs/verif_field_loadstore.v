Require Import floyd.proofauto.
Require Import progs.field_loadstore.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition ToyType := Tstruct _ToyType noattr.
Definition ToyType2 := Tstruct _ToyType2 noattr.

Definition toy_sub_spec :=
 DECLARE _toy_sub
  WITH n: int, m: int, other: list (val * val) , p: val
  PRE  [] 
        PROP  ()
        LOCAL (gvar _p p)
        SEP   (data_at Ews ToyType ((Vint n, Vint m), other) p)
  POST [ tint ]
        PROP() LOCAL()
        SEP(data_at Ews ToyType ((Vint (Int.add m Int.one), Vint m), other) p).

Definition toy_sub2_spec :=
 DECLARE _toy_sub
  WITH n: val, m: val, l0: val, l1: val, l2: val, l3: val, q: val
  PRE  [] 
        PROP  (is_int I32 Signed n; is_int I32 Signed m;
               is_int I32 Signed l2; is_int I32 Signed l3)
        LOCAL (gvar _q q)
        SEP   (data_at Ews ToyType2 ((n, m), (l0 :: l1 :: l2 :: l3 :: nil)) q)
  POST [ tint ]
        PROP() LOCAL()
        SEP(data_at Ews ToyType2 ((l2, l3), (m :: n :: Vint Int.zero :: Vint Int.zero :: nil)) q).

Definition Gprog : funspecs := augment_funspecs prog [ 
  toy_sub_spec; toy_sub2_spec].

Lemma body_toy_sub:  semax_body Vprog Gprog f_toy_sub toy_sub_spec.
Proof.
  unfold toy_sub_spec;
  start_function.
  forward.
  forward.
  forward.
Qed.

Lemma body_toy_sub2:  semax_body Vprog Gprog f_toy_sub2 toy_sub2_spec.
Proof.
  unfold toy_sub2_spec;
  start_function.
  forward.
  forward.
  forward.
    rewrite sem_cast_neutral_int by eauto; simpl.
    unfold upd_Znth, sublist; simpl.
    (* For most applications, program will load/store the nth element  *)
    (* of an array, thus we keep upd_Znth and Znth folded in spec. So, *)
    (* we unfold them manually here.                                   *)
  forward.
    rewrite sem_cast_neutral_int by eauto; simpl.
    unfold upd_Znth, sublist; simpl.
  forward.
    unfold Znth; simpl.
  forward.
    unfold Znth; simpl.
  forward.
    rewrite sem_cast_neutral_int by eauto; simpl.
  forward.
    rewrite sem_cast_neutral_int by eauto; simpl.
  forward.
    unfold upd_Znth, sublist; simpl.
  forward.
    unfold upd_Znth, sublist; simpl.
  forward.
Qed.
