Require Export Sf.

(** Equality is transitive *)
Theorem trans_eq : forall (n m o : nat),
  n = m -> m = o -> n = o.
Proof.
  intros n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Helpful properties of ble_nat:
    Here we assume some basic properties of the less than 
    or equal relation.*)



Lemma ble_nat_helper : forall (u v : nat),
  ble_nat (S u) v = true -> ble_nat u v = true.
Proof.
  intros u v.
  intros H.
  induction v as [ | v'].
  simpl in H.
  inversion H.
  simpl in H.
  Admitted.

Theorem ble_nat_transitive : forall (u v w : nat),
  ble_nat u v = true -> ble_nat v w = true -> ble_nat u w = true.
Proof.
  intros u v w.
  intros H.
  intros H'.
  induction v as [ | v'].
  destruct u as [ | u'].
  reflexivity.
  simpl in H.
  inversion H.
  Admitted.


Lemma ble_nat_anticomm : forall (u v : nat),
  (ble_nat u v) = false -> (ble_nat v u) = true.
Proof.
  intros u v.
  intros H.
  induction u as [ | u'].
  Case "u = 0".
  simpl. simpl in H.
  destruct (ble_nat v 0).
  reflexivity.
  rewrite H. reflexivity. 
  induction v as [ | v'].
  simpl. reflexivity.
  simpl. simpl in IHu'.
  Admitted.

Lemma ble_nat_helper1 : forall (u v w: nat),
  ble_nat u v = false -> ble_nat u w = true -> beq_nat v w = false.
Proof.
  intros u v w. intros H. intros H'.
  Admitted.
