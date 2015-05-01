Require Export Sf.

(** Disjunction of opposites is always true *)
Lemma orb_x_negx_true : forall (b : bool),
  orb b (negb b) = true.
Proof.
  intros b. destruct b.
  Case "b = true". reflexivity.
  Case "b = false". reflexivity. Qed.

