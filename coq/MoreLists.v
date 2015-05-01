Require Export Sf.

(** Count distributes over append as addition *)
Theorem append_add_counts : forall (x y : natlist) (v : nat),
  count v (x ++ y) = count v x + count v y.
Proof.
  intros x y v. induction x as [ | h t].
  Case "x = []". simpl. reflexivity.
  Case "x = h :: t". destruct (beq_nat v h) eqn:Casev.
    SCase "v = h". simpl. rewrite Casev. rewrite IHt. simpl. reflexivity.
    SCase "v != h". simpl. rewrite Casev. rewrite IHt. reflexivity. Qed.

(** Helper for later: If v is not present in a list l, it is not
    present in the tail of l *)
Lemma count_helper : forall (v h : nat) (l : natlist),
  count v (h :: l) = 0 -> count v l = 0.
Proof.
  intros v h l. intros H. simpl in H.
  destruct (beq_nat v h) eqn:Casevh.
  Case "v <= h". inversion H.
  Case "v > h". apply H. Qed.
