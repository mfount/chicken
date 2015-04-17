Require Export Poly.

Module IsSorted.

Fixpoint is_sorted_le (l : list nat) : bool :=
  match l with
    | h1 :: t1 =>
      match t1 with
        | h2 :: t2 => andb (ble_nat h1 h2) (is_sorted_le t2)
        | [] => true
      end
    | [] => true
  end.

Definition nat_le_before n l :=
  match hd_opt l with
    | Some m => ble_nat n m
    | None => true
  end.


Theorem is_sorted_part1 : forall (l : list nat),
                          forall (n : nat),
                            (nat_le_before n l = true) ->
                            (is_sorted_le l = true) ->
                            (is_sorted_le (n :: l) = true).
Proof.
  Admitted.

Theorem is_sorted_part2 : forall (l : list nat),
                          forall (n : nat),
                            (nat_le_before n l = false) ->
                            is_sorted_le (n :: l) = false.
Proof.
  Admitted.

Theorem is_sorted_part3 : forall (l : list nat),
                          forall (n : nat),
                            (is_sorted_le l = false) ->
                            is_sorted_le (n :: l) = false.
Proof.
  Admitted.

End IsSorted.