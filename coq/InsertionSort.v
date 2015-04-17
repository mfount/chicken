Require Export Poly.

Module InsertionSort.

Fixpoint insert (x : nat) (l:(list nat)) : (list nat) :=
  match l with
    | [] => [x]
    | h :: t =>
      match (blt_nat x h) with
        | true => x :: l
        | false => h :: (insert x t)
      end
  end.

Example test_insert1: insert 2 [1;3;4] = [1;2;3;4].
Proof. reflexivity. Qed.

Example test_insert2: insert 3 [10;20;25] = [3;10;20;25].
Proof. reflexivity. Qed.

Example test_insert3: insert 4 [3;4;4;4;5] = [3;4;4;4;4;5].
Proof. reflexivity. Qed.

Fixpoint insertion_sort (l:(list nat)) : (list nat) :=
  match l with
    | [] => []
    | h :: t => insert h (insertion_sort t)
  end.

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

Theorem insertion_sort_pf : forall (l : list nat),
                              is_sorted_le (insertion_sort l) = true.
Proof.
  Admitted.

End InsertionSort.