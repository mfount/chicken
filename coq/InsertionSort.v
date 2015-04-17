Require Export IsSorted.
(* Require Export Poly. *)

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

(* TODO: fix IsSorted library filepath
   Workaround: copy and paste... *)
Theorem insert_pf : forall (l : list nat), forall (n : nat),
                      (is_sorted_le l = true) ->
                      is_sorted_le (insert n l) = true.
Proof. intros l n H. induction l as [|n' l'].
       Case "l = []". reflexivity.
       Case "l = n'::l'". Abort.

Theorem insertion_sort_pf : forall (l : list nat),
                              is_sorted_le (insertion_sort l) = true.
Proof. intros l. induction l as [|n l'].
       Case "l = []". reflexivity.
       Case "l = n :: l'". Abort.

End InsertionSort.