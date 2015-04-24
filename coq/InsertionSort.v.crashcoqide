Require Export Lists.

Module InsertionSort.

Eval compute in natlist.

Fixpoint insert (x : nat) (l:natlist) : natlist :=
  match l with
    | nil => [x]
    | h :: t => if x < h then x :: l
                else h :: (insert x t)
  end.

end.