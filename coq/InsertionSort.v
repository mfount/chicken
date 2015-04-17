Require Export Lists.

Module InsertionSort.

Fixpoint insert (x : nat) (l:natlist) :=
  match l with
    | nil => [x]
    | h :: t => if x < h then x :: l
                else h :: (insert x t)
                       end.

end.