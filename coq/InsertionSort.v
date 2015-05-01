Require Export Sf.

(** Insertion sort : algorithm.
    Here we define the implementation of insertion sort
    we'll be using. *)

(** This is the insertion sort algorithm: sort the tail
    recursively and insert the head. *)
Fixpoint insertion_sort (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.


(** Insert an element in its place in a sorted list.
   This is the main subroutine for insertion sort. *)
Fixpoint insert (v : nat) (l : natlist) : natlist :=
  match l with
  (* keep in mind that we're assuming l is sorted for this function
     to make sense *)
  | [] => [v]
  | h :: t => match ble_nat v h with
              | true => v :: h :: t
              | false => h :: (insert v t)
              end
  end.


