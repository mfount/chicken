open Basics
open Datatypes
open Lists

(** val insert : nat -> natlist -> natlist **)

let rec insert v = function
| Coq_nil -> Coq_cons (v, Coq_nil)
| Coq_cons (h, t) ->
  (match ble_nat v h with
   | Basics.Coq_true -> Coq_cons (v, (Coq_cons (h, t)))
   | Basics.Coq_false -> Coq_cons (h, (insert v t)))

(** val insertion_sort : natlist -> natlist **)

let rec insertion_sort = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) -> insert h (insertion_sort t)

