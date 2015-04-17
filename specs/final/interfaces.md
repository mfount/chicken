Along the way, we use the following placeholder for proofs we will do later:

`Admitted.`, which is defined with:

`Definition admit {T: Type} : T.  Admitted.`

__Data structures and sorts__

booleans:
- TODO: there is code for this in `chicken/coq/Basics.v`
- this includes the proofs of axioms and binary operations

nats:
- TODO: there is code for this in `chicken/coq/Basics.v` and `chicken/coq/Induction.v`,
  which includes `ble_nat` (`<=` for nats) and its proof (likewise for other comparison
  functions, which we can pass into sorts).
- proofs of axioms and comparison functions are also included.

polymorphic lists:
- we will be sorting (`list nat`) or, informally, natlists throughout this project.
- we will use lists of lists, (`list (list nat)`) or, informally natlist lists in 
  simsort.
- TODO: definitions of polymorphic lists are found in `chicken/coq/Poly.v`
- TODO: check for requirements/ dependencies from `chicken/coq/Lists.v`, which
  defines natlists.
- proofs of axioms are also included.

`is_sorted_le` (and/ or more general `is_sorted` functions with passed-in comparison
function:
- checks if a list is sorted in ascending order.
- will be involved in all the sorting algorithm proofs.
- proof is split into 3 lemmas (see `chicken/coq/IsSorted.v`)
   Informally:
   * we check that if `l` is a sorted list and `n` is `<=` the head of l then `n::l`
     is again sorted.
   * we check that if `l` is a list that is not sorted, `n::l` is again not sorted.
   * we check that if `n` is not `<=` the head of `l` then `n::l` is not sorted.
   * these lemmas allow us to do an induction on `is_sorted_le`
- `IsSorted` (library) will be required by all other sorts

_Lemmas within proofs will take the form of proving sub-methods, then proving
the correctness of the entire procedure using these sub-method-proofs as lemmas._
_For an example, see_ `chicken/coq/InsertionSort.v`

Insertion sort:
- Procedure (`insert n t`): 
	takes input an list `t` where the last `n-1` elements are sorted
	returns list `t'` where last `n` elts are sorted, by inserting 1st element 

- Insertion sort:
	takes input a list `t_1`
	run (`insert 0 t_{n-1}`), (`insert 1 t_{n-2}`), ..., (`insert {n-1} t_{0}`)
	where `t_i` is the result of (`insertion (n-i) t_{i-1}`)
	
Proof: for the proof we prove insert and then InsertionSort on top of that. We will need IsSorted, which we prove elsewhere.
See `chicken/coq/InsertionSort.v`.

Mergesort:
- Procedure (`merge t s`): 
	takes input lists `t`, `s` that are sorted
	returns an array that is `s` and `t` merged together (and sorted)

- Merge sort: 
	takes input a list `t`
	calls itself recursively on each half of the list, then calls `merge`.

Proof: will take a similar form to `insertion_sort` proof. Prove `merge`, then prove `merge_sort` on top of that. We will need IsSorted, which we prove elsewhere.

Heapsort:
- Procedure (`heapify t`):
	takes input a list `t`
	returns a heap data structure with elements the element of the list

- Procedure (`heapsort_step h t`):
	takes as input a heap (a min-heap) `h` and a list `t`
	returns a new heap `h'` and new list `t'` where we moved the min element
	from the heap `h` to the beginning of `t`.

- Heap sort:
	takes as input a list `t`
	runs `heapify` on `t`
	then runs `heapsort_step` until the heap is empty.



Simple timsort (`simsort`):
- Procedure (runs `t`):
	takes as input a list `t`
	returns: consider a permutation of `t` where consecutive runs have 
        length at least 64 (or some other constant, we'll see)
	then (runs `t`) returns a list of these runs

	Uses either insertion sort (original timsort) or heapsort (our 
	modification) to sort the runs when necessary

- Procedure (`merge_runs T`)
	takes as input a list of lists `T`, as the output of (`runs t`). 
	returns a list of lists that represents the result of merging the runs following the timsort heuristic:
	the runs are put on a stack, and then if X, Y, Z are the lengths of the top 3 runs, the algorithm merges the runs
	until the invariant X > Y + Z, Y > Z is satisfied.
	
	stack can be done as a list or using dictionary type which is defined in `chicken/coq/Poly.v`.

