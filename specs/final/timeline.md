As of Friday 17 April at 5pm, we have exactly two weeks to finish our project.

__Week One__
- isolate axiom definitions from the first 4 chapters of Software Foundations that we will use. Get them working as a set of      libraries that can be Required.
- as a group, do all of these exercises (proof of the consistency of the axiom definitions that we need). As individuals, learn   the contents of the first 5 chapters.
- complete proofs of `is_sorted_le` in `chicken/coq/IsSorted.v`. Complete proofs of `insertion_sort` in 
  `chicken/coq/InsertSort.v`.
- do the same for `merge_sort`
- get an implementation of heaps working (in line with the pseudo-code signature given in the final spec) and prove half of the   operations.

__Week Two__
- complete proof of the correctness of operations of heap.
- implement heap_sort and prove it. Easy after the work we have done for heaps.
- combine merge and insert into `sim_sort`.
- export to ocaml and check on the list that breaks the java implementation.
- combine merge and heap into `our_sim_sort`.
- prove `sim_sort` itself.
