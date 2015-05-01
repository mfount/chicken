
(** Sorting basics: 
    Here we introduce predicates that test whether a list
    is sorted, and whether one list is a permutation of another.
    We use these two properties to define what it means for a 
    sorting algorithm to be correct: it has to produce a sorted
    list which is a permutation of the original list *)

(** Sortedness predicate: compare first two elements, and recurse *)
Fixpoint is_sorted (l : natlist) : bool :=
  match l with
  | [] => true
  | h :: t => match t with 
              | [] => true
              | h1 :: t1 => andb (ble_nat h h1) (is_sorted t)
  end
  end.

(** Permutation predicate: every natural number appears the
    same number of times in the two lists *)
Definition is_permutation (l l' : natlist) : Prop :=
  forall (v : nat), (count v l) = (count v l').

(** Helpful properties of is_sorted *)

(** Appending an element smaller than the head to a sorted list
    preserves sortedness *)
Lemma sorted_from_tail : forall (l : natlist) (v h : nat),
  andb (ble_nat v h) (is_sorted (h :: l)) = true -> is_sorted (v :: h :: l) = true.
Proof.
  intros l v h. intros H. simpl in H. simpl. apply H. Qed.

(** For a sorted list, the tail is sorted *)      
Lemma sorted_implies_subsorted : forall (l : natlist) (v : nat),
  is_sorted (v :: l) = true -> is_sorted l = true.
Proof.
  intros l v. intros H. simpl.
  destruct l as [ | h t].
  Case "l = []". simpl. reflexivity.
  Case "l = h t".
    simpl in H.  apply andb_true_elim2 in H.
    destruct t as [ | h' t'].
    SCase "t = []". simpl. reflexivity.
    SCase "t = h' t'". apply sorted_from_tail. apply H. Qed.  

(** Predicate that tests whether an element is less than or equal to
    all elements in a given list. This will be useful later on
    when we prove correctness of insertion sort, so we'll prove
    some properties of that predicate now. *)
Fixpoint leq_than_all (v : nat) (l : natlist) : bool :=
  match l with
  | [] => true
  | h :: t => andb (ble_nat v h) (leq_than_all v t)
  end.

(** For a sorted list, the head is <= all elements of the tail *)
Lemma sorted_implies_head_leq_than_all : forall (v : nat) (l : natlist),
  is_sorted (v :: l) = true -> leq_than_all v l = true.
Proof.
  intros v l. intros H. induction l as [ | h t].
  (* we induct on the list l: the rest is piecing 
     the inequalities in the right way and doing casework
     unfolding is_sorted and leq_than_all. The key point is that
     the two functions are defined in terms of the same recursion. *)
  Case "l = []". simpl. reflexivity.
  Case "l = h :: t". simpl.
    assert (Lemma1 : is_sorted (v :: h :: t) = true).
      SCase "Proof of Lemma 1". apply H.
    assert (Lemma2 : ble_nat v h = true).
      SCase "Proof of Lemma 2". simpl in Lemma1. apply andb_true_elim1 in Lemma1.
        apply Lemma1.
  rewrite Lemma2.
  assert (Lemma3 : is_sorted t = true).
    SCase "Proof of Lemma 3". apply sorted_implies_subsorted in H.
      apply sorted_implies_subsorted in H. apply H.
  destruct t as [ | h' t'].
  SCase "t = []". simpl. reflexivity.
  SCase "t = h' :: t'". 
    apply sorted_implies_subsorted in H. simpl in H. apply andb_true_elim1 in H.
  assert (Lemma4 : ble_nat v h' = true).
    SSCase "Proof of Lemma 4".
      apply ble_nat_transitive with (v := h). apply Lemma2. apply H.
  assert (Lemma5 : is_sorted (v :: h' :: t') = true).
    SSCase "Proof of Lemma 5".
      apply sorted_from_tail. rewrite Lemma4. rewrite Lemma3. simpl. reflexivity.
  assert (Lemma6 : leq_than_all v (h' :: t') = true).
    SSCase "Proof of Lemma 6".
      apply IHt. apply Lemma5.
  rewrite Lemma6. simpl. reflexivity. Qed.
 

(** Helpful properties of is_permutation: among other things, here we show
    that the permutation relation we've defined is an equivalence
    relation: that is, it is reflexive, symmetric and transitive. *)

Theorem is_permutation_reflexive : forall (l : natlist),
  is_permutation l l.
Proof.
  intros l. unfold is_permutation. reflexivity. Qed.

Theorem is_permutation_symmetric : forall (l l' : natlist),
  is_permutation l l' -> is_permutation l' l.
Proof.
  intros l l'. intros H. unfold is_permutation in H. symmetry in H.
  unfold is_permutation. apply H. Qed.

Theorem is_permutation_transitive : forall (l l' l'' : natlist),
  is_permutation l l' -> is_permutation l' l'' -> is_permutation l l''.
Proof.
  intros l l' l''. intros H1. intros H2. unfold is_permutation in H1, H2.
  unfold is_permutation. intros v.
  (* the rest of the proof is just an application of transitivity of
     equality. *)
  assert (Lemma1 : count v l = count v l').
    Case "Proof of Lemma 1". apply H1.
  assert (Lemma2 : count v l' = count v l'').
    Case "Proof of Lemma 2". apply H2.
  apply trans_eq with (m := count v l').
  rewrite Lemma1. reflexivity. rewrite Lemma2. reflexivity. Qed.

(** If two lists can be broken into parts that are permutations of one 
    another, the lists are permutations of one another *)
Theorem is_permutation_append : forall (x x' y y' : natlist),
  is_permutation x y -> is_permutation x' y' -> is_permutation (x ++ x') (y ++ y').
Proof.
  intros x x' y y'. intros H. intros H'. 
  unfold is_permutation. 
  intros v. 
  (* at this point, the theorem is a simple consequence of 
     the fact that count distributes over append as addition *)
  rewrite append_add_counts. rewrite append_add_counts. 
  unfold is_permutation in H, H'. rewrite H. rewrite H'. reflexivity. Qed.

(** For a list of length 2, transpositing the elements is a 
    permutation. *)
Theorem is_permutation_transposition : forall (v h : nat),
  is_permutation (v :: [h]) (h :: [v]).
Proof.
  intros v h. unfold is_permutation. intros v0.
  (* this is just a lot of casework *)
  destruct (beq_nat v0 v) eqn:Casev.
  destruct (beq_nat v0 h) eqn:Caseh.
  Case "v0 = v, v0 = h". simpl. rewrite Casev. rewrite Caseh. reflexivity.
  Case "v0 = v, v0 != h". simpl. rewrite Casev. rewrite Caseh. reflexivity.
  destruct (beq_nat v0 h) eqn:Caseh.
  Case "v0 != v, v0 = h". simpl. rewrite Casev. rewrite Caseh. reflexivity.
  Case "v0 != v, v0 != h". simpl. rewrite Casev. rewrite Caseh. reflexivity. Qed.
  
(** Swapping the first two elements in a list is a permutation *)
 Theorem is_permutation_swap_first : forall (l : natlist) (v h : nat),
  is_permutation (v :: h :: l) (h :: v :: l).
Proof.
  intros l v h.
  (* the goal follows readily by combining is_permutation_transposition
     with is_permutation_append *)
  assert (Lemma1 : is_permutation (v :: [h]) (h :: [v])).
    Case "Proof of Lemma 1". apply is_permutation_transposition.
  apply is_permutation_append with (x := (v :: [h]))
                                   (x' := l) (y := (h :: [v])) (y' := l).
  apply is_permutation_transposition. apply is_permutation_reflexive. Qed.
    
(** Prepending the same element to two lists that are permutations
    of each other preserves the permutation relation. *)
Theorem is_permutation_same_head : forall (v : nat) (l l' : natlist),
  is_permutation l l' -> is_permutation (v :: l) (v :: l').
Proof.
  intros v l l'. intros H.
  (* this easily follows by is_permutation_append *)
  apply is_permutation_append with (x := [v]) (x' := l) (y := [v]) (y' := l').
  apply is_permutation_reflexive. apply H. Qed. 
