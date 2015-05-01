Require Export Lists.
Require Export InsertionSortAlgorithm.

(** Sorting stuff **)

(** Preliminary lemmas:
    Here we prove some general facts that will be useful
    later on. *)


(** Count distributes over append as addition *)
Theorem append_add_counts : forall (x y : natlist) (v : nat),
  count v (x ++ y) = count v x + count v y.
Proof.
  intros x y v. induction x as [ | h t].
  Case "x = []". simpl. reflexivity.
  Case "x = h :: t". destruct (beq_nat v h) eqn:Casev.
    SCase "v = h". simpl. rewrite Casev. rewrite IHt. simpl. reflexivity.
    SCase "v != h". simpl. rewrite Casev. rewrite IHt. reflexivity. Qed.

(** Helper for later: If v is not present in a list l, it is not
    present in the tail of l *)
Lemma count_helper : forall (v h : nat) (l : natlist),
  count v (h :: l) = 0 -> count v l = 0.
Proof.
  intros v h l. intros H. simpl in H.
  destruct (beq_nat v h) eqn:Casevh.
  Case "v <= h". inversion H.
  Case "v > h". apply H. Qed.

(** Disjunction of opposites is always true *)
Lemma orb_x_negx_true : forall (b : bool),
  orb b (negb b) = true.
Proof.
  intros b. destruct b.
  Case "b = true". reflexivity.
  Case "b = false". reflexivity. Qed.

(** Equality is transitive *)
Theorem trans_eq : forall (n m o : nat),
  n = m -> m = o -> n = o.
Proof.
  intros n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Helpful properties of ble_nat:
    Here we assume some basic properties of the less than 
    or equal relation.*)

Theorem minus_help : forall (x y : nat),
  ble_nat x y = true -> x + (minus y x) = y.
Proof.
  intros x y. intros H.
  induction x as [ | x'].
  simpl. admit.
  simpl. admit. Qed.

Theorem ble_nat3 : forall (x y : nat),
  ble_nat x (x + y) = true.
Proof.
  intros x y.
  induction x as [ | x'].
  simpl. reflexivity.
  simpl. apply IHx'. Qed.

Theorem ble_nat_alt1 : forall (x y : nat),
  (exists (z : nat), x + z = y) -> ble_nat x y = true.
Proof.
  intros x y H.
  destruct H as [z G].
  assert (Lemma1 : ble_nat x (x + z) = true).
    apply ble_nat3.
  rewrite G in Lemma1.
  apply Lemma1. Qed.
  
Theorem ble_nat_alt2 : forall (x y : nat),
  ble_nat x y = true -> exists (z : nat), x + z = y.
Proof.
  intros x y.
  intros H.
  assert (Lemma1 : x + (minus y x) = y).
    apply minus_help. apply H.
  exists (minus y x). apply Lemma1. Qed.

Definition ble_nat_alt (x y : nat) : Prop :=
  exists (z : nat), x + z = y.

(*
Lemma ble_nat_helper : forall (u v : nat),
  ble_nat (S u) v = true -> ble_nat u v = true.
Proof.
  intros u v.
  intros H.
  induction v as [ | v'].
  simpl in H.
  inversion H.
  simpl in H.
  Admitted. *)

Theorem ble_nat_transitive : forall (u v w : nat),
  ble_nat u v = true -> ble_nat v w = true -> ble_nat u w = true.
Proof.
  intros u v w.
  intros H.
  intros H'.
  apply ble_nat_alt2 in H.
  apply ble_nat_alt2 in H'.
  apply ble_nat_alt1.
  destruct H as [z H].
  destruct H' as [z' H'].
  rewrite <- H in H'.
  exists (z + z').
  rewrite plus_assoc.
  apply H'. Qed.


Lemma ble_nat_anticomm : forall (u v : nat),
  (ble_nat u v) = false -> (ble_nat v u) = true.
Proof.
  Admitted.
(*
  intros u v.
  intros H.
  induction u as [ | u'].
  simpl in H. inversion H.
  destruct (beq_nat u' v) eqn:Caseu'v.
  assert (Lemma1 : ble_nat (S u') v = false).
  *)
  

Lemma ble_nat_helper1 : forall (u v w: nat),
  ble_nat u v = false -> ble_nat u w = true -> beq_nat v w = false.
Proof.
  Admitted.


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



(** Insertion sort : correctness.
    Here we show insertion sort is correct, that is, for every list 
    l, (insertion_sort l) is a sorted list and a permutation of l. *)

(** Permutation correctness: here we show that for every list l,
    (insertion_sort l) is a permutation of l. *)

(* First, we show that the insert subroutine gives a permutation
   of what we would get if we just inserted in the first position. *)
Theorem insert_is_permutation : forall (v : nat) (l : natlist),
  is_permutation (v :: l) (insert v l).
Proof.
  intros v l. induction l as [ | h t].
  Case "l = []". simpl. apply is_permutation_reflexive.
  Case "l = h :: t".
  destruct (ble_nat v h) eqn:Case1.
    SCase "v <= h".
      simpl. rewrite Case1. apply is_permutation_reflexive.
    SCase "v > h".
      simpl. rewrite -> Case1.
      assert (Lemma1 : is_permutation (v :: h :: t) (h :: v :: t)).
        SSCase "Proof of Lemma 1". apply is_permutation_swap_first.
      apply is_permutation_transitive with (l' := (h :: v :: t)).
        apply Lemma1. 
        apply is_permutation_same_head with (v := h) (l := (v :: t)) 
                                                     (l' := (insert v t)).
        apply IHt. Qed.

(* Now it's easy to show the main lemma *)
Theorem insertion_sort_is_permutation : forall (l : natlist),
  is_permutation l (insertion_sort l).
Proof.
  intros l. induction l as [ | h t].
  Case "l = []".
  simpl. apply is_permutation_reflexive.
  Case "l = h :: t".
  simpl.
  assert (Lemma1 : is_permutation (insert h (insertion_sort t)) (h :: (insertion_sort t))).
  SCase "Proof of Lemma 1". apply is_permutation_symmetric. apply insert_is_permutation.
  assert (Lemma2 : is_permutation (h :: t) (h :: (insertion_sort t))).
  SCase "Proof of Lemma 2". apply is_permutation_same_head. apply IHt.
  apply is_permutation_symmetric in Lemma1.
  apply is_permutation_transitive with (l' := (h :: insertion_sort t)).
  apply Lemma2.
  apply Lemma1. Qed.
  

(* Sortedness correctness *)

Theorem leq_than_all_alternative_def : forall (v : nat) (l : natlist),
  (leq_than_all v l) = true -> (forall (n : nat), (ble_nat v n) = false -> count n l = 0).
Proof.
  intros v l. intros H. intros n. intros H'. induction l as [ | h t].
  Case "l = []". simpl. reflexivity.
  Case "l = h :: t". simpl.
    assert (Helper1 : leq_than_all v (h :: t) = true).
      SCase "Proof of Helper 1". rewrite H. reflexivity.
    assert (Helper2 : leq_than_all v (h :: t) = true).
      SCase "Proof of Helper 1". rewrite H. reflexivity.
    assert (Lemma1: leq_than_all v t = true).
      SCase "Proof of Lemma 1". simpl in Helper1. apply andb_true_elim2 in Helper1.
        apply Helper1.
    rewrite Lemma1 in IHt. rewrite IHt.
    assert (Lemma2: ble_nat v h = true).
      SCase "Proof of Lemma 2". simpl in Helper2. apply andb_true_elim1 in Helper2.
        apply Helper2.
    assert (Lemma3: beq_nat n h = false).
      SCase "Proof of Lemma 3". apply ble_nat_helper1 with (u := v).
        apply H'. apply Lemma2.
  rewrite Lemma3. reflexivity. reflexivity. Qed.    
  
Theorem leq_than_all_alternative_def1 : forall (v : nat) (l : natlist),
  (forall (n : nat), (ble_nat v n) = false -> count n l = 0) -> (leq_than_all v l) = true.
Proof. 
  intros v l. intros H. induction l as [ | h t].
  Case "l = []". simpl. reflexivity.
  Case "l = h :: t". simpl.
  assert (Lemma1 : forall (n : nat), count n (h :: t) = 0 -> count n t = 0).
    SCase "Proof of Lemma 1". intros n. apply count_helper.
  assert (Lemma2 : forall n : nat, ble_nat v n = false -> count n t = 0).
    SCase "Proof of Lemma 2". intros n H'. apply Lemma1. apply H. apply H'.
  assert (Lemma3 : leq_than_all v t = true).
    SCase "Proof of Lemma 3". apply IHt. apply Lemma2.
  rewrite Lemma3. destruct (ble_nat v h) eqn:Casevh.
  SCase "v <= h". simpl. reflexivity.
  SCase "v > h".
  assert (Lemma4 : count h (h :: t) = 0).
    SSCase "Proof of Lemma 4". apply H. apply Casevh.
  simpl in Lemma4. rewrite <- beq_nat_refl in Lemma4. inversion Lemma4. Qed.

Theorem leq_than_all_invariant_permutation : forall (v : nat) (l l' : natlist),
  is_permutation l l' -> (leq_than_all v l) = true -> (leq_than_all v l') = true.
Proof. 
  intros v l l'. intros H. intros H'. unfold is_permutation in H.
  assert (Lemma1 : forall (n : nat), (ble_nat v n) = false -> count n l = 0). 
    Case "Proof of Lemma 1". apply leq_than_all_alternative_def. apply H'.
  assert (Lemma2 : forall (n : nat), (ble_nat v n) = false -> count n l' = 0).
    Case "Proof of Lemma 2". intros n.
      assert (Lemma21 : count n l = count n l'). apply H.
      rewrite <- Lemma21. apply Lemma1.
  apply leq_than_all_alternative_def1. apply Lemma2. Qed.
  
Theorem insertion_helper : forall (l : natlist) (v h: nat),
  leq_than_all v l = true -> ble_nat v h = true -> leq_than_all v (insert h l) = true.
Proof.
  intros l v h. intros H. intros H'.
  assert (Lemma1 : leq_than_all v (h :: l) = true).
    Case "Proof of Lemma 1". simpl. rewrite H. rewrite H'. simpl. reflexivity.
  assert (Lemma2 : is_permutation (h :: l) (insert h l)).
    Case "Proof of Lemma 2". apply insert_is_permutation.
  apply leq_than_all_invariant_permutation with (l := (h :: l)).
  apply Lemma2. apply Lemma1. Qed.

     
Theorem insert_preserves_sortedness : forall (v : nat) (l : natlist),
  is_sorted l = true -> is_sorted (insert v l) = true.
Proof.
  intros v l. intros H. induction l as [ | h t].
  Case "l = []". simpl. reflexivity.
  Case "l = h :: t". simpl.
    assert (Lemma1: andb (ble_nat v h) (is_sorted (h :: t)) = true  
                    -> is_sorted (v :: h :: t) = true).
      SCase "Proof of Lemma 1". apply sorted_from_tail.
    assert (Lemma2 : is_sorted (h :: t) = true).
      SCase "Proof of Lemma 2". rewrite H. reflexivity.
    assert (Lemma3: is_sorted t = true).
      SCase "Proof of Lemma 3".
        apply sorted_implies_subsorted in Lemma2. rewrite -> Lemma2. reflexivity.
    assert (Lemma4: is_sorted (insert v t) = true).
      SCase "Proof of Lemma 4". rewrite Lemma3 in IHt. apply IHt. reflexivity.
  destruct (insert v t) as [ | h' t'] eqn:Caseinsert.
    SCase "insert v t = []". destruct (ble_nat v h) eqn:Casevh. 
      rewrite H in Lemma1. apply Lemma1. simpl. reflexivity. simpl. reflexivity.
    SCase "insert v t = h' :: t'". destruct (ble_nat v h) eqn:Casevh.
      SSCase "v <= h". rewrite H in Lemma1. apply Lemma1. simpl. reflexivity.
      SSCase "v > h".
        assert (Lemma5 : ble_nat h v = true).
          SSSCase "Proof of Lemma 5". apply ble_nat_anticomm. apply Casevh.
        assert (Lemma6 : leq_than_all h t = true).
          SSSCase "Proof of Lemma 6".
            apply sorted_implies_head_leq_than_all. apply H.
        assert (Lemma7 : leq_than_all h (insert v t) = true).
          SSSCase "Proof of Lemma 7". 
            apply insertion_helper. apply Lemma6. apply Lemma5.
        assert (Lemma8 : ble_nat h h' = true).
          SSSCase "Proof of Lemma 8".
            rewrite Caseinsert in Lemma7. simpl in Lemma7. 
            apply andb_true_elim1 in Lemma7. apply Lemma7.
      apply sorted_from_tail. rewrite Lemma8. rewrite Lemma4. simpl. reflexivity. Qed.
      

Theorem insertion_sort_correct : forall (l : natlist),
  is_sorted (insertion_sort l) = true.
Proof.
  intros l. induction l as [ | h t].
  Case "l = []". simpl. reflexivity.
  Case "l = h :: t". simpl.
    apply insert_preserves_sortedness with (v:=h) in IHt.
    rewrite IHt. reflexivity. Qed.
  