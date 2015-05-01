
Require Export InsertionSort.
Require Export SortingBasics.



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
