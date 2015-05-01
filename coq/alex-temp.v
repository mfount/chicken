Require Export Basics.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Theorem minus_help : forall (x y : nat),
  ble_nat x y = true -> x + (minus y x) = y.
Proof.
  intros x y. intros H.
  induction x as [ | x'].
  simpl. admit.
  simpl. admit.

Theorem ble_nat1 : forall (x y : nat),
  ble_nat (S x) y = true -> ble_nat x y = true.
Proof.
  intros x y. intros H.
  induction y as [ | y'].
  inversion H.

Theorem ble_nat2 : forall (x : nat),
  ble_nat x (S x) = true.
Proof.
  intros x.
  induction x as [ | x'].
  simpl. reflexivity.
  simpl. apply IHx'. Qed.

Theorem ble_nat3 : forall (x y : nat),
  ble_nat x (x + y) = true.
Proof.
  intros x y.
  induction x as [ | x'].
  simpl. reflexivity.
  simpl. apply IHx'. Qed.
  


Theorem ble_nat_alt : forall (x y : nat),
  ble_nat x y = true -> exists (z : nat), x + z = y.
Proof.
  intros x y.
  intros H.
  assert (Lemma1 : x + (minus y x) = y).
  
