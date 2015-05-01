open Basics
open Datatypes
open Peano

type natprod =
| Coq_pair of nat * nat

val natprod_rect : (nat -> nat -> 'a1) -> natprod -> 'a1

val natprod_rec : (nat -> nat -> 'a1) -> natprod -> 'a1

val fst : natprod -> nat

val snd : natprod -> nat

val fst' : natprod -> nat

val snd' : natprod -> nat

val swap_pair : natprod -> natprod

type natlist =
| Coq_nil
| Coq_cons of nat * natlist

val natlist_rect : 'a1 -> (nat -> natlist -> 'a1 -> 'a1) -> natlist -> 'a1

val natlist_rec : 'a1 -> (nat -> natlist -> 'a1 -> 'a1) -> natlist -> 'a1

val mylist : natlist

val mylist1 : natlist

val mylist2 : natlist

val mylist3 : natlist

val repeat : nat -> nat -> natlist

val length : natlist -> nat

val app : natlist -> natlist -> natlist

val hd : nat -> natlist -> nat

val tl : natlist -> natlist

val nonzeros : natlist -> natlist

val oddmembers : natlist -> natlist

val countoddmembers : natlist -> nat

val alternate : natlist -> natlist -> natlist

type bag = natlist

val count : nat -> bag -> nat

val sum : bag -> bag -> bag

val add : nat -> bag -> bag

val member : nat -> bag -> Basics.bool

val remove_one : nat -> bag -> bag

val remove_all : nat -> bag -> bag

val subset : bag -> bag -> Basics.bool

val snoc : natlist -> nat -> natlist

val rev : natlist -> natlist

val beq_natlist : natlist -> natlist -> Basics.bool

val index_bad : nat -> natlist -> nat

type natoption =
| Some of nat
| None

val natoption_rect : (nat -> 'a1) -> 'a1 -> natoption -> 'a1

val natoption_rec : (nat -> 'a1) -> 'a1 -> natoption -> 'a1

val index : nat -> natlist -> natoption

val index' : nat -> natlist -> natoption

val option_elim : nat -> natoption -> nat

val hd_opt : natlist -> natoption

module Dictionary : 
 sig 
  type dictionary =
  | Coq_empty
  | Coq_record of nat * nat * dictionary
  
  val dictionary_rect :
    'a1 -> (nat -> nat -> dictionary -> 'a1 -> 'a1) -> dictionary -> 'a1
  
  val dictionary_rec :
    'a1 -> (nat -> nat -> dictionary -> 'a1 -> 'a1) -> dictionary -> 'a1
  
  val insert : nat -> nat -> dictionary -> dictionary
  
  val find : nat -> dictionary -> natoption
 end

