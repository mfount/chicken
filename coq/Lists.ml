open Basics
open Datatypes
open Peano

type natprod =
| Coq_pair of nat * nat

(** val natprod_rect : (nat -> nat -> 'a1) -> natprod -> 'a1 **)

let natprod_rect f = function
| Coq_pair (x, x0) -> f x x0

(** val natprod_rec : (nat -> nat -> 'a1) -> natprod -> 'a1 **)

let natprod_rec f = function
| Coq_pair (x, x0) -> f x x0

(** val fst : natprod -> nat **)

let fst = function
| Coq_pair (x, y) -> x

(** val snd : natprod -> nat **)

let snd = function
| Coq_pair (x, y) -> y

(** val fst' : natprod -> nat **)

let fst' = function
| Coq_pair (x, y) -> x

(** val snd' : natprod -> nat **)

let snd' = function
| Coq_pair (x, y) -> y

(** val swap_pair : natprod -> natprod **)

let swap_pair = function
| Coq_pair (x, y) -> Coq_pair (y, x)

type natlist =
| Coq_nil
| Coq_cons of nat * natlist

(** val natlist_rect :
    'a1 -> (nat -> natlist -> 'a1 -> 'a1) -> natlist -> 'a1 **)

let rec natlist_rect f f0 = function
| Coq_nil -> f
| Coq_cons (n0, n1) -> f0 n0 n1 (natlist_rect f f0 n1)

(** val natlist_rec :
    'a1 -> (nat -> natlist -> 'a1 -> 'a1) -> natlist -> 'a1 **)

let rec natlist_rec f f0 = function
| Coq_nil -> f
| Coq_cons (n0, n1) -> f0 n0 n1 (natlist_rec f f0 n1)

(** val mylist : natlist **)

let mylist =
  Coq_cons ((S O), (Coq_cons ((S (S O)), (Coq_cons ((S (S (S O))),
    Coq_nil)))))

(** val mylist1 : natlist **)

let mylist1 =
  Coq_cons ((S O), (Coq_cons ((S (S O)), (Coq_cons ((S (S (S O))),
    Coq_nil)))))

(** val mylist2 : natlist **)

let mylist2 =
  Coq_cons ((S O), (Coq_cons ((S (S O)), (Coq_cons ((S (S (S O))),
    Coq_nil)))))

(** val mylist3 : natlist **)

let mylist3 =
  Coq_cons ((S O), (Coq_cons ((S (S O)), (Coq_cons ((S (S (S O))),
    Coq_nil)))))

(** val repeat : nat -> nat -> natlist **)

let rec repeat n = function
| O -> Coq_nil
| S count' -> Coq_cons (n, (repeat n count'))

(** val length : natlist -> nat **)

let rec length = function
| Coq_nil -> O
| Coq_cons (h, t) -> S (length t)

(** val app : natlist -> natlist -> natlist **)

let rec app l1 l2 =
  match l1 with
  | Coq_nil -> l2
  | Coq_cons (h, t) -> Coq_cons (h, (app t l2))

(** val hd : nat -> natlist -> nat **)

let hd default = function
| Coq_nil -> default
| Coq_cons (h, t) -> h

(** val tl : natlist -> natlist **)

let tl = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) -> t

(** val nonzeros : natlist -> natlist **)

let rec nonzeros = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) ->
  (match beq_nat h O with
   | Basics.Coq_true -> nonzeros t
   | Basics.Coq_false -> app (Coq_cons (h, Coq_nil)) (nonzeros t))

(** val oddmembers : natlist -> natlist **)

let rec oddmembers = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) ->
  (match evenb h with
   | Basics.Coq_true -> oddmembers t
   | Basics.Coq_false -> app (Coq_cons (h, Coq_nil)) (oddmembers t))

(** val countoddmembers : natlist -> nat **)

let rec countoddmembers = function
| Coq_nil -> O
| Coq_cons (h, t) ->
  (match oddb h with
   | Basics.Coq_true -> plus (S O) (countoddmembers t)
   | Basics.Coq_false -> countoddmembers t)

(** val alternate : natlist -> natlist -> natlist **)

let rec alternate l1 l2 =
  match l1 with
  | Coq_nil -> l2
  | Coq_cons (h1, t1) ->
    (match l2 with
     | Coq_nil -> l1
     | Coq_cons (h2, t2) ->
       app (Coq_cons (h1, (Coq_cons (h2, Coq_nil)))) (alternate t1 t2))

type bag = natlist

(** val count : nat -> bag -> nat **)

let rec count v = function
| Coq_nil -> O
| Coq_cons (h, t) ->
  (match beq_nat v h with
   | Basics.Coq_true -> plus (S O) (count v t)
   | Basics.Coq_false -> count v t)

(** val sum : bag -> bag -> bag **)

let sum x y =
  app x y

(** val add : nat -> bag -> bag **)

let add v s =
  sum (Coq_cons (v, Coq_nil)) s

(** val member : nat -> bag -> Basics.bool **)

let member v s =
  Basics.negb (beq_nat (count v s) O)

(** val remove_one : nat -> bag -> bag **)

let rec remove_one v = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) ->
  (match beq_nat h v with
   | Basics.Coq_true -> t
   | Basics.Coq_false -> Coq_cons (h, (remove_one v t)))

(** val remove_all : nat -> bag -> bag **)

let rec remove_all v = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) ->
  (match beq_nat h v with
   | Basics.Coq_true -> remove_all v t
   | Basics.Coq_false -> Coq_cons (h, (remove_all v t)))

(** val subset : bag -> bag -> Basics.bool **)

let rec subset s1 s2 =
  match s1 with
  | Coq_nil -> Basics.Coq_true
  | Coq_cons (h, t) ->
    Basics.andb (ble_nat (count h s1) (count h s2)) (subset t s2)

(** val snoc : natlist -> nat -> natlist **)

let rec snoc l v =
  match l with
  | Coq_nil -> Coq_cons (v, Coq_nil)
  | Coq_cons (h, t) -> Coq_cons (h, (snoc t v))

(** val rev : natlist -> natlist **)

let rec rev = function
| Coq_nil -> Coq_nil
| Coq_cons (h, t) -> snoc (rev t) h

(** val beq_natlist : natlist -> natlist -> Basics.bool **)

let rec beq_natlist l1 l2 =
  match l1 with
  | Coq_nil ->
    (match l2 with
     | Coq_nil -> Basics.Coq_true
     | Coq_cons (n, n0) -> Basics.Coq_false)
  | Coq_cons (h1, t1) ->
    (match l2 with
     | Coq_nil -> Basics.Coq_false
     | Coq_cons (h2, t2) -> Basics.andb (beq_nat h1 h2) (beq_natlist t1 t2))

(** val index_bad : nat -> natlist -> nat **)

let rec index_bad n = function
| Coq_nil ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))
| Coq_cons (a, l') ->
  (match beq_nat n O with
   | Basics.Coq_true -> a
   | Basics.Coq_false -> index_bad (pred n) l')

type natoption =
| Some of nat
| None

(** val natoption_rect : (nat -> 'a1) -> 'a1 -> natoption -> 'a1 **)

let natoption_rect f f0 = function
| Some x -> f x
| None -> f0

(** val natoption_rec : (nat -> 'a1) -> 'a1 -> natoption -> 'a1 **)

let natoption_rec f f0 = function
| Some x -> f x
| None -> f0

(** val index : nat -> natlist -> natoption **)

let rec index n = function
| Coq_nil -> None
| Coq_cons (a, l') ->
  (match beq_nat n O with
   | Basics.Coq_true -> Some a
   | Basics.Coq_false -> index (pred n) l')

(** val index' : nat -> natlist -> natoption **)

let rec index' n = function
| Coq_nil -> None
| Coq_cons (a, l') ->
  (match beq_nat n O with
   | Basics.Coq_true -> Some a
   | Basics.Coq_false -> index' (pred n) l')

(** val option_elim : nat -> natoption -> nat **)

let option_elim d = function
| Some n' -> n'
| None -> d

(** val hd_opt : natlist -> natoption **)

let hd_opt = function
| Coq_nil -> None
| Coq_cons (h, t) -> Some h

module Dictionary = 
 struct 
  type dictionary =
  | Coq_empty
  | Coq_record of nat * nat * dictionary
  
  (** val dictionary_rect :
      'a1 -> (nat -> nat -> dictionary -> 'a1 -> 'a1) -> dictionary -> 'a1 **)
  
  let rec dictionary_rect f f0 = function
  | Coq_empty -> f
  | Coq_record (n, n0, d0) -> f0 n n0 d0 (dictionary_rect f f0 d0)
  
  (** val dictionary_rec :
      'a1 -> (nat -> nat -> dictionary -> 'a1 -> 'a1) -> dictionary -> 'a1 **)
  
  let rec dictionary_rec f f0 = function
  | Coq_empty -> f
  | Coq_record (n, n0, d0) -> f0 n n0 d0 (dictionary_rec f f0 d0)
  
  (** val insert : nat -> nat -> dictionary -> dictionary **)
  
  let insert key value d =
    Coq_record (key, value, d)
  
  (** val find : nat -> dictionary -> natoption **)
  
  let rec find key = function
  | Coq_empty -> None
  | Coq_record (k, v, d') ->
    (match beq_nat key k with
     | Basics.Coq_true -> Some v
     | Basics.Coq_false -> find key d')
 end

