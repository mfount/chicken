open Datatypes
open Peano

(** val admit : 'a1 **)

let admit =
  failwith "AXIOM TO BE REALIZED"

type day =
| Coq_monday
| Coq_tuesday
| Coq_wednesday
| Coq_thursday
| Coq_friday
| Coq_saturday
| Coq_sunday

(** val day_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1 **)

let day_rect f f0 f1 f2 f3 f4 f5 = function
| Coq_monday -> f
| Coq_tuesday -> f0
| Coq_wednesday -> f1
| Coq_thursday -> f2
| Coq_friday -> f3
| Coq_saturday -> f4
| Coq_sunday -> f5

(** val day_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1 **)

let day_rec f f0 f1 f2 f3 f4 f5 = function
| Coq_monday -> f
| Coq_tuesday -> f0
| Coq_wednesday -> f1
| Coq_thursday -> f2
| Coq_friday -> f3
| Coq_saturday -> f4
| Coq_sunday -> f5

(** val next_weekday : day -> day **)

let next_weekday = function
| Coq_monday -> Coq_tuesday
| Coq_tuesday -> Coq_wednesday
| Coq_wednesday -> Coq_thursday
| Coq_thursday -> Coq_friday
| _ -> Coq_monday

type bool =
| Coq_true
| Coq_false

(** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rect f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rec f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val negb : bool -> bool **)

let negb = function
| Coq_true -> Coq_false
| Coq_false -> Coq_true

(** val andb : bool -> bool -> bool **)

let andb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> Coq_false

(** val orb : bool -> bool -> bool **)

let orb b1 b2 =
  match b1 with
  | Coq_true -> Coq_true
  | Coq_false -> b2

(** val nandb : bool -> bool -> bool **)

let nandb b1 b2 =
  negb (andb b1 b2)

(** val andb3 : bool -> bool -> bool -> bool **)

let andb3 b1 b2 b3 =
  andb b1 (andb b2 b3)

module Playground1 = 
 struct 
  type nat =
  | O
  | S of nat
  
  (** val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)
  
  let rec nat_rect f f0 = function
  | O -> f
  | S n0 -> f0 n0 (nat_rect f f0 n0)
  
  (** val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)
  
  let rec nat_rec f f0 = function
  | O -> f
  | S n0 -> f0 n0 (nat_rec f f0 n0)
  
  (** val pred : nat -> nat **)
  
  let pred = function
  | O -> O
  | S n' -> n'
 end

(** val minustwo : nat -> nat **)

let minustwo = function
| O -> O
| S n0 ->
  (match n0 with
   | O -> O
   | S n' -> n')

(** val evenb : nat -> bool **)

let rec evenb = function
| O -> Coq_true
| S n0 ->
  (match n0 with
   | O -> Coq_false
   | S n' -> evenb n')

(** val oddb : nat -> bool **)

let oddb n =
  negb (evenb n)

module Playground2 = 
 struct 
  (** val plus : nat -> nat -> nat **)
  
  let rec plus n m =
    match n with
    | O -> m
    | S n' -> S (plus n' m)
  
  (** val mult : nat -> nat -> nat **)
  
  let rec mult n m =
    match n with
    | O -> O
    | S n' -> plus m (mult n' m)
  
  (** val minus : nat -> nat -> nat **)
  
  let rec minus n m =
    match n with
    | O -> O
    | S n' ->
      (match m with
       | O -> n
       | S m' -> minus n' m')
 end

(** val exp : nat -> nat -> nat **)

let rec exp base = function
| O -> S O
| S p -> mult base (exp base p)

(** val factorial : nat -> nat **)

let rec factorial n = match n with
| O -> S O
| S m -> mult n (factorial m)

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m =
  match n with
  | O ->
    (match m with
     | O -> Coq_true
     | S m' -> Coq_false)
  | S n' ->
    (match m with
     | O -> Coq_false
     | S m' -> beq_nat n' m')

(** val ble_nat : nat -> nat -> bool **)

let rec ble_nat n m =
  match n with
  | O -> Coq_true
  | S n' ->
    (match m with
     | O -> Coq_false
     | S m' -> ble_nat n' m')

(** val blt_nat : nat -> nat -> bool **)

let blt_nat n m =
  andb (ble_nat n m) (negb (beq_nat m n))

(** val plus' : nat -> nat -> nat **)

let rec plus' n m =
  match n with
  | O -> m
  | S n' -> S (plus' n' m)

