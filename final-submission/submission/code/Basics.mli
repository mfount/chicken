open Datatypes
open Peano

val admit : 'a1

type day =
| Coq_monday
| Coq_tuesday
| Coq_wednesday
| Coq_thursday
| Coq_friday
| Coq_saturday
| Coq_sunday

val day_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1

val day_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1

val next_weekday : day -> day

type bool =
| Coq_true
| Coq_false

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

val negb : bool -> bool

val andb : bool -> bool -> bool

val orb : bool -> bool -> bool

val nandb : bool -> bool -> bool

val andb3 : bool -> bool -> bool -> bool

module Playground1 : 
 sig 
  type nat =
  | O
  | S of nat
  
  val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1
  
  val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1
  
  val pred : nat -> nat
 end

val minustwo : nat -> nat

val evenb : nat -> bool

val oddb : nat -> bool

module Playground2 : 
 sig 
  val plus : nat -> nat -> nat
  
  val mult : nat -> nat -> nat
  
  val minus : nat -> nat -> nat
 end

val exp : nat -> nat -> nat

val factorial : nat -> nat

val beq_nat : nat -> nat -> bool

val ble_nat : nat -> nat -> bool

val blt_nat : nat -> nat -> bool

val plus' : nat -> nat -> nat

