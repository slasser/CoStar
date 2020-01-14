
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type MiniDecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module Make_UDT :
 functor (M:MiniDecidableType) ->
 sig
  type t = M.t

  val eq_dec : t -> t -> bool
 end

module Nat :
 sig
  val eq_dec : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module MakeRaw :
 functor (X:DecidableType) ->
 sig
  type elt = X.t

  type t = elt list

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val union : t -> t -> t

  val diff : t -> t -> t

  val inter : t -> t -> t

  val subset : t -> t -> bool

  val equal : t -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val isok : elt list -> bool
 end

module Make :
 functor (X:DecidableType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool
 end

val allEqual : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val dmap : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list

type terminal = char list

type nonterminal = nat

type symbol =
| T of terminal
| NT of nonterminal

val t_eq_dec : terminal -> terminal -> bool

val nt_eq_dec : nonterminal -> nonterminal -> bool

val gamma_eq_dec : symbol list -> symbol list -> bool

val beqGamma : symbol list -> symbol list -> bool

module MDT_NT :
 sig
  type t = nonterminal

  val eq_dec : nat -> nat -> bool
 end

module NT_as_DT :
 sig
  type t = nonterminal

  val eq_dec : nonterminal -> nonterminal -> bool
 end

module NtSet :
 sig
  module Raw :
   sig
    type elt = nonterminal

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = nonterminal

    val eq_dec : nonterminal -> nonterminal -> bool
   end

  type elt = nonterminal

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool
 end

type production = nonterminal * symbol list

type grammar = production list

val lhs : production -> nonterminal

val lhss : grammar -> nonterminal list

val rhssForNt :
  production list -> nonterminal -> symbol list list

val fromNtList : nonterminal list -> NtSet.t

val allNts : grammar -> NtSet.t

type literal = char list

type token = terminal * literal

type tree =
| Leaf of terminal * literal
| Node of nonterminal * tree list

type forest = tree list

type location = { lopt : nonterminal option;
                  rpre : symbol list; rsuf : symbol list }

type location_stack = location * location list

type ('a, 'b) sum0 = ('a, 'b) sum

type location_stack0 = location * location list

type subparser = { avail : NtSet.t; prediction : symbol list;
                   stack : location_stack0 }

val prediction : subparser -> symbol list

type prediction_error =
| SpInvalidState
| SpLeftRecursion of nonterminal

type subparser_move_result =
| SpMoveSucc of subparser
| SpMoveReject
| SpMoveError of prediction_error

val moveSp :
  grammar -> token -> subparser -> subparser_move_result

type move_result = (prediction_error, subparser list) sum0

val aggrMoveResults :
  subparser_move_result list -> move_result

val move : grammar -> token -> subparser list -> move_result

type subparser_closure_step_result =
| SpClosureStepDone
| SpClosureStepK of subparser list
| SpClosureStepError of prediction_error

val spClosureStep :
  grammar -> subparser -> subparser_closure_step_result

type closure_result = (prediction_error, subparser list) sum0

val aggrClosureResults : closure_result list -> closure_result

val spClosure : grammar -> subparser -> closure_result

val closure :
  grammar -> subparser list -> (prediction_error, subparser
  list) sum0

type prediction_result =
| PredSucc of symbol list
| PredAmbig of symbol list
| PredReject
| PredError of prediction_error

val finalConfig : subparser -> bool

val allPredictionsEqual : subparser -> subparser list -> bool

val handleFinalSubparsers :
  subparser list -> prediction_result

val llPredict' :
  grammar -> subparser list -> token list -> prediction_result

val initSps :
  grammar -> nonterminal -> location_stack0 -> subparser list

val startState :
  grammar -> nonterminal -> location_stack0 ->
  (prediction_error, subparser list) sum0

val llPredict :
  grammar -> nonterminal -> location_stack0 -> token list ->
  prediction_result

type frame = { loc : location; sem : forest }

val loc : frame -> location

type parser_stack = frame * frame list

val lstackOf : parser_stack -> location_stack

type parser_state = { avail0 : NtSet.t;
                      stack0 : parser_stack;
                      tokens : token list; unique : bool }

val unique : parser_state -> bool

type parse_error =
| InvalidState
| LeftRecursion of nonterminal
| PredictionError of prediction_error

type step_result =
| StepAccept of forest
| StepReject of char list
| StepK of parser_state
| StepError of parse_error

type parse_result =
| Accept of forest
| Ambig of forest
| Reject of char list
| Error of parse_error

val step : grammar -> parser_state -> step_result

val multistep : grammar -> parser_state -> parse_result

val mkInitState :
  grammar -> symbol list -> token list -> parser_state

val parse :
  grammar -> symbol list -> token list -> parse_result

val int : char list

val float : char list

val str : char list

val tru : char list

val fls : char list

val null : char list

val leftBrace : char list

val rightBrace : char list

val leftBrack : char list

val rightBrack : char list

val colon : char list

val comma : char list

val value : nat

val pairs : nat

val pairsTl : nat

val pair : nat

val elts : nat

val eltsTl : nat

val jsonGrammar : grammar
