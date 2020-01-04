
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

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

module Make_UDT =
 functor (M:MiniDecidableType) ->
 struct
  type t = M.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    M.eq_dec
 end

module Nat =
 struct
  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n0 -> (match m with
               | O -> false
               | S m0 -> eq_dec n0 m0)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_left :
    ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right :
    ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module MakeRaw =
 functor (X:DecidableType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : elt -> t -> bool **)

  let rec mem x = function
  | [] -> false
  | y :: l -> if X.eq_dec x y then true else mem x l

  (** val add : elt -> t -> t **)

  let rec add x s = match s with
  | [] -> x :: []
  | y :: l -> if X.eq_dec x y then s else y :: (add x l)

  (** val singleton : elt -> t **)

  let singleton x =
    x :: []

  (** val remove : elt -> t -> t **)

  let rec remove x = function
  | [] -> []
  | y :: l -> if X.eq_dec x y then l else y :: (remove x l)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f =
    fold_left (flip f)

  (** val union : t -> t -> t **)

  let union s =
    fold add s

  (** val diff : t -> t -> t **)

  let diff s s' =
    fold remove s' s

  (** val inter : t -> t -> t **)

  let inter s s' =
    fold (fun x s0 -> if mem x s' then add x s0 else s0) s []

  (** val subset : t -> t -> bool **)

  let subset s s' =
    is_empty (diff s s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    (&&) (subset s s') (subset s' s)

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | [] -> []
  | x :: l -> if f x then x :: (filter f l) else filter f l

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | [] -> true
  | x :: l -> if f x then for_all f l else false

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | [] -> false
  | x :: l -> if f x then true else exists_ f l

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition f l in
    if f x then ((x :: s1), s2) else (s1, (x :: s2))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements s =
    s

  (** val choose : t -> elt option **)

  let choose = function
  | [] -> None
  | x :: _ -> Some x

  (** val isok : elt list -> bool **)

  let rec isok = function
  | [] -> true
  | a :: l0 -> (&&) (negb (mem a l0)) (isok l0)
 end

module Make =
 functor (X:DecidableType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false
 end

(** val allEqual :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let allEqual beq x xs =
  forallb (beq x) xs

(** val dmap : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec dmap l f =
  match l with
  | [] -> []
  | h :: t0 -> (f h __) :: (dmap t0 (fun x _ -> f x __))

type terminal = char list

type nonterminal = nat

type symbol =
| T of terminal
| NT of nonterminal

(** val t_eq_dec : terminal -> terminal -> bool **)

let rec t_eq_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a1::s1 ->
       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
         (fun x0 x1 x2 x3 x4 x5 x6 x7 ->
         (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
           (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
           if x0
           then if b7
                then if x1
                     then if b8
                          then if x2
                               then if b9
                                    then if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                    else false
                               else if b9
                                    then false
                                    else if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                          else false
                     else if b8
                          then false
                          else if x2
                               then if b9
                                    then if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                    else false
                               else if b9
                                    then false
                                    else if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                else false
           else if b7
                then false
                else if x1
                     then if b8
                          then if x2
                               then if b9
                                    then if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                    else false
                               else if b9
                                    then false
                                    else if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                          else false
                     else if b8
                          then false
                          else if x2
                               then if b9
                                    then if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                    else false
                               else if b9
                                    then false
                                    else if x3
                                         then if b10
                                              then if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                              else false
                                         else if b10
                                              then false
                                              else if x4
                                                   then 
                                                    if b11
                                                    then 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x5
                                                    then 
                                                    if b12
                                                    then 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b13
                                                    then 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b14
                                                    then 
                                                    t_eq_dec
                                                    s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    t_eq_dec
                                                    s0 s1)
           a1)
         a)

(** val nt_eq_dec : nonterminal -> nonterminal -> bool **)

let rec nt_eq_dec n x0 =
  match n with
  | O -> (match x0 with
          | O -> true
          | S _ -> false)
  | S n0 ->
    (match x0 with
     | O -> false
     | S n1 -> nt_eq_dec n0 n1)

(** val gamma_eq_dec : symbol list -> symbol list -> bool **)

let rec gamma_eq_dec l x =
  match l with
  | [] -> (match x with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match x with
     | [] -> false
     | s :: l1 ->
       if match y with
          | T x0 ->
            (match s with
             | T t0 ->
               let rec f s0 x1 =
                 match s0 with
                 | [] ->
                   (match x1 with
                    | [] -> true
                    | _::_ -> false)
                 | a::s1 ->
                   (match x1 with
                    | [] -> false
                    | a1::s2 ->
                      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                        (fun x2 x3 x4 x5 x6 x7 x8 x9 ->
                        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                          (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                          if x2
                          then if b7
                               then if x3
                                    then if b8
                                         then if x4
                                              then if b9
                                                   then 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                   else false
                                              else if b9
                                                   then false
                                                   else 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                         else false
                                    else if b8
                                         then false
                                         else if x4
                                              then if b9
                                                   then 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                   else false
                                              else if b9
                                                   then false
                                                   else 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                               else false
                          else if b7
                               then false
                               else if x3
                                    then if b8
                                         then if x4
                                              then if b9
                                                   then 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                   else false
                                              else if b9
                                                   then false
                                                   else 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                         else false
                                    else if b8
                                         then false
                                         else if x4
                                              then if b9
                                                   then 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                   else false
                                              else if b9
                                                   then false
                                                   else 
                                                    if x5
                                                    then 
                                                    if b10
                                                    then 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b10
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    f s1 s2
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s1 s2)
                          a1)
                        a)
               in f x0 t0
             | NT _ -> false)
          | NT x0 ->
            (match s with
             | T _ -> false
             | NT n0 ->
               let rec f n x1 =
                 match n with
                 | O ->
                   (match x1 with
                    | O -> true
                    | S _ -> false)
                 | S n1 ->
                   (match x1 with
                    | O -> false
                    | S n2 -> f n1 n2)
               in f x0 n0)
       then gamma_eq_dec l0 l1
       else false)

(** val beqGamma : symbol list -> symbol list -> bool **)

let beqGamma xs ys =
  if gamma_eq_dec xs ys then true else false

module MDT_NT =
 struct
  type t = nonterminal

  (** val eq_dec : nat -> nat -> bool **)

  let eq_dec =
    Nat.eq_dec
 end

module NT_as_DT = Make_UDT(MDT_NT)

module NtSet = Make(NT_as_DT)

type production = nonterminal * symbol list

type grammar = production list

(** val lhs : production -> nonterminal **)

let lhs = function
| (x, _) -> x

(** val lhss : grammar -> nonterminal list **)

let lhss g =
  map lhs g

(** val rhssForNt :
    production list -> nonterminal -> symbol list list **)

let rec rhssForNt ps x =
  match ps with
  | [] -> []
  | p :: ps' ->
    let (x', gamma) = p in
    if nt_eq_dec x' x
    then gamma :: (rhssForNt ps' x)
    else rhssForNt ps' x

(** val fromNtList : nonterminal list -> NtSet.t **)

let fromNtList ls =
  fold_right NtSet.add NtSet.empty ls

(** val allNts : grammar -> NtSet.t **)

let allNts g =
  fromNtList (lhss g)

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

(** val prediction : subparser -> symbol list **)

let prediction x = x.prediction

type prediction_error =
| SpInvalidState
| SpLeftRecursion of nonterminal

type subparser_move_result =
| SpMoveSucc of subparser
| SpMoveReject
| SpMoveError of prediction_error

(** val moveSp :
    grammar -> token -> subparser -> subparser_move_result **)

let moveSp g tok sp =
  let { avail = _; prediction = pred; stack = stk } = sp in
  let (l, locs) = stk in
  let { lopt = xo; rpre = pre; rsuf = rsuf0 } = l in
  (match rsuf0 with
   | [] ->
     (match locs with
      | [] -> SpMoveReject
      | _ :: _ -> SpMoveError SpInvalidState)
   | s :: suf ->
     (match s with
      | T a ->
        let (a', _) = tok in
        if t_eq_dec a' a
        then SpMoveSucc { avail = (allNts g); prediction =
               pred; stack = ({ lopt = xo; rpre =
               (app pre ((T a) :: [])); rsuf = suf }, locs) }
        else SpMoveReject
      | NT _ -> SpMoveError SpInvalidState))

type move_result = (prediction_error, subparser list) sum0

(** val aggrMoveResults :
    subparser_move_result list -> move_result **)

let rec aggrMoveResults = function
| [] -> Inr []
| smr :: smrs' ->
  let m = aggrMoveResults smrs' in
  (match smr with
   | SpMoveSucc sp ->
     (match m with
      | Inl e -> Inl e
      | Inr sps -> Inr (sp :: sps))
   | SpMoveReject -> m
   | SpMoveError e -> Inl e)

(** val move :
    grammar -> token -> subparser list -> move_result **)

let move g tok sps =
  aggrMoveResults (map (moveSp g tok) sps)

type subparser_closure_step_result =
| SpClosureStepDone
| SpClosureStepK of subparser list
| SpClosureStepError of prediction_error

(** val spClosureStep :
    grammar -> subparser -> subparser_closure_step_result **)

let spClosureStep g sp =
  let { avail = av; prediction = pred; stack = stack1 } = sp
  in
  let (loc0, locs) = stack1 in
  let { lopt = _; rpre = _; rsuf = rsuf0 } = loc0 in
  (match rsuf0 with
   | [] ->
     (match locs with
      | [] -> SpClosureStepDone
      | l :: locs_tl ->
        let { lopt = xo_cr; rpre = pre_cr; rsuf = rsuf1 } = l
        in
        (match rsuf1 with
         | [] -> SpClosureStepError SpInvalidState
         | s :: suf_cr ->
           (match s with
            | T _ -> SpClosureStepError SpInvalidState
            | NT x ->
              let stk' = ({ lopt = xo_cr; rpre =
                (app pre_cr ((NT x) :: [])); rsuf = suf_cr },
                locs_tl)
              in
              SpClosureStepK ({ avail = (NtSet.add x av);
              prediction = pred; stack = stk' } :: []))))
   | s :: _ ->
     (match s with
      | T _ -> SpClosureStepDone
      | NT x ->
        if NtSet.mem x av
        then let sps' =
               map (fun rhs -> { avail = (NtSet.remove x av);
                 prediction = pred; stack = ({ lopt = (Some
                 x); rpre = []; rsuf = rhs },
                 (loc0 :: locs)) }) (rhssForNt g x)
             in
             SpClosureStepK sps'
        else if NtSet.mem x (allNts g)
             then SpClosureStepError (SpLeftRecursion x)
             else SpClosureStepK []))

type closure_result = (prediction_error, subparser list) sum0

(** val aggrClosureResults :
    closure_result list -> closure_result **)

let rec aggrClosureResults = function
| [] -> Inr []
| cr :: crs' ->
  let c0 = aggrClosureResults crs' in
  (match cr with
   | Inl e -> Inl e
   | Inr sps ->
     (match c0 with
      | Inl e -> Inl e
      | Inr sps' -> Inr (app sps sps')))

(** val spClosure : grammar -> subparser -> closure_result **)

let rec spClosure g sp =
  match spClosureStep g sp with
  | SpClosureStepDone -> Inr (sp :: [])
  | SpClosureStepK sps' ->
    let crs = dmap sps' (fun sp' _ -> spClosure g sp') in
    aggrClosureResults crs
  | SpClosureStepError e -> Inl e

(** val closure :
    grammar -> subparser list -> (prediction_error, subparser
    list) sum0 **)

let closure g sps =
  aggrClosureResults (map (fun sp -> spClosure g sp) sps)

type prediction_result =
| PredSucc of symbol list
| PredAmbig of symbol list
| PredReject
| PredError of prediction_error

(** val finalConfig : subparser -> bool **)

let finalConfig sp =
  let { avail = _; prediction = _; stack = stack1 } = sp in
  let (l, l0) = stack1 in
  let { lopt = _; rpre = _; rsuf = rsuf0 } = l in
  (match rsuf0 with
   | [] -> (match l0 with
            | [] -> true
            | _ :: _ -> false)
   | _ :: _ -> false)

(** val allPredictionsEqual :
    subparser -> subparser list -> bool **)

let allPredictionsEqual sp sps =
  allEqual beqGamma sp.prediction (map prediction sps)

(** val handleFinalSubparsers :
    subparser list -> prediction_result **)

let handleFinalSubparsers sps =
  match filter finalConfig sps with
  | [] -> PredReject
  | sp :: sps' ->
    if allPredictionsEqual sp sps'
    then PredSucc sp.prediction
    else PredAmbig sp.prediction

(** val llPredict' :
    grammar -> subparser list -> token list ->
    prediction_result **)

let rec llPredict' g sps ts =
  match sps with
  | [] -> PredReject
  | sp :: sps' ->
    if allPredictionsEqual sp sps'
    then PredSucc sp.prediction
    else (match ts with
          | [] -> handleFinalSubparsers sps
          | t0 :: ts' ->
            (match move g t0 sps with
             | Inl msg -> PredError msg
             | Inr mv ->
               (match closure g mv with
                | Inl msg -> PredError msg
                | Inr cl -> llPredict' g cl ts')))

(** val initSps :
    grammar -> nonterminal -> location_stack0 -> subparser
    list **)

let initSps g x = function
| (loc0, locs) ->
  map (fun rhs -> { avail = (allNts g); prediction = rhs;
    stack = ({ lopt = (Some x); rpre = []; rsuf = rhs },
    (loc0 :: locs)) }) (rhssForNt g x)

(** val startState :
    grammar -> nonterminal -> location_stack0 ->
    (prediction_error, subparser list) sum0 **)

let startState g x stk =
  closure g (initSps g x stk)

(** val llPredict :
    grammar -> nonterminal -> location_stack0 -> token list
    -> prediction_result **)

let llPredict g x stk ts =
  match startState g x stk with
  | Inl msg -> PredError msg
  | Inr sps -> llPredict' g sps ts

type frame = { loc : location; sem : forest }

(** val loc : frame -> location **)

let loc x = x.loc

type parser_stack = frame * frame list

(** val lstackOf : parser_stack -> location_stack **)

let lstackOf = function
| (fr, frs) -> (fr.loc, (map loc frs))

type parser_state = { avail0 : NtSet.t;
                      stack0 : parser_stack;
                      tokens : token list; unique : bool }

(** val unique : parser_state -> bool **)

let unique x = x.unique

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

(** val step : grammar -> parser_state -> step_result **)

let step g st =
  let { avail0 = av; stack0 = stack1; tokens = ts; unique =
    u } = st
  in
  let (fr, frs) = stack1 in
  let { loc = loc0; sem = sv } = fr in
  let { lopt = xo; rpre = pre; rsuf = suf } = loc0 in
  (match suf with
   | [] ->
     (match frs with
      | [] ->
        (match ts with
         | [] -> StepAccept sv
         | _ :: _ ->
           StepReject
             ('s'::('t'::('a'::('c'::('k'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::(','::(' '::('t'::('o'::('k'::('e'::('n'::('s'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::[])))))))))))))))))))))))))))))))
      | f :: frs_tl ->
        let { loc = loc1; sem = sv_cr } = f in
        let { lopt = xo_cr; rpre = pre_cr; rsuf = suf_cr } =
          loc1
        in
        (match suf_cr with
         | [] -> StepError InvalidState
         | s :: suf_cr_tl ->
           (match s with
            | T _ -> StepError InvalidState
            | NT x ->
              let cr' = { loc = { lopt = xo_cr; rpre =
                (app pre_cr ((NT x) :: [])); rsuf =
                suf_cr_tl }; sem =
                (app sv_cr ((Node (x, sv)) :: [])) }
              in
              StepK { avail0 = (NtSet.add x av); stack0 =
              (cr', frs_tl); tokens = ts; unique = u })))
   | s :: suf_tl ->
     (match s with
      | T a ->
        (match ts with
         | [] ->
           StepReject
             ('i'::('n'::('p'::('u'::('t'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::[])))))))))))))))
         | t0 :: ts_tl ->
           let (a', l) = t0 in
           if t_eq_dec a' a
           then let fr' = { loc = { lopt = xo; rpre =
                  (app pre ((T a) :: [])); rsuf = suf_tl };
                  sem = (app sv ((Leaf (a, l)) :: [])) }
                in
                StepK { avail0 = (allNts g); stack0 = (fr',
                frs); tokens = ts_tl; unique = u }
           else StepReject
                  ('t'::('o'::('k'::('e'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[])))))))))))))))
      | NT x ->
        if NtSet.mem x av
        then (match llPredict g x (lstackOf (fr, frs)) ts with
              | PredSucc rhs ->
                let callee = { loc = { lopt = (Some x);
                  rpre = []; rsuf = rhs }; sem = [] }
                in
                StepK { avail0 = (NtSet.remove x av);
                stack0 = (callee, (fr :: frs)); tokens = ts;
                unique = u }
              | PredAmbig rhs ->
                let callee = { loc = { lopt = (Some x);
                  rpre = []; rsuf = rhs }; sem = [] }
                in
                StepK { avail0 = (NtSet.remove x av);
                stack0 = (callee, (fr :: frs)); tokens = ts;
                unique = false }
              | PredReject ->
                StepReject
                  ('p'::('r'::('e'::('d'::('i'::('c'::('t'::('i'::('o'::('n'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('v'::('i'::('a'::('b'::('l'::('e'::(' '::('r'::('i'::('g'::('h'::('t'::('-'::('h'::('a'::('n'::('d'::(' '::('s'::('i'::('d'::('e'::('s'::[])))))))))))))))))))))))))))))))))))))))))))
              | PredError e -> StepError (PredictionError e))
        else if NtSet.mem x (allNts g)
             then StepError (LeftRecursion x)
             else StepReject
                    ('n'::('o'::('n'::('t'::('e'::('r'::('m'::('i'::('n'::('a'::('l'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::(' '::('g'::('r'::('a'::('m'::('m'::('a'::('r'::[]))))))))))))))))))))))))))))

(** val multistep :
    grammar -> parser_state -> parse_result **)

let rec multistep g st =
  match step g st with
  | StepAccept sv -> if st.unique then Accept sv else Ambig sv
  | StepReject s -> Reject s
  | StepK st' -> multistep g st'
  | StepError e -> Error e

(** val mkInitState :
    grammar -> symbol list -> token list -> parser_state **)

let mkInitState g gamma ts =
  { avail0 = (allNts g); stack0 = ({ loc = { lopt = None;
    rpre = []; rsuf = gamma }; sem = [] }, []); tokens = ts;
    unique = true }

(** val parse :
    grammar -> symbol list -> token list -> parse_result **)

let parse g gamma ts =
  multistep g (mkInitState g gamma ts)

(** val int : char list **)

let int =
  'I'::('n'::('t'::[]))

(** val float : char list **)

let float =
  'F'::('l'::('o'::('a'::('t'::[]))))

(** val str : char list **)

let str =
  'S'::('t'::('r'::[]))

(** val tru : char list **)

let tru =
  'T'::('r'::('u'::[]))

(** val fls : char list **)

let fls =
  'F'::('l'::('s'::[]))

(** val null : char list **)

let null =
  'N'::('u'::('l'::('l'::[])))

(** val leftBrace : char list **)

let leftBrace =
  'L'::('e'::('f'::('t'::('B'::('r'::('a'::('c'::('e'::[]))))))))

(** val rightBrace : char list **)

let rightBrace =
  'R'::('i'::('g'::('h'::('t'::('B'::('r'::('a'::('c'::('e'::[])))))))))

(** val leftBrack : char list **)

let leftBrack =
  'L'::('e'::('f'::('t'::('B'::('r'::('a'::('c'::('k'::[]))))))))

(** val rightBrack : char list **)

let rightBrack =
  'R'::('i'::('g'::('h'::('t'::('B'::('r'::('a'::('c'::('k'::[])))))))))

(** val colon : char list **)

let colon =
  'C'::('o'::('l'::('o'::('n'::[]))))

(** val comma : char list **)

let comma =
  'C'::('o'::('m'::('m'::('a'::[]))))

(** val value : nat **)

let value =
  O

(** val pairs : nat **)

let pairs =
  S O

(** val pairsTl : nat **)

let pairsTl =
  S (S O)

(** val pair : nat **)

let pair =
  S (S (S O))

(** val elts : nat **)

let elts =
  S (S (S (S O)))

(** val eltsTl : nat **)

let eltsTl =
  S (S (S (S (S O))))

(** val jsonGrammar : grammar **)

let jsonGrammar =
  (value, ((T leftBrace) :: ((NT pairs) :: ((T
    rightBrace) :: [])))) :: ((value, ((T leftBrack) :: ((NT
    elts) :: ((T rightBrack) :: [])))) :: ((value, ((T
    str) :: [])) :: ((value, ((T int) :: [])) :: ((value, ((T
    float) :: [])) :: ((value, ((T tru) :: [])) :: ((value,
    ((T fls) :: [])) :: ((value, ((T
    null) :: [])) :: ((pairs, []) :: ((pairs, ((NT
    pair) :: ((NT pairsTl) :: []))) :: ((pairsTl,
    []) :: ((pairsTl, ((T comma) :: ((NT pair) :: ((NT
    pairsTl) :: [])))) :: ((pair, ((T str) :: ((T
    colon) :: ((NT value) :: [])))) :: ((elts, []) :: ((elts,
    ((NT value) :: ((NT eltsTl) :: []))) :: ((eltsTl,
    []) :: ((eltsTl, ((T comma) :: ((NT value) :: ((NT
    eltsTl) :: [])))) :: []))))))))))))))))
