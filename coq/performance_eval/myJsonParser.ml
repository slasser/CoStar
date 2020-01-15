
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val option_map :
    ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

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

type positive =
| XI of positive
| XO of positive
| XH

module Pos =
 struct
  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)
 end

module PositiveOrderedTypeBits =
 struct
  type t = positive

  (** val eqb : positive -> positive -> bool **)

  let eqb =
    Pos.eqb

  (** val eq_dec : positive -> positive -> bool **)

  let eq_dec x y =
    let b = Pos.eqb x y in if b then true else false

  (** val compare : positive -> positive -> comparison **)

  let rec compare x y =
    match x with
    | XI x0 -> (match y with
                | XI y0 -> compare x0 y0
                | _ -> Gt)
    | XO x0 -> (match y with
                | XO y0 -> compare x0 y0
                | _ -> Lt)
    | XH -> (match y with
             | XI _ -> Lt
             | XO _ -> Gt
             | XH -> Eq)
 end

module PositiveSet =
 struct
  module E = PositiveOrderedTypeBits

  type elt = positive

  type tree =
  | Leaf
  | Node of tree * bool * tree

  type t = tree

  (** val empty : t **)

  let empty =
    Leaf

  (** val is_empty : t -> bool **)

  let rec is_empty = function
  | Leaf -> true
  | Node (l, b, r) ->
    if if negb b then is_empty l else false
    then is_empty r
    else false

  (** val mem : positive -> t -> bool **)

  let rec mem i = function
  | Leaf -> false
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> mem i0 r
     | XO i0 -> mem i0 l
     | XH -> o)

  (** val add : positive -> t -> t **)

  let rec add i = function
  | Leaf ->
    (match i with
     | XI i0 -> Node (Leaf, false, (add i0 Leaf))
     | XO i0 -> Node ((add i0 Leaf), false, Leaf)
     | XH -> Node (Leaf, true, Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> Node (l, o, (add i0 r))
     | XO i0 -> Node ((add i0 l), o, r)
     | XH -> Node (l, true, r))

  (** val singleton : positive -> t **)

  let singleton i =
    add i empty

  (** val node : t -> bool -> t -> t **)

  let node l b r =
    if b
    then Node (l, b, r)
    else (match l with
          | Leaf ->
            (match r with
             | Leaf -> Leaf
             | Node (_, _, _) -> Node (l, false, r))
          | Node (_, _, _) -> Node (l, false, r))

  (** val remove : positive -> t -> t **)

  let rec remove i = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    (match i with
     | XI i0 -> node l o (remove i0 r)
     | XO i0 -> node (remove i0 l) o r
     | XH -> node l false r)

  (** val union : t -> t -> t **)

  let rec union m m' =
    match m with
    | Leaf -> m'
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> m
       | Node (l', o', r') ->
         Node ((union l l'), ((||) o o'), (union r r')))

  (** val inter : t -> t -> t **)

  let rec inter m m' =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> Leaf
       | Node (l', o', r') ->
         node (inter l l') ((&&) o o') (inter r r'))

  (** val diff : t -> t -> t **)

  let rec diff m m' =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> m
       | Node (l', o', r') ->
         node (diff l l') ((&&) o (negb o')) (diff r r'))

  (** val equal : t -> t -> bool **)

  let rec equal m m' =
    match m with
    | Leaf -> is_empty m'
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> is_empty m
       | Node (l', o', r') ->
         if if eqb o o' then equal l l' else false
         then equal r r'
         else false)

  (** val subset : t -> t -> bool **)

  let rec subset m m' =
    match m with
    | Leaf -> true
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> is_empty m
       | Node (l', o', r') ->
         if if if negb o then true else o'
            then subset l l'
            else false
         then subset r r'
         else false)

  (** val rev_append : elt -> elt -> elt **)

  let rec rev_append y x =
    match y with
    | XI y0 -> rev_append y0 (XI x)
    | XO y0 -> rev_append y0 (XO x)
    | XH -> x

  (** val rev : elt -> elt **)

  let rev x =
    rev_append x XH

  (** val xfold :
      (positive -> 'a1 -> 'a1) -> t -> 'a1 -> positive -> 'a1 **)

  let rec xfold f m v i =
    match m with
    | Leaf -> v
    | Node (l, b, r) ->
      if b
      then xfold f r (f (rev i) (xfold f l v (XO i))) (XI i)
      else xfold f r (xfold f l v (XO i)) (XI i)

  (** val fold :
      (positive -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f m i =
    xfold f m i XH

  (** val xforall :
      (positive -> bool) -> t -> positive -> bool **)

  let rec xforall f m i =
    match m with
    | Leaf -> true
    | Node (l, o, r) ->
      if if if negb o then true else f (rev i)
         then xforall f r (XI i)
         else false
      then xforall f l (XO i)
      else false

  (** val for_all : (positive -> bool) -> t -> bool **)

  let for_all f m =
    xforall f m XH

  (** val xexists :
      (positive -> bool) -> t -> positive -> bool **)

  let rec xexists f m i =
    match m with
    | Leaf -> false
    | Node (l, o, r) ->
      if if if o then f (rev i) else false
         then true
         else xexists f r (XI i)
      then true
      else xexists f l (XO i)

  (** val exists_ : (positive -> bool) -> t -> bool **)

  let exists_ f m =
    xexists f m XH

  (** val xfilter :
      (positive -> bool) -> t -> positive -> t **)

  let rec xfilter f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      node (xfilter f l (XO i))
        (if o then f (rev i) else false) (xfilter f r (XI i))

  (** val filter : (positive -> bool) -> t -> t **)

  let filter f m =
    xfilter f m XH

  (** val xpartition :
      (positive -> bool) -> t -> positive -> t * t **)

  let rec xpartition f m i =
    match m with
    | Leaf -> (Leaf, Leaf)
    | Node (l, o, r) ->
      let (lt, lf) = xpartition f l (XO i) in
      let (rt, rf) = xpartition f r (XI i) in
      if o
      then let fi = f (rev i) in
           ((node lt fi rt), (node lf (negb fi) rf))
      else ((node lt false rt), (node lf false rf))

  (** val partition : (positive -> bool) -> t -> t * t **)

  let partition f m =
    xpartition f m XH

  (** val xelements :
      t -> positive -> positive list -> positive list **)

  let rec xelements m i a =
    match m with
    | Leaf -> a
    | Node (l, b, r) ->
      if b
      then xelements l (XO i)
             ((rev i) :: (xelements r (XI i) a))
      else xelements l (XO i) (xelements r (XI i) a)

  (** val elements : t -> positive list **)

  let elements m =
    xelements m XH []

  (** val cardinal : t -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, b, r) ->
    if b
    then S (Coq__1.add (cardinal l) (cardinal r))
    else Coq__1.add (cardinal l) (cardinal r)

  (** val choose : t -> elt option **)

  let rec choose = function
  | Leaf -> None
  | Node (l, o, r) ->
    if o
    then Some XH
    else (match choose l with
          | Some i -> Some (XO i)
          | None -> option_map (fun x -> XI x) (choose r))

  (** val min_elt : t -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match min_elt l with
     | Some i -> Some (XO i)
     | None ->
       if o
       then Some XH
       else option_map (fun x -> XI x) (min_elt r))

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match max_elt r with
     | Some i -> Some (XI i)
     | None ->
       if o
       then Some XH
       else option_map (fun x -> XO x) (max_elt l))

  (** val compare_bool : bool -> bool -> comparison **)

  let compare_bool a b =
    if a then if b then Eq else Gt else if b then Lt else Eq

  (** val compare : t -> t -> comparison **)

  let rec compare m m' =
    match m with
    | Leaf -> if is_empty m' then Eq else Lt
    | Node (l, o, r) ->
      (match m' with
       | Leaf -> if is_empty m then Eq else Gt
       | Node (l', o', r') ->
         (match compare_bool o o' with
          | Eq ->
            (match compare l l' with
             | Eq -> compare r r'
             | x -> x)
          | x -> x))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s s' =
    if equal s s' then true else false
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

type nonterminal = positive

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

let rec nt_eq_dec p x0 =
  match p with
  | XI p0 ->
    (match x0 with
     | XI p1 -> nt_eq_dec p0 p1
     | _ -> false)
  | XO p0 ->
    (match x0 with
     | XO p1 -> nt_eq_dec p0 p1
     | _ -> false)
  | XH -> (match x0 with
           | XH -> true
           | _ -> false)

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
               let rec f p x1 =
                 match p with
                 | XI p0 ->
                   (match x1 with
                    | XI p1 -> f p0 p1
                    | _ -> false)
                 | XO p0 ->
                   (match x1 with
                    | XO p1 -> f p0 p1
                    | _ -> false)
                 | XH ->
                   (match x1 with
                    | XH -> true
                    | _ -> false)
               in f x0 n0)
       then gamma_eq_dec l0 l1
       else false)

(** val beqGamma : symbol list -> symbol list -> bool **)

let beqGamma xs ys =
  if gamma_eq_dec xs ys then true else false

module NtSet = PositiveSet

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

type tree0 =
| Leaf0 of terminal * literal
| Node0 of nonterminal * tree0 list

type forest = tree0 list

type location = { lopt : nonterminal option;
                  rpre : symbol list; rsuf : symbol list }

type location_stack = location * location list

type ('a, 'b) sum0 = ('a, 'b) sum

type subparser = { avail : NtSet.t; prediction : symbol list;
                   stack : location_stack }

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
  let { avail = av; prediction = pred; stack = stack0 } = sp
  in
  let (loc, locs) = stack0 in
  let { lopt = _; rpre = _; rsuf = rsuf0 } = loc in
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
              let stk' = ({ lopt = xo_cr; rpre = ((NT
                x) :: pre_cr); rsuf = suf_cr }, locs_tl)
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
                 (loc :: locs)) }) (rhssForNt g x)
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
  let { avail = _; prediction = _; stack = stack0 } = sp in
  let (l, l0) = stack0 in
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
    grammar -> nonterminal -> location_stack -> subparser list **)

let initSps g x = function
| (loc, locs) ->
  map (fun rhs -> { avail = (allNts g); prediction = rhs;
    stack = ({ lopt = (Some x); rpre = []; rsuf = rhs },
    (loc :: locs)) }) (rhssForNt g x)

(** val startState :
    grammar -> nonterminal -> location_stack ->
    (prediction_error, subparser list) sum0 **)

let startState g x stk =
  closure g (initSps g x stk)

(** val llPredict :
    grammar -> nonterminal -> location_stack -> token list ->
    prediction_result **)

let llPredict g x stk ts =
  match startState g x stk with
  | Inl msg -> PredError msg
  | Inr sps -> llPredict' g sps ts

type value_stack = forest * forest list

type parser_state = { lstack : location_stack;
                      vstack : value_stack;
                      tokens : token list; avail0 : NtSet.t;
                      unique : bool }

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
  let { lstack = lstack0; vstack = vstack0; tokens = ts;
    avail0 = av; unique = u } = st
  in
  let (fr, frs) = lstack0 in
  let (v, vs) = vstack0 in
  let { lopt = o; rpre = pre; rsuf = suf } = fr in
  (match suf with
   | [] ->
     (match frs with
      | [] ->
        (match vs with
         | [] ->
           (match ts with
            | [] -> StepAccept v
            | _ :: _ ->
              StepReject
                ('s'::('t'::('a'::('c'::('k'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::(','::(' '::('t'::('o'::('k'::('e'::('n'::('s'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::[])))))))))))))))))))))))))))))))
         | _ :: _ -> StepError InvalidState)
      | l :: frs' ->
        let { lopt = o'; rpre = pre'; rsuf = suf' } = l in
        (match vs with
         | [] -> StepError InvalidState
         | v' :: vs' ->
           (match suf' with
            | [] -> StepError InvalidState
            | s :: suf'0 ->
              (match s with
               | T _ -> StepError InvalidState
               | NT x ->
                 let cr' = { lopt = o'; rpre = ((NT
                   x) :: pre'); rsuf = suf'0 }
                 in
                 StepK { lstack = (cr', frs'); vstack =
                 (((Node0 (x, v)) :: v'), vs'); tokens = ts;
                 avail0 = (NtSet.add x av); unique = u }))))
   | s :: suf' ->
     (match s with
      | T a ->
        (match ts with
         | [] ->
           StepReject
             ('i'::('n'::('p'::('u'::('t'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::[])))))))))))))))
         | t0 :: ts' ->
           let (a', l) = t0 in
           if t_eq_dec a' a
           then let fr' = { lopt = o; rpre = ((T a) :: pre);
                  rsuf = suf' }
                in
                StepK { lstack = (fr', frs); vstack =
                (((Leaf0 (a, l)) :: v), vs); tokens = ts';
                avail0 = (allNts g); unique = u }
           else StepReject
                  ('t'::('o'::('k'::('e'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[])))))))))))))))
      | NT x ->
        if NtSet.mem x av
        then (match llPredict g x (fr, frs) ts with
              | PredSucc rhs ->
                let callee = { lopt = (Some x); rpre = [];
                  rsuf = rhs }
                in
                StepK { lstack = (callee, (fr :: frs));
                vstack = ([], (v :: vs)); tokens = ts;
                avail0 = (NtSet.remove x av); unique = u }
              | PredAmbig rhs ->
                let callee = { lopt = (Some x); rpre = [];
                  rsuf = rhs }
                in
                StepK { lstack = (callee, (fr :: frs));
                vstack = ([], (v :: vs)); tokens = ts;
                avail0 = (NtSet.remove x av); unique = false }
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
  { lstack = ({ lopt = None; rpre = []; rsuf = gamma }, []);
    vstack = ([], []); tokens = ts; avail0 = (allNts g);
    unique = true }

(** val parse :
    grammar -> symbol list -> token list -> parse_result **)

let parse g gamma ts =
  multistep g (mkInitState g gamma ts)

(** val jInt : char list **)

let jInt =
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

(** val value : positive **)

let value =
  XH

(** val pairs : positive **)

let pairs =
  XO XH

(** val pairsTl : positive **)

let pairsTl =
  XI XH

(** val pair : positive **)

let pair =
  XO (XO XH)

(** val elts : positive **)

let elts =
  XI (XO XH)

(** val eltsTl : positive **)

let eltsTl =
  XO (XI XH)

(** val jsonGrammar : grammar **)

let jsonGrammar =
  (value, ((T leftBrace) :: ((NT pairs) :: ((T
    rightBrace) :: [])))) :: ((value, ((T leftBrack) :: ((NT
    elts) :: ((T rightBrack) :: [])))) :: ((value, ((T
    str) :: [])) :: ((value, ((T jInt) :: [])) :: ((value,
    ((T float) :: [])) :: ((value, ((T
    tru) :: [])) :: ((value, ((T fls) :: [])) :: ((value, ((T
    null) :: [])) :: ((pairs, []) :: ((pairs, ((NT
    pair) :: ((NT pairsTl) :: []))) :: ((pairsTl,
    []) :: ((pairsTl, ((T comma) :: ((NT pair) :: ((NT
    pairsTl) :: [])))) :: ((pair, ((T str) :: ((T
    colon) :: ((NT value) :: [])))) :: ((elts, []) :: ((elts,
    ((NT value) :: ((NT eltsTl) :: []))) :: ((eltsTl,
    []) :: ((eltsTl, ((T comma) :: ((NT value) :: ((NT
    eltsTl) :: [])))) :: []))))))))))))))))
