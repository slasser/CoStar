(* Representations of grammar symbols *)
type terminal     = string
type nonterminal  = char
type symbol       = T of terminal | NT of nonterminal

(* Finite sets of nonterminals *)
module NtAsOt     =
  struct
    type t        = nonterminal
    let compare   = compare
  end    
module NtSet      = Set.Make(NtAsOt)

(* Grammar-related definitions *)                           
type production   = nonterminal * symbol list
type grammar      = production list

(* Definitions related to input that the parser consumes. *)
type literal      = string
type token        = terminal * literal

(* Parser return values *)
type tree         = Leaf of literal | Node of nonterminal * forest
and  forest       = tree list
type parse_res    = S_accept of tree * token list
                  | G_accept of tree list * token list
                  | Reject   of string
                  | Error    of string

(* Generally useful definitions *)
type ('a,'b) sum  = Inl of 'a | Inr of 'b                                 
