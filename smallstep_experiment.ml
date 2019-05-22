(* Representations of grammar symbols *)
type terminal    = string
type nonterminal = char
type symbol      = T of terminal | NT of nonterminal
(* Finite sets of nonterminals *)
module NtAsOt    =
  struct
    type t       = nonterminal
    let compare  = compare
  end    
module NtSet     = Set.Make(NtAsOt)
(* Finite sets of sentential forms *)
module GammaAsOt =
  struct
    type t       = symbol list
    let compare  = compare
  end
module GammaSet  = Set.Make(GammaAsOt)
(* Grammar-related definitions *)                           
type production  = nonterminal * symbol list
type grammar     = production list
(* A grammar location is a triple (x, rpre, rsuf) such that 
   (x, rpre ++ rsuf) is a grammar production. *)
type grammar_loc = nonterminal * symbol list * symbol list
type loc_stack   = grammar_loc * grammar_loc list
(* Definitions related to input that the parser consumes. *)
type sym_arg     = S_arg of symbol | G_arg of grammar_loc
type literal     = string
type token       = terminal * literal
(* Parser return values *)
type tree        = Leaf of literal | Node of nonterminal * forest
and  forest      = tree list
type parse_res   = S_accept of tree * token list
                 | G_accept of tree list * token list
                 | Reject   of string
                 | Error    of string
(* Prediction-related definitions *)                                 
type ('a,'b) sum = Inl of 'a | Inr of 'b                                 
type subparser   = { location   : grammar_loc
                   ; stack      : grammar_loc list
                   ; prediction : symbol list
                   }
module LsAsOt    =
  struct
    type t       = loc_stack
    let compare  = compare
  end
module LsMap     = Map.Make(LsAsOt)
type ls_ps_map   = GammaSet.t LsMap.t


type frame = { lhs_opt : nonterminal option
             ; rhs_pre : symbol list
             ; rhs_suf : symbol list
             ; sem_val : forest
             }
type lookahead = LA of terminal | EOF
module PtKeyAsOt =
  struct
    type t      = nonterminal * lookahead
    let compare = compare
  end
module ParseTable = Map.Make(PtKeyAsOt)
type parse_table  = (symbol list) ParseTable.t
let peek (ts : token list) : lookahead =
  match ts with
  | []          -> EOF
  | (a, _) :: _ -> LA a

type stack = frame list
type state = Error   of string
           | K       of frame * stack * token list
           | Accept  of forest * token list
           | Reject  of string

let step (tbl : parse_table) (fr : frame) (stk : stack) (ts : token list) : state =
  match fr with
  | {lhs_opt = lo; rhs_pre = rpre; rhs_suf = rsuf; sem_val = sv} ->
     match rsuf with
     (* no more symbols to process in this stack frame *)
     | [] ->
        (match lo with
         (* we're in the top level frame *)
         | None ->
            (match stk with
             | []     -> Accept (sv, ts)
             | _ :: _ -> Error "impossible")
         | Some x ->
            (match stk with
             | [] -> Error "impossible"
             | {lhs_opt = lo'; rhs_pre = rpre'; rhs_suf = rsuf'; sem_val = sv'} :: stk' ->
                (match rsuf' with
                 | [] -> Error "impossible"
                 | T _ :: _ -> Error "impossible"
                 | NT x' :: rsuf'' ->
                    if x = x' then
                      let fr' = { lhs_opt = lo'
                                ; rhs_pre = rpre' @ [NT x]
                                ; rhs_suf = rsuf''
                                ; sem_val = (Node (x, List.rev sv) :: sv')
                                }
                      in  K (fr', stk', ts)
                    else
                      Error "impossible")))
     | T a :: rsuf' ->
        (match ts with
         | []             -> Reject "input exhausted"
         | (a', l) :: ts' ->
            if a = a' then
              let fr' = { lhs_opt = lo
                        ; rhs_pre = rpre @ [T a]
                        ; rhs_suf = rsuf'
                        ; sem_val = Leaf a :: sv
                        }
              in  K (fr', stk, ts')
            else
              Reject "token mismatch")
     | NT x :: rsuf' ->
        match ParseTable.find_opt (x, peek ts) tbl with
        | Some gamma ->
           let fr' = { lhs_opt = Some x
                     ; rhs_pre = []
                     ; rhs_suf = gamma
                     ; sem_val = []
                     }
           in  K (fr', fr :: stk, ts)
        | None -> Reject "no parse table entry"

let rec run (tbl : parse_table) (fr : frame) (stk : stack) (ts : token list) : state =
  match step tbl fr stk ts with
  | Accept (f, ts')    -> Accept (f, ts')
  | Reject s           -> Reject s
  | Error s            -> Error s
  | K (fr', stk', ts') -> run tbl fr' stk' ts'

let parse (tbl : parse_table) (s : symbol) (ts : token list) =
  let fr = { lhs_opt = None
           ; rhs_pre = []
           ; rhs_suf = [s]
           ; sem_val = []
           }
  in  run tbl fr [] ts

let g = [ ('S', [T "a"])
        ; ('S', [T "b"])
        ]

let tbl = ParseTable.add ('S', LA "a") [T "a"; T "c"]
            (ParseTable.add ('S', LA "b") [T "b"; T "c"] ParseTable.empty)
                           
let ts = [("a", "sam"); ("c", "anna")]
                                           
