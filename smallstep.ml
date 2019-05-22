open Defs
open Prediction

type lookahead    = LA of terminal | EOF

module PtKeyAsOt  =
  struct
    type t        = nonterminal * lookahead
    let compare   = compare
  end
module ParseTable = Map.Make(PtKeyAsOt)
type parse_table  = (symbol list) ParseTable.t
let pt_find_opt (k : nonterminal * lookahead) (m : parse_table) : (symbol list) option =
  try 
    let gamma = ParseTable.find k m in Some gamma
  with
    Not_found -> None

let peek (ts : token list) : lookahead =
  match ts with
  | []          -> EOF
  | (a, _) :: _ -> LA a

(* A single stack frame in the parser VM *)
type frame = { lhs_opt : nonterminal option
             ; rhs_pre : symbol list
             ; rhs_suf : symbol list
             ; sem_val : forest
             }

(* A stack is essentially a non-empty list of frames *)
type stack        = frame * frame list

type parser_state = stack * token list

type step_result  = StepAccept of forest * token list
                  | StepReject of string
                  | StepK      of stack * token list
                  | StepError  of string

type parse_result = Accept of forest * token list
                  | Reject of string
                  | Error  of string
                                                     
let mkFrame (lo : nonterminal option) (rpre : symbol list) (rsuf : symbol list) (sv : forest) : frame =
  { lhs_opt = lo ; rhs_pre = rpre ; rhs_suf = rsuf ; sem_val = sv }

 let step (tbl : parse_table) ((fr, stk') : stack) (ts : token list) : step_result =
   let {lhs_opt = lo; rhs_pre = rpre; rhs_suf = rsuf; sem_val = sv} = fr in
   match rsuf with
   | [] ->
      (match (lo, stk') with
       | (None, [])            -> StepAccept (sv, ts)
       | (Some x, caller :: stk'') ->
          let {lhs_opt = lo'; rhs_pre = rpre'; rhs_suf = rsuf'; sem_val = sv'} = caller in
          (match rsuf' with
           | []              -> StepError "impossible"
           | T _ :: _        -> StepError "impossible"
           | NT x' :: rsuf'' ->
              if x = x' then
                let caller' = mkFrame lo' (rpre' @ [NT x]) rsuf'' (sv' @ [Node (x, sv)])
                in  StepK ((caller', stk''), ts)
              else
                StepError "impossible")
       | (None, _ :: _) -> StepError "impossible"
       | (Some _, [])   -> StepError "impossible")
   | T a :: rsuf' ->
      (match ts with
       | []             -> StepReject "input exhausted"
       | (a', l) :: ts' ->
          if a = a' then
            let fr' = mkFrame lo (rpre @ [T a]) rsuf' (sv @ [Leaf a])
            in  StepK ((fr', stk'), ts')
          else
            StepReject "token mismatch")
   | NT x :: rsuf' ->
      match pt_find_opt (x, peek ts) tbl with
      | Some gamma -> let callee = mkFrame (Some x) [] gamma []
                      in  StepK ((callee, fr :: stk'), ts)
      | None       -> StepReject "no parse table entry"
                             
let rec run (tbl : parse_table) (stk : stack) (ts : token list) : parse_result =
  match step tbl stk ts with
  | StepAccept (f, ts') -> Accept (f, ts')
  | StepReject s        -> Reject s
  | StepError s         -> Error s
  | StepK (stk', ts')   -> run tbl stk' ts'

let parse (tbl : parse_table) (s : symbol) (ts : token list) =
  let fr_init = { lhs_opt = None
                ; rhs_pre = []
                ; rhs_suf = [s]
                ; sem_val = []
                }
  in  run tbl (fr_init, []) ts

let g = [ ('S', [T "a"])
        ; ('S', [T "b"])
        ]

let tbl = ParseTable.add ('S', LA "a") [T "a"; T "c"]
            (ParseTable.add ('S', LA "b") [T "b"; T "c"] ParseTable.empty)
                           
let ts = [("a", "sam"); ("c", "anna")]
                                           
