open Defs
open Formatting
open Prediction

(* LL(1)-related definitions *)
type lookahead = LA of terminal | EOF

module ParseTable = Map.Make(struct
                               type t = nonterminal * lookahead
                               let compare = compare
                             end)

type parse_table = (symbol list) ParseTable.t

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

type parser_state = stack * token list * NtSet.t

type step_result  = StepAccept of forest * token list
                  | StepReject of string
                  | StepK      of parser_state
                  | StepError  of string

type parse_result = Accept of forest * token list
                  | Reject of string
                  | Error  of string

let showFrame fr : string =
  let {lhs_opt = lo; rhs_pre = rpre; rhs_suf = rsuf} = fr in
  let template = "parsed   : %s \n" ^^
                 "to_parse : %s   "
  in  Printf.sprintf template
                     (showGamma rpre)
                     (showGamma rsuf)

let showStack ((fr, stk') : stack) : string =
  let frame_bound = "\n--------\n" in
  let ss = (showFrame fr) :: (List.map showFrame stk') in 
  String.concat frame_bound ss
                
let showState ((stk, ts, vis) : parser_state) : string =
  let bound = "*****" in
  String.concat "\n" ["STACK" ; bound ; showStack stk ; "INPUT" ; bound ; (showTokens ts); bound ; "VISITED" ; bound ; (showNtSet vis)]
                   
let mkFrame (lo : nonterminal option) (rpre : symbol list) (rsuf : symbol list) (sv : forest) : frame =
  { lhs_opt = lo ; rhs_pre = rpre ; rhs_suf = rsuf ; sem_val = sv }

let stackHeight ((fr, stk') : stack) : int =
  List.length stk'                  
    
let step (tbl : parse_table) (((fr, stk'), ts, vis) : parser_state) : step_result =
  (*let _ = Printf.printf "input length : %d\n" (List.length ts) in
  let _ = Printf.printf "visited set size : %d\n" (NtSet.cardinal vis) in
  let _ = Printf.printf "stack height : %d\n" (stackHeight (fr, stk')) in
  let _ = print_string (showState ((fr, stk'), ts, vis) ^ "\n\n\n") in *)
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
                in  StepK ((caller', stk''), ts, NtSet.remove x vis)
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
            in  StepK ((fr', stk'), ts', NtSet.empty)
          else
            StepReject "token mismatch")
   | NT x :: rsuf' ->
      match pt_find_opt (x, peek ts) tbl with
      | Some gamma -> let callee = mkFrame (Some x) [] gamma []
                      in  StepK ((callee, fr :: stk'), ts, NtSet.add x vis) 
      | None       -> StepReject "no parse table entry"
                             
let rec run (tbl : parse_table) (st : parser_state) : parse_result =
  match step tbl st with
  | StepAccept (f, ts') -> Accept (f, ts')
  | StepReject s        -> Reject s
  | StepError s         -> Error s
  | StepK st'           -> run tbl st'

let parse (tbl : parse_table) (s : symbol) (ts : token list) =
  let fr_init = { lhs_opt = None
                ; rhs_pre = []
                ; rhs_suf = [s]
                ; sem_val = []
                }
  in  run tbl ((fr_init, []), ts, NtSet.empty)

(* TESTING *)
let g1   = [ ('S', [T "a"])
           ; ('S', [T "b"])
           ]

let tbl1 = ParseTable.add ('S', LA "int") [T "int"; T "str"]
             (ParseTable.add ('S', LA "char") [T "char"; T "str"] ParseTable.empty)
             
let ts1  = [("int", "42"); ("str", "hello")]
            
let _    = parse tbl1 (NT 'S') ts1

let g2   = [ ('X', [NT 'Y'; NT 'Y'])
           ; ('Y', [])
           ]

let tbl2 = ParseTable.add ('X', EOF) [NT 'Y'; NT 'Y']
             (ParseTable.add ('Y', EOF) [] ParseTable.empty)

let ts2  = []

let _    = parse tbl2 (NT 'X') ts2

             
