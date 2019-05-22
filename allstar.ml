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
(* Finite sets of sentential forms *)
module GammaAsOt  =
  struct
    type t        = symbol list
    let compare   = compare
  end
module GammaSet   = Set.Make(GammaAsOt)
(* Grammar-related definitions *)                           
type production   = nonterminal * symbol list
type grammar      = production list
(* A grammar location is a triple (x, rpre, rsuf) such that 
   (x, rpre ++ rsuf) is a grammar production. *)
type grammar_loc  = nonterminal * symbol list * symbol list
(* Definitions related to input that the parser consumes. *)
type sym_arg      = S_arg of symbol | G_arg of grammar_loc
type literal      = string
type token        = terminal * literal
(* Parser return values *)
type tree         = Leaf of literal | Node of nonterminal * forest
and  forest       = tree list
type parse_res    = S_accept of tree * token list
                  | G_accept of tree list * token list
                  | Reject   of string
                  | Error    of string
(* Prediction-related definitions *)                                 
type ('a,'b) sum  = Inl of 'a | Inr of 'b                                 
type subparser    = { location   : grammar_loc
                    ; stack      : grammar_loc list
                    ; prediction : symbol list
                    }
type loc_stack    = grammar_loc * grammar_loc list
module LsAsOt     =
  struct
    type t        = loc_stack
    let compare   = compare
  end
module LsMap      = Map.Make(LsAsOt)
type loc_pred_map = GammaSet.t LsMap.t
                          
let filterLhsEq (g : grammar) (x : nonterminal) : production list =
  List.filter (fun (x', gamma) -> x = x') g
                       
let rhssForNt (g : grammar) (x : nonterminal) : symbol list list =
  List.map snd (filterLhsEq g x)
                       
let initSubparser (stk : grammar_loc list) (x : nonterminal) (gamma : symbol list) : subparser =
  { location   = (x, [], gamma)
  ; stack      = stk
  ; prediction = gamma
  }
                       
let initSubparsers (g : grammar) (stk : grammar_loc list) (x : nonterminal) : subparser list =
  let rhss = rhssForNt g x
  in  List.map (initSubparser stk x) rhss

let rec closure (g : grammar) (sps : subparser list) : subparser list =
  List.concat (List.map (spClosure g) sps)
and     spClosure (g : grammar) (sp : subparser) : subparser list =
  match sp with
  | {location = (x, rpre, rsuf) ; stack = s ; prediction = p} ->
     match rsuf with
     | [] ->
        (match s with
         | []        -> [sp]
         | loc :: s' ->
            let sp' = { location = loc; stack = s' ; prediction = p }
            in  spClosure g sp')
     | T a :: _      -> [sp]
     | NT y :: rsuf' ->
        let rhss = rhssForNt g y in
        let sps' = List.map (fun gamma -> { location   = (y, [], gamma)
                                          ; stack      = (x, rpre, rsuf') :: s
                                          ; prediction = p
                                          }) rhss
        in  closure g sps'

let startState (g : grammar) (stk : grammar_loc list) (x : nonterminal) =
  let sps = initSubparsers g stk x
  in  closure g sps

let prediction (sp : subparser) : symbol list =
  let {prediction = p} = sp in p
              
let predictions (sps : subparser list) : symbol list list =
  List.map (fun sp -> prediction sp) sps

let rec allEq (xs : 'a list) : bool =
  match xs with
  | []            -> true
  | [_]           -> true
  | x :: y :: xs' -> x = y && allEq (y :: xs')

let allPredictionsEq (sps : subparser list) : bool =
  allEq (predictions sps)

let addSpToMap (sp : subparser) (m : ls_ps_map) : ls_ps_map =
  let {location = loc; stack = stk; prediction = pred} = sp in
  match LsMap.find_opt (loc, stk) m with
  | Some s -> LsMap.add (loc, stk) (GammaSet.add pred s) m
  | None   -> LsMap.add (loc, stk) (GammaSet.singleton pred) m
        
let mkLocstackPredsMap (sps : subparser list) : ls_ps_map =
  List.fold_right addSpToMap sps LsMap.empty

let cardGtOne (s : GammaSet.t) : bool =
  GammaSet.cardinal s > 1

let allLocsAmbiguous (sps : subparser list) : bool =
  let m = mkLocstackPredsMap sps
  in  LsMap.for_all (fun _ ps -> cardGtOne ps) m

let moveSp (a : terminal) (sp : subparser) : subparser option =
  let {location = (x, rpre, rsuf); stack = s; prediction = p} = sp in
  match rsuf with
  | []            -> None
  | NT _ :: _     -> None
  | T a' :: rsuf' ->
     if a = a' then
       Some { location   = (x, rpre @ [T a], rsuf')
            ; stack      = s
            ; prediction = p
            }
     else
       None

let rec extractSome (os : 'a option list) : 'a list =
  match os with
  | []            -> []
  | None :: os'   -> extractSome os'
  | Some x :: os' -> x :: extractSome os'

let move (a : terminal) (sps : subparser list) : subparser list =
  let spOpts = List.map (moveSp a) sps
  in  extractSome spOpts
     
let rec llPredict' (g : grammar) (sps : subparser list) (ts : token list) : (string, symbol list) sum =
  match sps with
  | []      -> Inl "all subparsers died off"
  | sp :: _ ->
     if allPredictionsEq sps then
       Inr (prediction sp)
     else if allLocsAmbiguous sps then
       Inl "all locations are ambiguous"
     else
       match ts with
       | []            -> Inl "input exhausted during prediction"
       | (a, _) :: ts' ->
          let sps' = closure g (move a sps)
          in  llPredict' g sps' ts'
                            
let llPredict (g : grammar) (stk : grammar_loc list) (x : nonterminal) (ts : token list) : (string, symbol list) sum =  
  let sps = startState g stk x
  in  llPredict' g sps ts
           
let rec parse' (g   : grammar)
               (sa  : sym_arg)
               (ts  : token list)
               (stk : grammar_loc list) :
               parse_res = 
  match sa with
  | S_arg (T a) ->
     (match ts with
      | []               -> Reject "input exhausted"
      | (a', lit) :: ts' ->
         if a = a' then S_accept (Leaf lit, ts') else Reject "token mismatch")
  | S_arg (NT x) ->
     (match llPredict g stk x ts with
      | Inl s     -> Reject s
      | Inr gamma ->
         (match parse' g (G_arg (x, [], gamma)) ts stk with
          | S_accept _        -> Error "this can't happen"
          | G_accept (f, ts') -> S_accept (Node (x, f), ts')
          | Reject s          -> Reject s
          | Error s           -> Error s))
  | G_arg (_, _, [])         -> G_accept ([], ts)
  | G_arg (x, rpre, sym :: gamma') ->
     match parse' g (S_arg sym) ts ((x, rpre, gamma') :: stk) with
     | G_accept _           -> Error "this can't happen"
     | Reject s             -> Reject s
     | Error s              -> Error s
     | S_accept (lsib, ts') ->
        (* skipping the visited set component in OCaml version *)
        match parse' g (G_arg (x, rpre @ [sym], gamma')) ts' stk with
        | S_accept _             -> Error "this can't happen"
        | Reject s               -> Reject s
        | Error s                -> Error s
        | G_accept (rsibs, ts'') -> G_accept (lsib :: rsibs, ts'')

let parse g sym ts = parse' g (S_arg sym) ts []
          
let g = [ ('S', [T "a"])
        ; ('S', [T "b"])
        ]

let ts = [("a", "sam")]
          
