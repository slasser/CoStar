open Defs

(* A grammar location is a triple (x, rpre, rsuf) such that 
   (x, rpre ++ rsuf) is a grammar production. *)
type grammar_loc  = nonterminal * symbol list * symbol list

(* Finite sets of sentential forms *)
module GammaAsOt  =
  struct
    type t        = symbol list
    let compare   = compare
  end
module GammaSet   = Set.Make(GammaAsOt)

(* Subparser used by the ALL( * ) prediction mechanism *)
type subparser    = { location   : grammar_loc
                    ; stack      : grammar_loc list
                    ; prediction : symbol list
                    }

(* Finite map from (location * stack) pairs to production right-hand sides
   (used by ALL( * ) to detect ambiguity) *)
type locstk_pair  = grammar_loc * grammar_loc list
module LsAsOt     =
  struct
    type t        = locstk_pair
    let compare   = compare
  end
module LsMap      = Map.Make(LsAsOt)
type ls_pred_map  = GammaSet.t LsMap.t

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

let cardGtOne (s : GammaSet.t) : bool =
  GammaSet.cardinal s > 1

(* kludge until Tufts OCaml version is updated *)
let find_opt (pr : locstk_pair) (m : ls_pred_map) : (GammaSet.t) option =
  try 
    let gamma = LsMap.find pr m 
    in  Some gamma
  with
    Not_found -> None

let addSpToMap (sp : subparser) (m : ls_pred_map) : ls_pred_map =
  let {location = loc; stack = stk; prediction = pred} = sp in
  match find_opt (loc, stk) m with
  | Some s -> LsMap.add (loc, stk) (GammaSet.add pred s) m
  | None   -> LsMap.add (loc, stk) (GammaSet.singleton pred) m
        
let mkLocstackPredsMap (sps : subparser list) : ls_pred_map =
  List.fold_right addSpToMap sps LsMap.empty

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
