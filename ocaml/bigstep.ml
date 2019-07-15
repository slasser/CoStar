open Defs
open Prediction

type sym_arg = S_arg of symbol | G_arg of grammar_loc
           
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
          
