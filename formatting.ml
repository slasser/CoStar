open Defs

let showT (a : terminal) : string = a
                                          
let showNT (x : nonterminal) : string = Char.escaped x

let showSym (s : symbol) : string =
  match s with
  | T a  -> "T "  ^ (showT a)
  | NT x -> "NT " ^ (showNT x)
                      
let showGamma (gamma : symbol list) : string =
  "[" ^ (String.concat ", " (List.map showSym gamma)) ^ "]"
                                                          
let showToken ((a, lit) : token) : string =
  Printf.sprintf "(%s, %s)" a lit

let showTokens' (ts : token list) : string =
  "[" ^ String.concat ", " (List.map showToken ts) ^ "]"
                
let showTokens (ts : token list) : string =
  match ts with
  | []     -> "[]"
  | _ :: _ -> showTokens' ts
                                                          
let showOption (o : 'a option) (showA : 'a -> string) : string =
  match o with
  | Some a -> "Some " ^ (showA a)
  | None   -> "None"
