open Defs

let nilStr : string = "[]"
                        
let showList (showElt : 'a -> string) (xs : 'a list) =
  match xs with
  | []     -> nilStr
  | _ :: _ -> "[" ^ (String.concat ", " (List.map showElt xs)) ^ "]"
       
let showT (a : terminal) : string =
  a
                                          
let showNt (x : nonterminal) : string =
  Char.escaped x

let showNtList (xs : nonterminal list) : string =
  showList showNt xs

let showSym (s : symbol) : string =
  match s with
  | T a  -> "T "  ^ (showT a)
  | NT x -> "NT " ^ (showNt x)
                      
let showGamma (gamma : symbol list) : string =
  showList showSym gamma
                                                          
let showToken ((a, lit) : token) : string =
  Printf.sprintf "(%s, %s)" a lit
                
let showTokens (ts : token list) : string =
  showList showToken ts
                                                          
let showOption (o : 'a option) (showA : 'a -> string) : string =
  match o with
  | Some a -> "Some " ^ (showA a)
  | None   -> "None"

let showNtSet (s : NtSet.t) : string =
  showList showNt (NtSet.elements s)
