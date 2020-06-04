open List
                                  
type elt = Terminal of string
         | NonTerminal of string
         | Optional of elt
         | ZeroOrMore of elt
         | OneOrMore of elt
         | Choice of elt list
         | Sequence of elt list
                           
type ebnf_rule    = string * elt list
type ebnf_grammar = ebnf_rule list

type symbol = T of string
            | NT of string

type bnf_rule    = string * symbol list
                                   
type bnf_grammar = bnf_rule list
                     
let optional_count = ref 0
let star_count     = ref 0
let plus_count     = ref 0
let group_count    = ref 0
                                 
let normalize_ebnf_elt (e : elt) : symbol * ebnf_rule list =
  match e with
  | Terminal s    -> (T s,  [])
  | NonTerminal s -> (NT s, [])
  | Optional e'   -> let s = "optional_" ^ string_of_int !optional_count in
                     let _ = optional_count := !optional_count + 1       in
                     (NT s, [(s, []); (s, [e'])])
  | ZeroOrMore e' -> let s = "star_" ^ string_of_int !star_count in
                     let _ = star_count := !star_count + 1       in
                     (NT s, [(s, []); (s, [e'; NonTerminal s])])
  | OneOrMore e'  -> let s = "plus_" ^ string_of_int !plus_count in
                     let _ = plus_count := !plus_count + 1       in
                     (NT s, [(s, [e']); (s, [e'; NonTerminal s])])
  | Choice es     ->
     let s     = "group_" ^ string_of_int !group_count   in
     let _     = group_count := !group_count + 1         in
     let rules = map (fun e -> match e with
                               | Sequence es' -> (s, es')
                               | _            -> failwith "expected Sequence") es
     in  (NT s, rules)
  | Sequence _    -> failwith "Sequence should have been handled in Choice rule"
                              
let normalize_ebnf_rule ((lhs, rhs) : ebnf_rule) : bnf_rule * ebnf_rule list =
  let prs             = map normalize_ebnf_elt rhs        in
  let rhs', new_rules = map fst prs, concat (map snd prs) in
  ((lhs, rhs'), new_rules)

let bnf_rules_of_ebnf_rule (e : ebnf_rule) : bnf_rule list =
  let rec f (es : ebnf_rule list) (bs : bnf_rule list) : bnf_rule list =
    match es with
    | [] -> bs
    | e :: es'' ->
       let (b, es') = normalize_ebnf_rule e
       in  f (es' @ es'') (bs @ [b])
  in  f [e] []

let bnf_of (g : ebnf_grammar) : bnf_grammar =
  concat (map bnf_rules_of_ebnf_rule g)

let rec rhs_terminals (ys : symbol list) : string list =
  match ys with
  | []          -> []
  | T s :: ys'  -> s :: rhs_terminals ys'
  | NT _ :: ys' -> rhs_terminals ys'

let rule_terminals ((x, ys) : bnf_rule) : string list =
  rhs_terminals ys

let terminals (g : bnf_grammar) : string list =
  sort_uniq compare (concat (map rule_terminals g))

let rec rhs_nonterminals (ys : symbol list) : string list =
  match ys with
  | []          -> []
  | T _ :: ys'  -> rhs_nonterminals ys'
  | NT s :: ys' -> s :: rhs_nonterminals ys'

let rule_nonterminals ((x, ys) : bnf_rule) : string list =
  x :: rhs_nonterminals ys

let nonterminals (g : bnf_grammar) : string list =
  sort_uniq compare (concat (map rule_nonterminals g))

let coq_list_repr (xs : string list) : string =
  "[" ^ String.concat "; " xs ^ "]"

let coq_symbol_name (s : string) : string =
  String.capitalize_ascii s
                          
let coq_symbol (x : symbol) : string =
  match x with
  | T s  -> "T "  ^ (coq_symbol_name s)
  | NT s -> "NT " ^ (coq_symbol_name s)

let coq_bnf_rule ((x, ys) : bnf_rule) : string =
  "(" ^ coq_symbol_name x ^ ", " ^ coq_list_repr (map coq_symbol ys) ^ ")"
                      
let coq_grammar (g : bnf_grammar) : string =
  "[\n" ^ String.concat ";\n\n" (List.map coq_bnf_rule g) ^ "\n]"

let coq_grammar_def (name : string) (g : bnf_grammar) : string =
  Printf.sprintf ("Definition %sGrammar : grammar :=\n%s.") name (coq_grammar g)
                                                                
                      
let tup  : ebnf_rule = ("sexpr", [ZeroOrMore (NonTerminal "item"); Terminal "EOF"])
let tup2 : ebnf_rule = ("content", [Optional (NonTerminal "chardata"); ZeroOrMore (Choice [Sequence [Choice [Sequence [NonTerminal "element"]; Sequence [NonTerminal "reference"]; Sequence [Terminal "CDATA"]; Sequence [Terminal "PI"]; Sequence [Terminal "COMMENT"]]; Optional (NonTerminal "chardata")]])])

let sexpr_grammar : ebnf_grammar = [

    ("sexpr", [ZeroOrMore (NonTerminal "item"); Terminal "EOF"]);
    
    ("item", [NonTerminal "atom"]);
    
    ("item", [NonTerminal "list"]);
    
    ("item", [Terminal "LPAREN"; NonTerminal "item"; Terminal "DOT"; NonTerminal "item"; Terminal "RPAREN"]);
    
    ("list", [Terminal "LPAREN"; ZeroOrMore (NonTerminal "item"); Terminal "RPAREN"]);
    
    ("atom", [Terminal "STRING"]);
    
    ("atom", [Terminal "SYMBOL"]);
    
    ("atom", [Terminal "NUMBER"]);
    
    ("atom", [Terminal "DOT"])
      
  ]

let g = bnf_of sexpr_grammar
                      
