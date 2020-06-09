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

(* Functions for creating strings that represent legal Coq source code *)

let coq_list_repr (xs : string list) : string =
  "[" ^ String.concat "; " xs ^ "]"

let coq_constr (s : string) : string =
  String.capitalize_ascii s

let coq_str_lit (s : string) : string =
  Printf.sprintf "\"%s\"" s
                          
let coq_symbol (x : symbol) : string =
  match x with
  | T s  -> "T "  ^ (coq_constr s)
  | NT s -> "NT " ^ (coq_constr s)

let coq_symbol_constructors (names : string list) : string =
  let clauses = map (fun s -> "| " ^ coq_constr s) names in
  String.concat "\n" clauses
                      
let coq_terminal_defs (g : bnf_grammar) : string =
  Printf.sprintf
    "Inductive terminal' :=\n%s.\n\nDefinition terminal := terminal'."
    (coq_symbol_constructors (terminals g))

let coq_nonterminal_defs (g : bnf_grammar) : string =
  Printf.sprintf
    "Inductive nonterminal' :=\n%s.\n\nDefinition nonterminal := nonterminal'."
    (coq_symbol_constructors (nonterminals g))

let coq_match_clause (name : string) : string =
  let constr = coq_constr name in
  Printf.sprintf "| %s => %s" constr (coq_str_lit constr)
                                                 
let coq_match_clauses (names : string list) : string =
  String.concat "\n" (map coq_match_clause names)

let coq_showT_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition showT (a : terminal) : string :=\n" ^^
     "match a with\n"                                ^^
     "%s\n"                                          ^^
     "end.")
    (coq_match_clauses (terminals g))

let coq_showNT_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition showNT (x : nonterminal) : string :=\n" ^^
     "match x with\n"                                    ^^
     "%s\n"                                              ^^
     "end.")
    (coq_match_clauses (nonterminals g))

let coq_bnf_rule ((x, ys) : bnf_rule) : string =
  "(" ^ coq_constr x ^ ", " ^ coq_list_repr (map coq_symbol ys) ^ ")"
                                                                    (*                
let coq_grammar (g : bnf_grammar) : string =
  "[\n" ^ String.concat ";\n\n" (map coq_bnf_rule g) ^ "\n]"
                                                                     *)

let coq_grammar (g : bnf_grammar) : string =
  "[ " ^ String.concat "\n; " (map coq_bnf_rule g) ^ "\n]"
let coq_grammar_def (name : string) (g : bnf_grammar) : string =
  Printf.sprintf "Definition %sGrammar : grammar :=\n%s." name (coq_grammar g)

let coq_types_module_start (name : string) : string =
  Printf.sprintf "Module Export %s_Types <: SYMBOL_TYPES." name

let coq_types_module_end (name : string) : string =
  Printf.sprintf "End %s_Types." name

let coq_t_eq_dec : string =
  String.concat "\n" [ "Lemma t_eq_dec : forall (t t' : terminal),"
                     ; "{t = t'} + {t <> t'}."
                     ; "Proof. decide equality. Defined."
                     ]
  
let coq_nt_eq_dec : string =
  String.concat "\n" [ "Lemma nt_eq_dec : forall (nt nt' : nonterminal),"
                     ; "{nt = nt'} + {nt <> nt'}."                        
                     ; "Proof. decide equality. Defined."
                     ]
                 
let coq_types_module (g : bnf_grammar) (g_name : string) : string =
  String.concat "\n\n" [ coq_types_module_start g_name
                       ; coq_terminal_defs g
                       ; coq_nonterminal_defs g
                       ; coq_t_eq_dec
                       ; coq_nt_eq_dec
                       ; coq_showT_def  g
                       ; coq_showNT_def g
                       ; coq_types_module_end g_name
                       ]

let coq_defs_module (g_name : string) : string =
 Printf.sprintf ("Module Export D <: Defs.T.\n"           ^^
                 "Module Export SymTy := %s_Types.\n"     ^^
                 "Module Export Defs  := DefsFn SymTy.\n" ^^
                 "End D.") g_name

let coq_export_pg : string =
  "Module Export PG := Make D."

let coq_imports : string =
  String.concat "\n" [ "Require Import List String ExtrOcamlBasic ExtrOcamlString."
                     ; "Require Import GallStar.Defs GallStar.Main."
                     ; "Import ListNotations."
                     ; "Open Scope list_scope."
                     ]

let coq_extraction_command (g_name : string) : string =
  Printf.sprintf "Extraction \"%sParser.ml\" D PG %sGrammar parse." g_name g_name

let coq_file_contents (g : bnf_grammar) (g_name : string) : string =
  String.concat "\n\n"
                [ coq_imports
                ; coq_types_module g g_name
                ; coq_defs_module g_name
                ; coq_export_pg
                ; coq_grammar_def g_name g
                ; coq_extraction_command g_name
                ]

(* grammar for s-expressions *)
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
