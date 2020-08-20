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

let explode (s : string) : char list = List.init (String.length s) (String.get s)

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false
let is_coq_char c = is_alpha c || is_digit c || Char.equal c '_'

let legal_coq_constr s = for_all is_coq_char (explode s)

let legal_coq_equiv (k : string) : string =
  let open Yojson.Basic                          in
  let open Yojson.Basic.Util                     in
  let subs = from_file "../resources/name_substitutions.json" in
  match member k subs with
  | `String v -> v
  | _         -> failwith ("unrecognized literal: " ^ k)
                     
let normalize_terminal_name (s : string) : string =
  let r = Str.regexp {|^Lit_\(.*\)$|} in
  if Str.string_match r s 0 then
    (* the terminal is a literal in the grammar *)
    let literal = Str.matched_group 1 s in
    if legal_coq_constr literal then
      s
    else
      "Lit_" ^ legal_coq_equiv literal
  else
    s

let coq_keywords = ["type"]

let normalize_nonterminal_name (s : string) : string =
  if mem s coq_keywords
  then s ^ "'"
  else s
    
let optional_count = ref 0
let star_count     = ref 0
let plus_count     = ref 0
let group_count    = ref 0
                                 
let normalize_ebnf_elt (e : elt) : symbol * ebnf_rule list =
  match e with
  | Terminal s    -> let s' = normalize_terminal_name s
                     in  (T s',  [])
  | NonTerminal s -> let s' = normalize_nonterminal_name s
                     in  (NT s', [])
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
  let lhs'            = normalize_nonterminal_name lhs    in
  let rhs', new_rules = map fst prs, concat (map snd prs) in
  ((lhs', rhs'), new_rules)

let bnf_rules_of_ebnf_rule (e : ebnf_rule) : bnf_rule list =
  let rec f (es : ebnf_rule list) (bs : bnf_rule list) : bnf_rule list =
    match es with
    | []        -> bs
    | e :: es'' ->
       let (b, es') = normalize_ebnf_rule e
       in  f (es' @ es'') (bs @ [b])
  in  f [e] []
        
let bnf_of (g : ebnf_grammar) : bnf_grammar =
  concat (map bnf_rules_of_ebnf_rule g)

(* Removing left recursion *)
let lhss (g : bnf_grammar) : string list =
  List.sort_uniq String.compare (map fst g)

let group_by_lhs (g : bnf_grammar) : (string * symbol list list) list =
  let tbl = Hashtbl.create (length g)                         in
  let ()  = List.iter (fun (x, ys) -> Hashtbl.add tbl x ys) g in
  map (fun x -> (x, Hashtbl.find_all tbl x)) (lhss g)

(* Does the list ys start with nonterminal x? *)
let starts_with (x : string) (ys : symbol list) : bool =
  match ys with
  | []
  | T _ :: _  -> false
  | NT y :: _ -> String.equal x y

let alphabetize_rhss (x : string) (rhss : symbol list list) : symbol list list * symbol list list =
  let (lr_rhss, non_lr_rhss) = partition (starts_with x) rhss
  in  (map tl lr_rhss, non_lr_rhss)

let leftrec_elim_count = ref 0
                             
let elim_left_recursion' ((x, rhss) : string * symbol list list) : bnf_rule list =
  let (alphas, betas) = alphabetize_rhss x rhss                              in
  match alphas with
  | []     -> map (fun rhs -> (x, rhs)) rhss (* no left-recursive right-hand sides *)
  | _ :: _ ->
     let x' = "leftrec_" ^ (string_of_int !leftrec_elim_count)                  in
     let () = leftrec_elim_count := !leftrec_elim_count + 1                     in
     let x_rules  = map (fun beta -> (x, beta @ [NT x'])) betas                 in
     let x'_rules = (x', []) :: map (fun alpha -> (x', alpha @ [NT x'])) alphas in
     x_rules @ x'_rules

let elim_left_recursion (g : bnf_grammar) : bnf_grammar =
  concat (map elim_left_recursion' (group_by_lhs g))

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
  normalize_nonterminal_name x :: rhs_nonterminals ys

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
  | T s  -> "T "  ^ s
  | NT s -> "NT " ^ s

let coq_symbol_constructors (names : string list) : string =
  let clauses = map (fun s -> "| " ^ s) names in
  String.concat "\n" clauses
                      
let coq_terminal_defs (g : bnf_grammar) : string =
  Printf.sprintf
    "Inductive terminal' :=\n%s.\n\nDefinition terminal := terminal'."
    (coq_symbol_constructors (terminals g))

let coq_nonterminal_defs (g : bnf_grammar) : string =
  Printf.sprintf
    "Inductive nonterminal' :=\n%s.\n\nDefinition nonterminal := nonterminal'."
    (coq_symbol_constructors (nonterminals g))

let coq_match_clause (lhs : string) (rhs : string) : string =
  Printf.sprintf "| %s => %s" lhs rhs

let coq_show_clauses (names : string list) : string =
  String.concat "\n"
    (map (fun s -> coq_match_clause s (coq_str_lit s)) names)

let coq_showT_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition showT (a : terminal) : string :=\n" ^^
     "match a with\n"                                ^^
     "%s\n"                                          ^^
     "end.")
    (coq_show_clauses (terminals g))

let coq_showNT_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition showNT (x : nonterminal) : string :=\n" ^^
     "match x with\n"                                    ^^
     "%s\n"                                              ^^
     "end.")
    (coq_show_clauses (nonterminals g))

let coq_terminalOfString_clauses (names : string list) : string =
  let clauses = (map (fun s -> coq_match_clause (coq_str_lit s) s) names) in
  let comment = "(* This clause should be unreachable *)"                 in
  let catch_all = coq_match_clause "_" (hd (rev names))                   in
  String.concat "\n" (clauses @ [comment ; catch_all])

let coq_terminalOfString_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition terminalOfString (s : string) : terminal :=\n" ^^
     "match s with\n"                                           ^^
     "%s\n"                                                     ^^
     "end.")
    (coq_terminalOfString_clauses (terminals g))

let coq_bnf_rule ((x, ys) : bnf_rule) : string =
  "(" ^ x ^ ", " ^ coq_list_repr (map coq_symbol ys) ^ ")"
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

(* Functions for generating Coq definitions related to ordered types *)
let all_pairs xs =
  List.sort_uniq compare (List.concat (List.map (fun x -> List.map (fun x' -> (x, x')) xs) xs))

let coq_comparison s s' =
  let c = compare s s' in
  if c < 0 then
    "Lt"
  else if c > 0 then
    "Gt"
  else
    "Eq"

let coq_compare_clause (s, s') =
  Printf.sprintf "| %s, %s => %s" s s' (coq_comparison s s')

let coq_compare_clauses prs =
  String.concat "\n" (List.map coq_compare_clause prs)

let coq_compareT_def g =
  Printf.sprintf
    ("Definition compareT (t t' : terminal) :=\n" ^^
     "match t, t' with\n"                         ^^
     "%s\n"                                       ^^
     "end.")
    (coq_compare_clauses (all_pairs (terminals g)))

let coq_compareNT_def g =
  Printf.sprintf
    ("Definition compareNT (x x' : nonterminal) :=\n" ^^
     "match x, x' with\n"                             ^^
     "%s\n"                                           ^^
     "end.")
    (coq_compare_clauses (all_pairs (nonterminals g)))

let coq__match_clause l r =
  Printf.sprintf "| %s => %s" l r

let coq__nat_of_sym_clauses names =
  String.concat "\n" (List.mapi
                        (fun i n -> coq__match_clause n (string_of_int i))
                        names)

let coq__sym_of_nat_clauses names =
  String.concat "\n"
    ((List.mapi (fun i n -> coq__match_clause (string_of_int i) n)
                names)
     @ [coq__match_clause "_" (List.hd (List.rev names))])

let coq__nat_of_t_def g =
  Printf.sprintf
    ("Definition nat_of_t (t : terminal) : nat :=\n"  ^^
     "match t with\n"                                 ^^
     "%s\n"                                           ^^
     "end.")
    (coq__nat_of_sym_clauses (terminals g))

let coq__t_of_nat_def g =
  Printf.sprintf
    ("Definition t_of_nat (n : nat) : terminal :=\n"  ^^
     "match n with\n"                                 ^^
     "%s\n"                                           ^^
     "end.")
    (coq__sym_of_nat_clauses (terminals g))

let coq__nat_of_nt_def g =
  Printf.sprintf
    ("Definition nat_of_nt (x : nonterminal) : nat :=\n"  ^^
     "match x with\n"                                     ^^
     "%s\n"                                               ^^
     "end.")
    (coq__nat_of_sym_clauses (nonterminals g))

let coq__nt_of_nat_def g =
  Printf.sprintf
    ("Definition nt_of_nat (n : nat) : nonterminal :=\n"  ^^
     "match n with\n"                                     ^^
     "%s\n"                                               ^^
     "end.")
    (coq__sym_of_nat_clauses (nonterminals g))

let coq__compareT_compare_nat_lemma =
  String.concat "\n" [ "Lemma compareT__compare_nat : forall (x y : terminal),"
                     ; "compareT x y = Nat_as_OT_Alt.compare (nat_of_t x) (nat_of_t y)."
                     ; "Proof. intros x y; destruct x; destruct y; auto. Qed."
                     ]

let coq__compareNT_compare_nat_lemma =
  String.concat "\n" [ "Lemma compareNT__compare_nat : forall (x y : nonterminal),"
                     ; "compareNT x y = Nat_as_OT_Alt.compare (nat_of_nt x) (nat_of_nt y)."
                     ; "Proof. intros x y; destruct x; destruct y; auto. Qed."
                     ]

let coq__compareT_sym_lemma =
  String.concat "\n" [ "Lemma compareT_sym : forall (x y : terminal),"
                     ; "compareT y x = CompOpp (compareT x y)."
                     ; "Proof."
                     ; "intros x y; repeat rewrite compareT__compare_nat; apply Nat_as_OT_Alt.compare_sym."
                     ; "Qed."
                     ]

let coq__compareNT_sym_lemma =
  String.concat "\n" [ "Lemma compareNT_sym : forall (x y : nonterminal),"
                     ; "compareNT y x = CompOpp (compareNT x y)."
                     ; "Proof."
                     ; "intros x y; repeat rewrite compareNT__compare_nat; apply Nat_as_OT_Alt.compare_sym."
                     ; "Qed."
                     ]
(* to do : we can probably use compareT__compare_nat 
   to avoid the destructs here *)
let coq__compareT_eq_lemma =
  String.concat "\n" [ "Lemma compareT_eq :"
                     ; "  forall x y : terminal,"
                     ; "    compareT x y = Eq <-> x = y."
                     ; "Proof."
                     ; "  intros x y; split; [intros hc | intros he; subst]."
                     ; "  - destruct x; destruct y; simpl in *; congruence."
                     ; "  - destruct y; auto."
                     ; "Qed."
                     ]

let coq__compareNT_eq_lemma =
  String.concat "\n" [ "Lemma compareNT_eq :"
                     ; "  forall x y : nonterminal,"
                     ; "    compareNT x y = Eq <-> x = y."
                     ; "Proof."
                     ; "  intros x y; split; [intros hc | intros he; subst]."
                     ; "  - destruct x; destruct y; simpl in *; congruence."
                     ; "  - destruct y; auto."
                     ; "Qed."
                     ]
                
let coq__compareT_trans_lemma =
  String.concat "\n" [ "Lemma compareT_trans : forall c (x y z : terminal),"
                     ; "compareT x y = c -> compareT y z = c -> compareT x z = c."
                     ; "Proof."
                     ; "intros c x y z hc hc'; rewrite compareT__compare_nat in *."
                     ; "eapply Nat_as_OT_Alt.compare_trans; eauto."
                     ; "Qed."
                     ]

let coq__compareNT_trans_lemma =
  String.concat "\n" [ "Lemma compareNT_trans : forall c (x y z : nonterminal),"
                     ; "compareNT x y = c -> compareNT y z = c -> compareNT x z = c."
                     ; "Proof."
                     ; "intros c x y z hc hc'; rewrite compareNT__compare_nat in *."
                     ; "eapply Nat_as_OT_Alt.compare_trans; eauto."
                     ; "Qed."
                     ]

let coq__ltb_clause (s, s') =
  let b = if compare s s' < 0 then "true" else "false"
  in  Printf.sprintf "| %s, %s => %s" s s' b

let coq__ltb_clauses prs =
  String.concat "\n" (List.map coq__ltb_clause prs)

let coq__terminal_ltb_def g =
  Printf.sprintf
    ("Definition terminal_ltb (t t' : terminal) :=\n" ^^
     "match t, t' with\n"                             ^^
     "%s\n"                                           ^^
     "end.")
    (coq__ltb_clauses (all_pairs (terminals g)))

let coq__terminal_ltb_not_eq_lemma =
  String.concat "\n" [ "Lemma terminal_ltb_not_eq :"
                     ; "forall x y : terminal,"
                     ; "terminal_ltb x y = true -> x <> y."
                     ; "Proof."
                     ; "unfold terminal_ltb; intros x y ht heq; destruct x; destruct y; try congruence."
                     ; "Qed."
                     ]
    
let coq__terminal_ltb_trans_lemma =
  String.concat "\n" [ "Lemma terminal_ltb_trans :"
                     ; "forall x y z : terminal,"
                     ; "terminal_ltb x y = true -> terminal_ltb y z = true -> terminal_ltb x z = true."
                     ; "Proof."
                     ; "intros x y z; destruct x; destruct y; destruct z; auto."
                     ; "Qed."
                     ]
                
(*let coq__ltb_nonterminal_def g =
  Printf.sprintf
    ("Definition ltb_nonterminal (x x' : nonterminal) :=\n" ^^
     "match x, x' with\n"                                   ^^
     "%s\n"                                                 ^^
     "end.")
    (coq__ltb_clauses (all_pairs (nonterminals g)))
 *)             
let coq_types_module (g : bnf_grammar) (g_name : string) : string =
  String.concat "\n\n" [ coq_types_module_start g_name
                       ; coq_terminal_defs g
                       ; coq_compareT_def g
                       ; coq__nat_of_t_def g
                       ; coq__compareT_compare_nat_lemma
                       ; coq__compareT_eq_lemma
                       ; coq__compareT_trans_lemma
                       ; coq_nonterminal_defs g
                       ; coq_compareNT_def g
                       ; coq__nat_of_nt_def g
                       ; coq__compareNT_compare_nat_lemma
                       ; coq__compareNT_eq_lemma
                       ; coq__compareNT_trans_lemma
                       ; coq_showT_def  g
                       ; coq_showNT_def g
                       ; coq_terminalOfString_def g
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
  String.concat "\n" [ "Require Import OrderedType OrderedTypeAlt OrderedTypeEx."
                     ; "Require Import List String ExtrOcamlBasic ExtrOcamlString."
                     ; "Require Import GallStar.Defs GallStar.Main GallStar.Orders."
                     ; "Import ListNotations."
                     ; "Open Scope list_scope."
                     ; "Open Scope string_scope."
                     ]

let coq_extraction_command (g_name : string) : string =
  Printf.sprintf "Extraction \"%sParser.ml\" D PG %sGrammar parse." g_name g_name

let coq_grammar_file_contents (g : bnf_grammar) (g_name : string) : string =
  String.concat "\n\n"
                [ coq_imports
                ; coq_types_module g g_name
                ; coq_defs_module g_name
                ; coq_export_pg
                ; coq_grammar_def g_name g
                ]

let write_coq_grammar_file (g : ebnf_grammar) (g_name : string) (f_name : string) : unit =
  let g' = elim_left_recursion (bnf_of g)                         in
  let oc = open_out f_name                                        in
  let _  = output_string oc (coq_grammar_file_contents g' g_name) in
  close_out oc
