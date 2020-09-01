module Sexp       = Core_kernel.Sexp
module In_channel = Core_kernel.In_channel
(****************************************************************************************)  
(* CONVERT AN S-EXPRESSION REPRESENTATION OF AN ANTLR GRAMMAR TO AN EBNF DATA STRUCTURE *)
(****************************************************************************************)  
let sexp_from_file (fname : string) : Sexp.t =
  Sexp.of_string (In_channel.read_all fname)
                   
let get_name_and_rules_from_sexp_grammar (s : Sexp.t) : string * Sexp.t list =
  match s with
  | Sexp.List [ Sexp.Atom "COMBINED_GRAMMAR"
              ; Sexp.Atom name
              ; Sexp.List (Sexp.Atom "RULES" :: rules)
              ] -> (name, rules)
  | _ -> failwith "unrecognized grammar format"

let get_rule_lhs_and_alts (s : Sexp.t) : string * Sexp.t list =
  match s with
  | Sexp.List [ Sexp.Atom "RULE"
              ; Sexp.Atom lhs
              ; Sexp.List (Sexp.Atom "BLOCK" :: alts)
              ] -> (lhs, alts)
  | _ -> failwith "couldn't extract rule lhs and rhss"

type ebnf_elt    = Terminal of string
                 | NonTerminal of string
                 | Set of string list
                 | Block of ebnf_alt list
                 | Optional of ebnf_alt list
                 | ZeroOrMore of ebnf_alt list
                 | OneOrMore of ebnf_alt list
and ebnf_alt     = ebnf_elt list
and ebnf_rule    = string * ebnf_alt
and ebnf_grammar = ebnf_rule list

let is_upper (s : string) : bool =
  let fst = Char.escaped (String.get s 0) in
  let r   = Str.regexp {|[A-Z]|}          in
  Str.string_match r fst 0

(* to do: refactor symbol case *)
let rec ebnf_elt_of (s : Sexp.t) : ebnf_elt =
  match s with
  | Sexp.Atom symbol_name ->
     let r = Str.regexp {|^'\(.*\)'$|} in
     if Str.string_match r symbol_name 0 then
       (* the terminal is a literal in the grammar *)
       let literal = Str.matched_group 1 symbol_name in
       Terminal ("Lit_" ^ literal)
     else if is_upper symbol_name then
       Terminal symbol_name
     else
       NonTerminal symbol_name
  | Sexp.List (Sexp.Atom "SET" :: ss) ->
     Set (List.map terminal_name_of ss)
  | Sexp.List (Sexp.Atom "BLOCK" :: alts) ->
     Block (List.map ebnf_alt_of alts)
  | Sexp.List [Sexp.Atom "*" ; Sexp.List (Sexp.Atom "BLOCK" :: alts)] ->
     ZeroOrMore (List.map ebnf_alt_of alts)
  | Sexp.List [Sexp.Atom "+" ; Sexp.List (Sexp.Atom "BLOCK" :: alts)] ->
     OneOrMore (List.map ebnf_alt_of alts)
  | Sexp.List [Sexp.Atom "?" ; Sexp.List (Sexp.Atom "BLOCK" :: alts)] ->
     Optional (List.map ebnf_alt_of alts)
  | _ -> failwith ("unrecognized s-exp pattern in ebnf_elt_of: " ^ Sexp.to_string s)
and terminal_name_of (s : Sexp.t) : string =
  match s with
  | Sexp.Atom symbol_name ->
     let r = Str.regexp {|^'\(.*\)'$|} in
     if Str.string_match r symbol_name 0 then
       (* the terminal is a literal in the grammar *)
       let literal = Str.matched_group 1 symbol_name in
       "Lit_" ^ literal
     else if is_upper symbol_name then
       symbol_name
     else
       failwith ("invalid terminal name in set: " ^ symbol_name)
  | _ -> failwith ("unrecognized s-exp pattern in terminal_name_of: " ^ Sexp.to_string s)
and ebnf_alt_of (s : Sexp.t) : ebnf_alt =
  match s with
  | Sexp.List (Sexp.Atom "ALT" :: ss) ->
     List.map ebnf_elt_of ss
  | _ -> failwith ("unrecognized s-exp pattern in ebnf_alt_of: " ^ Sexp.to_string s)

let ebnf_rules_of_sexp_rule (s : Sexp.t) : ebnf_rule list =
  match get_rule_lhs_and_alts s with
  | (lhs, alts) ->
     List.map (fun a -> (lhs, ebnf_alt_of a)) alts

let ebnf_grammar_of_rules (rules : Sexp.t list) : ebnf_grammar =
  List.concat (List.map ebnf_rules_of_sexp_rule rules)
(****************************************************************************************)  
(* CONVERT AN EBNF GRAMMAR TO BNF                                                       *)
(****************************************************************************************)
type symbol     = T of string
                | NT of string
and bnf_rule    = string * symbol list
and bnf_grammar = bnf_rule list

let explode (s : string) : char list =
  List.init (String.length s) (String.get s)

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false

let is_coq_char c = is_alpha c || is_digit c || Char.equal c '_'

let legal_coq_constr s = List.for_all is_coq_char (explode s)

let legal_coq_equiv (k : string) : string =
  let open Yojson.Basic                                       in
  let open Yojson.Basic.Util                                  in
  let subs = from_file "../resources/name_substitutions.json" in
  match member k subs with
  | `String v -> v
  | _         -> failwith ("unrecognized literal: " ^ k)
                     
let normalize_terminal_name (s : string) : string =
  let r = Str.regexp {|^Lit_\(.*\)$|} in
  if Str.string_match r s 0 then
    (* the terminal is a literal in the grammar *)
    let literal = Str.matched_group 1 s in
    if legal_coq_constr literal then s else "Lit_" ^ legal_coq_equiv literal
  else s

let coq_keywords = ["type"; "string"]

let normalize_nonterminal_name (s : string) : string =
  if List.mem s coq_keywords then s ^ "'" else s
    
let optional_count = ref 0
let star_count     = ref 0
let plus_count     = ref 0
let block_count    = ref 0

let incr (ir : int ref) : unit =
  ir := !ir + 1

let fresh_name (base : string) (ir : int ref) : string =
  let s  = base ^ "_" ^ string_of_int !ir in
  let () = incr ir                        in
  s

let fresh_optional_name () = fresh_name "optional" optional_count
let fresh_star_name     () = fresh_name "star" star_count
let fresh_plus_name     () = fresh_name "plus" plus_count
let fresh_block_name    () = fresh_name "block" block_count
                                 
let normalize_ebnf_elt (e : ebnf_elt) : symbol * ebnf_rule list =
  match e with
  | Terminal s    -> let s' = normalize_terminal_name s
                     in  (T s',  [])
  | NonTerminal s -> let s' = normalize_nonterminal_name s
                     in  (NT s', [])
  | Set mems      ->
     let b = fresh_block_name () in
     (NT b, List.map (fun m -> (b, [Terminal m])) mems)
  | Optional alts ->
     let o = fresh_optional_name () in
     let b = fresh_block_name ()    in
     (NT o, (o, []) :: (o, [NonTerminal b]) :: List.map (fun a -> (b, a)) alts)
  | Block alts ->
     let b = fresh_block_name () in
     (NT b, List.map (fun a -> (b, a)) alts)
  | ZeroOrMore alts ->
     let s = fresh_star_name ()  in
     let b = fresh_block_name () in
     (NT s, (s, []) :: (s, [NonTerminal b; NonTerminal s]) :: List.map (fun a -> (b, a)) alts)
  | OneOrMore alts ->
     let p = fresh_plus_name ()  in
     let b = fresh_block_name () in
     (NT p, (p, [NonTerminal b]) :: (p, [NonTerminal b; NonTerminal p]) :: List.map (fun a -> (b, a)) alts)
                              
let normalize_ebnf_rule ((lhs, rhs) : ebnf_rule) : bnf_rule * ebnf_rule list =
  let prs             = List.map normalize_ebnf_elt rhs        in
  let lhs'            = normalize_nonterminal_name lhs    in
  let rhs', new_rules = List.map fst prs, List.concat (List.map snd prs) in
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
  List.concat (List.map bnf_rules_of_ebnf_rule g)
(****************************************************************************************)  
(* ELIMINATE DIRECT LEFT RECURSION FROM A BNF GRAMMAR                                   *)
(****************************************************************************************)
let lhss (g : bnf_grammar) : string list =
  List.sort_uniq String.compare (List.map fst g)

let group_by_lhs (g : bnf_grammar) : (string * symbol list list) list =
  let tbl = Hashtbl.create (List.length g)                         in
  let ()  = List.iter (fun (x, ys) -> Hashtbl.add tbl x ys) g      in
  List.map (fun x -> (x, Hashtbl.find_all tbl x)) (lhss g)

(* Does the list ys start with nonterminal x? *)
let starts_with (x : string) (ys : symbol list) : bool =
  match ys with
  | []
  | T _ :: _  -> false
  | NT y :: _ -> String.equal x y

let alphabetize_rhss (x : string) (rhss : symbol list list) : symbol list list * symbol list list =
  let (lr_rhss, non_lr_rhss) = List.partition (starts_with x) rhss
  in  (List.map List.tl lr_rhss, non_lr_rhss)

let leftrec_elim_count = ref 0
                             
let elim_left_recursion' ((x, rhss) : string * symbol list list) : bnf_rule list =
  let (alphas, betas) = alphabetize_rhss x rhss                              in
  match alphas with
  | []     -> List.map (fun rhs -> (x, rhs)) rhss (* no left-recursive right-hand sides *)
  | _ :: _ ->
     let x' = "leftrec_" ^ (string_of_int !leftrec_elim_count)                       in
     let () = leftrec_elim_count := !leftrec_elim_count + 1                          in
     let x_rules  = List.map (fun beta -> (x, beta @ [NT x'])) betas                 in
     let x'_rules = (x', []) :: List.map (fun alpha -> (x', alpha @ [NT x'])) alphas in
     x_rules @ x'_rules

let elim_left_recursion (g : bnf_grammar) : bnf_grammar =
  List.concat (List.map elim_left_recursion' (group_by_lhs g))
(****************************************************************************************)  
(* CONVERT A BNF GRAMMAR TO A STRING REPRESENTING A COQ MODULE FOR THAT GRAMMAR         *)
(****************************************************************************************)
let rec rhs_terminals (ys : symbol list) : string list =
  match ys with
  | []          -> []
  | T s :: ys'  -> s :: rhs_terminals ys'
  | NT _ :: ys' -> rhs_terminals ys'

let rule_terminals ((_, ys) : bnf_rule) : string list =
  rhs_terminals ys

let terminals (g : bnf_grammar) : string list =
  List.sort_uniq compare (List.concat (List.map rule_terminals g))

let rec rhs_nonterminals (ys : symbol list) : string list =
  match ys with
  | []          -> []
  | T _ :: ys'  -> rhs_nonterminals ys'
  | NT s :: ys' -> s :: rhs_nonterminals ys'

let rule_nonterminals ((x, ys) : bnf_rule) : string list =
  normalize_nonterminal_name x :: rhs_nonterminals ys

let nonterminals (g : bnf_grammar) : string list =
  List.sort_uniq compare (List.concat (List.map rule_nonterminals g))

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
  let clauses = List.map (fun s -> "| " ^ s) names in
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
    (List.map (fun s -> coq_match_clause s (coq_str_lit s)) names)

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
  let clauses = (List.map (fun s -> coq_match_clause (coq_str_lit s) s) names) in
  let comment = "(* This clause should be unreachable *)"                      in
  let catch_all = coq_match_clause "_" (List.hd (List.rev names))              in
  String.concat "\n" (clauses @ [comment ; catch_all])

let coq_terminalOfString_def (g : bnf_grammar) : string =
  Printf.sprintf
    ("Definition terminalOfString (s : string) : terminal :=\n" ^^
     "match s with\n"                                           ^^
     "%s\n"                                                     ^^
     "end.")
    (coq_terminalOfString_clauses (terminals g))

let coq_bnf_rule ((x, ys) : bnf_rule) : string =
  "(" ^ x ^ ", " ^ coq_list_repr (List.map coq_symbol ys) ^ ")"

let coq_grammar (g : bnf_grammar) : string =
  "[ " ^ String.concat "\n; " (List.map coq_bnf_rule g) ^ "\n]"
                                                       
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
(****************************************************************************************)  
(* FULL PIPELINE: CONVERT AN S-EXPRESSION ANTLR GRAMMAR TO A COQ SOURCE FILE            *)
(****************************************************************************************)
let main (sexp_fname : string) (coq_fname : string) : unit =
  let s  = sexp_from_file sexp_fname                                           in
  let (g_name, sexp_rules) = get_name_and_rules_from_sexp_grammar s            in
  let g = sexp_rules |> ebnf_grammar_of_rules |> bnf_of |> elim_left_recursion in
  let oc = open_out coq_fname                                                  in
  let _  = output_string oc (coq_grammar_file_contents g g_name)               in
  close_out oc

let () = main Sys.argv.(1) Sys.argv.(2)
