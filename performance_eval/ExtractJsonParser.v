Require Import List String ExtrOcamlBasic ExtrOcamlString.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Main.
Import ListNotations.
Open Scope string_scope.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module Json_Types <: SYMBOL_TYPES.
  
  Inductive terminal' :=
  | Int 
  | Float 
  | Str 
  | Tru 
  | Fls 
  | Null 
  | LeftBrace 
  | RightBrace 
  | LeftBrack
  | RightBrack
  | Colon
  | Comma.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | Value 
  | Pairs
  | PairsTl
  | Pair 
  | Elts
  | EltsTl.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition showT (a : terminal) : string :=
    match a with
    | Int        => "Int"
    | Float      => "Float"
    | Str        => "String"
    | Tru        => "True"
    | Fls        => "False"
    | Null       => "Null"
    | LeftBrace  => "{"
    | RightBrace => "}" 
    | LeftBrack  => "["
    | RightBrack => "]"
    | Colon      => ":"
    | Comma      => ","
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Value    => "value"
    | Pairs    => "pairs"
    | PairsTl  => "pairs_tl"
    | Pair     => "pair"
    | Elts     => "elts"
    | EltsTl   => "elts_tl"
    end.

End Json_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export D <: Defs.T.
  Module Export SymTy := Json_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

(* The parser generator itself. *)
Module Export PG := Make D.

Open Scope list_scope.

(* The JSON grammar itself *)
Definition jsonGrammar : grammar :=
  [
    (* association list rule *)
    (Value, [T LeftBrace; NT Pairs; T RightBrace]);
    
    (* list rule *)
    (Value, [T LeftBrack; NT Elts; T RightBrack]);
    
    (* string rule *)
    (Value, [T Str]);
    
    (* int rule *)
    (Value, [T Int]);

    (* float rule *)
    (Value, [T Float]);

    (* true rule *)
    (Value, [T Tru]);
    
    (* false rule *)
    (Value, [T Fls]);

    (* null rule *)
    (Value, [T Null]);

    (Pairs, []);
    
    (Pairs, [NT Pair; NT PairsTl]);

    (PairsTl, []);
    
    (PairsTl, [T Comma; NT Pair; NT PairsTl]);

    (Pair, [T Str; T Colon; NT Value]);

    (Elts, []);

    (Elts, [NT Value; NT EltsTl]);

    (EltsTl, []);

    (EltsTl, [T Comma; NT Value; NT EltsTl])
  ].

Extraction "performance_eval/myJsonParser.ml" D PG jsonGrammar.