Require Import List String ExtrOcamlBasic ExtrOcamlString.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Main.
Import ListNotations.
Open Scope string_scope.

(* JSON terminals *)
Definition JInt       := "Int".
Definition Float      := "Float".
Definition Str        := "Str".
Definition Tru        := "Tru".
Definition Fls        := "Fls".
Definition Null       := "Null".
Definition LeftBrace  := "LeftBrace".
Definition RightBrace := "RightBrace".
Definition LeftBrack  := "LeftBrack".
Definition RightBrack := "RightBrack".
Definition Colon      := "Colon".
Definition Comma      := "Comma".

(* JSON nonterminals *)
Definition Value   := 1.
Definition Pairs   := 2.
Definition PairsTl := 3.
Definition Pair    := 4.
Definition Elts    := 5.
Definition EltsTl  := 6.

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
    (Value, [T JInt]);

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

(* { "bateman":50, "alexander":60 } *)
Definition tokens := [ (LeftBrace, "")
                     ; (Str, "Bateman")
                     ; (Colon, "")
                     ; (JInt, "50")
                     ; (Comma, "")
                     ; (Str, "Alexander")
                     ; (Colon, "")
                     ; (JInt, "60")
                     ; (RightBrace, "")
                     ].

Definition tokens' := [ (Tru, "")].

Extraction "performance_eval/myJsonParser.ml" jsonGrammar parseSymbol.