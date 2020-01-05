Require Import List String ExtrOcamlBasic ExtrOcamlString.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Import ListNotations.
Open Scope string_scope.

(* JSON terminals *)
Definition Int        := "Int".
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
Definition Value   := 0.
Definition Pairs   := 1.
Definition PairsTl := 2.
Definition Pair    := 3.
Definition Elts    := 4.
Definition EltsTl  := 5.

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

(* { "bateman":50, "alexander":60 } *)
Definition tokens := [ (LeftBrace, "")
                     ; (Str, "Bateman")
                     ; (Colon, "")
                     ; (Int, "50")
                     ; (Comma, "")
                     ; (Str, "Alexander")
                     ; (Colon, "")
                     ; (Int, "60")
                     ; (RightBrace, "")
                     ].

(* next step: change lemmas from Qed to Defined so that parse can simplify. *)

Lemma mkIniteState_test :
  mkInitState jsonGrammar [NT Value] tokens =
  Pst (allNts jsonGrammar)
      (Fr (Loc None [] [NT Value]) [], [])
      tokens
      true.
Proof. auto. Qed.

Definition init_st := 
  Pst (allNts jsonGrammar)
      (Fr (Loc None [] [NT Value]) [], [])
      tokens
      true.

(* simpl seems to diverge *)
Lemma test :
  parse jsonGrammar [NT Value] tokens = Accept [Node Value []].
Proof.
  unfold parse.
  auto.
Abort.

Extraction "myJsonParser.ml" jsonGrammar parse.