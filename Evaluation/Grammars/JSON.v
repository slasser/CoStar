Require Import List String.
Import ListNotations.
Require Import Verbatim.Examples.JSON.Lexer.Literal.
Require Import Verbatim.Examples.JSON.Lexer.Semantic.
Require Import CoStar.Tactics CoStar.Defs CoStar.Main.

Inductive json_value :=
| JAssoc  : list (string * json_value) -> json_value
| JBool   : bool -> json_value
| JFloat  : nat -> json_value
| JInt    : nat -> json_value
| JList   : list json_value -> json_value
| JNull   : json_value
| JString : string -> json_value.

Module JSON_Symbol_Types <: SYMBOL_TYPES.

  Definition terminal := Label.

  Definition showT (x : terminal) : string :=
    match x with
    | INT => "INT"
    | FLOAT => "FLOAT"
    | STRING => "STRING"
    | TRUE => "TRUE"
    | FALSE => "FALSE"
    | NULL => "NULL"
    | COLON => "COLON"
    | COMMA => "COMMA"
    | LEFT_BRACKET => "LEFT_BRACKET"
    | RIGHT_BRACKET => "RIGHT_BRACKET"
    | LEFT_BRACE => "LEFT_BRACE"
    | RIGHT_BRACE => "RIGHT_BRACE"
    | WS => "WS"               
    end.

  Require Import Ascii BinNat String.
  Definition ascii_compare (x y : ascii) : comparison :=
    N.compare (N_of_ascii x) (N_of_ascii y).
  
  Fixpoint strcmp (s1 s2 : string) : comparison :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _ => Lt
  | String _ _ , EmptyString => Gt
  | String c1 s1', String c2 s2' =>
    match ascii_compare c1 c2 with
    | Eq => strcmp s1' s2'
    | ne => ne
    end
  end.

  Ltac all_terminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (strcmp (showT lx) (showT ly)))
        in  exact r
    end.
  
  Definition compareT : forall (x y : terminal), comparison.
    intros x y; destruct x eqn:hx; destruct y eqn:hy; all_terminal_comparisons x y.
  Defined.
  
  Lemma compareT_eq :
    forall x y : terminal,
      compareT x y = Eq <-> x = y.
  Proof.
    intros x y; split; intros heq; destruct x; destruct y; auto; sis; tc.
  Qed.

  Lemma compareT_trans :
    forall (c : comparison) (x y z : terminal),
      compareT x y = c -> compareT y z = c -> compareT x z = c.
  Proof.
    intros c x y z h1 h2; destruct x; destruct y; destruct z; auto; sis; tc. 
  Qed.
  
  Inductive nonterminal' :=
  | Json
  | Obj
  | Pair
  | Pairs
  | Arr
  | Value
  | Values.
  
  Definition nonterminal := nonterminal'.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Json => "Json"
    | Obj => "Obj"
    | Pair => "Pair"
    | Pairs => "Pairs"
    | Arr => "Arr"
    | Value => "Value"
    | Values => "Values"
    end.

  Ltac all_nonterminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (strcmp (showNT lx) (showNT ly)))
        in  exact r
    end.

  Definition compareNT (x y : nonterminal) : comparison.
    destruct x eqn:hx; destruct y eqn:hy; all_nonterminal_comparisons x y.
  Defined.
                             
  Lemma compareNT_eq :
    forall x y : nonterminal,
      compareNT x y = Eq <-> x = y.
  Proof.
    intros x y; split; intros heq; destruct x; destruct y; auto; sis; tc.
  Qed.

  Lemma compareNT_trans :
    forall (c : comparison) (x y z : nonterminal),
      compareNT x y = c -> compareNT y z = c -> compareNT x z = c.
  Proof.
    intros c x y z h1 h2; destruct x; destruct y; destruct z; auto; sis; tc. 
  Qed.

  Definition t_semty : terminal -> Type :=
    Verbatim.Examples.JSON.Lexer.Semantic.USER.sem_ty.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Json => json_value
    | Obj => list (string * json_value)
    | Pair => string * json_value
    | Pairs => list (string * json_value)
    | Arr => list json_value
    | Value => json_value
    | Values => list json_value
  end.

End JSON_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := JSON_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export JSON_Parser := Make D.

(* to do *)
Definition jsonGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Json, [NT Value])
            (fun tup => true,
             fun tup =>
               match tup with
               | (v, _) => v
               end)
  ].
