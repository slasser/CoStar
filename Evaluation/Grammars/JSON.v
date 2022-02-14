Require Import BinInt List String.
Import ListNotations.
Require Import Verbatim.Examples.JSON.Lexer.Literal.
Require Import Verbatim.Examples.JSON.Lexer.Semantic.
Require Import CoStar.Tactics CoStar.Utils CoStar.Defs CoStar.Main.
Require Import OrderedTypeEx.

Module StringSet := FSetAVL.Make String_as_OT.

Fixpoint nodupKeys' {A : Type} (prs : list (string * A)) (seen : StringSet.t) : bool :=
  match prs with
  | [] => true
  | (s, _) :: prs' =>
      if StringSet.mem s seen
      then false
      else nodupKeys' prs' (StringSet.add s seen)
  end.

Definition nodupKeys {A : Type} (prs : list (string * A)) : bool :=
  nodupKeys' prs StringSet.empty.

Inductive json_value :=
| JAssoc  : list (string * json_value) -> json_value
| JBool   : bool -> json_value
| JFloat  : Z -> json_value
| JInt    : Z -> json_value
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

  Ltac all_terminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (cmpString (showT lx) (showT ly)))
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
        let r := eval compute in (cmpString (showNT lx) (showNT ly))
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

Definition jsonGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Json, [NT Value])
            (fun _ => true,
             fun tup =>
               match tup with
               | (v, _) => v
               end)
  ; @existT _ _
            (Obj, [T LEFT_BRACE ; NT Pair ; NT Pairs ; T RIGHT_BRACE])
            (fun _ => true,
             fun tup =>
               match tup with
               | (_, (pr, (prs, (_, _)))) => pr :: prs
               end)

  ; @existT _ _
            (Obj, [T LEFT_BRACE ; T RIGHT_BRACE])
            (fun _ => true,
             fun _ => [])
            
  ; @existT _ _
            (Pairs, [T COMMA ; NT Pair ; NT Pairs])
            (fun _ => true,
             fun tup =>
               match tup with
               | (_, (pr, (prs, _))) => pr :: prs
               end)

  ; @existT _ _
            (Pairs, [])
            (fun _ => true,
             fun _ => [])

    ; @existT _ _
              (Pair, [T STRING ; T COLON ; NT Value])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (s, (_, (v, _))) => (s, v)
                   end)

    ; @existT _ _
              (Arr, [T LEFT_BRACKET ; NT Value ; NT Values ; T RIGHT_BRACKET])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (_, (v, (vs, (_, _)))) => v :: vs
                   end)

    ; @existT _ _
              (Arr, [T LEFT_BRACKET ; T RIGHT_BRACKET])
              (fun _ => true,
                 fun _ => [])

    ; @existT _ _
              (Values, [T COMMA ; NT Value ; NT Values])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (_, (v, (vs, _))) => v :: vs
                   end)

    ; @existT _ _
              (Values, [])
              (fun _ => true,
                 fun _ => [])

    ; @existT _ _
              (Value, [T STRING])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (s, _) => JString s
                   end)

    ; @existT _ _
              (Value, [T INT])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (i, _) => JInt i
                   end)

    ; @existT _ _
              (Value, [T FLOAT])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (i, _) => JFloat i
                   end)

    ; @existT _ _
              (Value, [NT Obj])
              (fun tup =>
                 match tup with
                 | (prs, _) => nodupKeys prs
                 end,
                 fun tup =>
                   match tup with
                   | (prs, _) => JAssoc prs
                   end)

    ; @existT _ _
              (Value, [NT Arr])
              (fun _ => true,
                 fun tup =>
                   match tup with
                   | (vs, _) => JList vs
                   end)

    ; @existT _ _
              (Value, [T TRUE])
              (fun _ => true, fun _ => JBool true)

    ; @existT _ _
              (Value, [T FALSE])
              (fun _ => true, fun _ => JBool false)

    ; @existT _ _
              (Value, [T NULL])
              (fun _ => true, fun _ => JNull) 
    
  ].

Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ WS _ => false
  | _ => true
  end.

Definition lex_sem   := Verbatim.Examples.JSON.Lexer.Semantic.SemLexer.Impl.lex_sem.
Definition lex_rus   := Verbatim.Examples.JSON.Lexer.Literal.rus.
Definition lex_json' := lex_sem lex_rus.
Definition lex_json (s : String) : option (list token) * String :=
  let res' := lex_json' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

Definition parse_json       := parse (grammarOfEntryList jsonGrammarEntries) (grammarOfEntryList_wf _) Json.
Definition show_json_result := showResult Json.
