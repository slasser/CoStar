Require Import List Floats String.
Require Import Verbatim.Examples.XML.Lexer.Literal.
Require Import Verbatim.Examples.XML.Lexer.Semantic.
Require Import CoStar.Tactics CoStar.Utils CoStar.Defs CoStar.Main.
Import ListNotations.

Inductive xml_tree : Type :=
| XmlNode (name : string) (attrs : list (string * string)) (children : list xml_tree)
| XmlLeaf (name : string) (attrs : list (string * string)).

Inductive xml_document : Type :=
| XmlDocument (attrs : list (string * string)) (elt : xml_tree).

Module XML_Symbol_Types <: SYMBOL_TYPES.

  Definition terminal := Label.

  Definition showT (x : terminal) : string :=
    match x with
    | OPEN => "OPEN"
    | XMLDeclOpen => "XMLDeclOpen"
    | CLOSE => "CLOSE"
    | SPECIAL_CLOSE => "SPECIAL_CLOSE"
    | SLASH_CLOSE => "SLASH_CLOSE"
    | SLASH => "SLASH"
    | EQUALS => "EQUALS"
    | STRING => "STRING"
    | NAME => "NAME"
    | SEA_WS => "SEA_WS"
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
  | Document
  | Prolog_opt
  | Prolog
  | Content
  | Element
  | Attrs
  | Attr.

  Definition nonterminal := nonterminal'.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Document => "Document"
    | Prolog_opt => "Prolog_opt"
    | Prolog => "Prolog"
    | Content => "Content"
    | Element => "Element"
    | Attrs => "Attrs"
    | Attr => "Attr"
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
    Verbatim.Examples.XML.Lexer.Semantic.USER.sem_ty.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Document => xml_document
    | Prolog_opt => list (string * string)
    | Prolog => list (string * string)
    | Content => list xml_tree
    | Element => xml_tree
    | Attrs => list (string * string)
    | Attr => string * string
    end.

End XML_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := XML_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export XML_Parser := Make D.

Definition xmlGrammarEntries : list grammar_entry :=
  [

    @existT _ _ (Document, [NT Prolog_opt ; NT Element])
            (fun _ => true, fun tup => match tup with
                                       | (attrs, (elt, _)) => XmlDocument attrs elt
                                       end)

    ; @existT _ _ (Prolog_opt, [NT Prolog])
              (fun _ => true, fun tup => match tup with
                                         | (attrs, _) => attrs
                                         end)

    ; @existT _ _ (Prolog_opt, [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Prolog, [T XMLDeclOpen ; NT Attrs ; T SPECIAL_CLOSE])
              (fun _ => true, fun tup => match tup with
                                         | (_, (attrs, (_, _))) => attrs
                                         end)

    ; @existT _ _ (Attrs, [NT Attr ; NT Attrs])
              (fun _ => true, fun tup => match tup with
                                         | (x, (xs, _)) => x :: xs
                                         end)

    ; @existT _ _ (Attrs, [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Content, [NT Element ; NT Content])
              (fun _ => true, fun tup => match tup with
                                         | (t, (ts, _)) => t :: ts
                                         end)

    ; @existT _ _ (Content, [])
              (fun _ => true, fun _ => [])

              (* to do : add constraint *)
    ; @existT _ _ (Element, [T OPEN ; T NAME ; NT Attrs ; T CLOSE ; NT Content ; T OPEN ; T SLASH ; T NAME ; T CLOSE])
              (fun _ => true, fun tup => match tup with
                                         | (_, (nm, (attrs, (_, (ts, (_, (_, (nm', (_, _))))))))) => XmlNode nm attrs ts
                                         end)

    ; @existT _ _ (Element, [T OPEN ; T NAME ; NT Attrs ; T SLASH_CLOSE])
              (fun _ => true, fun tup => match tup with
                                         | (_, (nm, (attrs, (_, _)))) => XmlLeaf nm attrs
                                         end)

    ; @existT _ _ (Attr, [T NAME ; T EQUALS ; T STRING])
              (fun _ => true, fun tup => match tup with
                                         | (nm, (_, (s, _))) => (nm, s)
                                         end)

  ].

Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ SEA_WS _ => false
  | _ => true
  end.

Definition lex_sem   := Verbatim.Examples.XML.Lexer.Semantic.SemLexer.Impl.lex_sem.
Definition lex_rus   := Verbatim.Examples.XML.Lexer.Literal.rus.
Definition lex_xml'  := lex_sem lex_rus.
Definition lex_xml (s : String) : option (list token) * String :=
  let res' := lex_xml' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

Definition parse_xml       := parse (grammarOfEntryList xmlGrammarEntries) (grammarOfEntryList_wf _) Document.
Definition show_xml_result := showResult Document.
