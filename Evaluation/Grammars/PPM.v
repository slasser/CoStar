Require Import BinNat Bool List NArith PeanoNat String.
Import ListNotations.
Require Import Verbatim.Examples.PPM.Lexer.Literal.
Require Import Verbatim.Examples.PPM.Lexer.Semantic.
Require Import CoStar.Tactics CoStar.Defs CoStar.Main.

Record rgb_triple : Type :=
  mkRGBTriple { red   : N
              ; green : N
              ; blue  : N
              }.

Definition triple_le_max (t : rgb_triple) (m : N) : bool :=
  match t with
  | mkRGBTriple r g b =>
      (r <=? m)%N && (g <=? m)%N && (b <=? m)%N
  end.

Fixpoint triples_le_max (ts : list rgb_triple) (m : N) : bool :=
  match ts with
  | [] => true
  | t :: ts' => triple_le_max t m && triples_le_max ts' m
  end.

Definition width_x_height_eq_length {A : Type} (w h : N) (l : list A) : bool :=
  (w * h =? N.of_nat (List.length l))%N.

Record ppm_value : Type :=
  mkPPMValue { width   : N
             ; height  : N
             ; max     : N
             ; triples : list rgb_triple
             }.  

Module PPM_Symbol_Types <: SYMBOL_TYPES.

  Definition terminal := Label.

  Definition compareT (x y : terminal) : comparison :=
    match x, y with
    | NAT, NAT => Eq
    | NAT, _ => Lt
    | P3, NAT => Gt
    | P3, P3 => Eq
    | P3, WS => Lt
    | WS, WS => Eq
    | WS, _ => Gt
    end.

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
  | Triples.

  Definition nonterminal := nonterminal'.

  Definition compareNT (x y : nonterminal) : comparison :=
    match x, y with
    | Document, Triples => Lt
    | Triples, Document => Gt
    | _, _ => Eq
    end.
                             
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
  
  Definition showT (x : terminal) : string :=
    match x with
    | P3 => "P3"
    | NAT => "NAT"
    | WS => "WS"
    end.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Document => "Document"
    | Triples => "Triples"
    end.

  Definition t_semty : terminal -> Type :=
    Verbatim.Examples.PPM.Lexer.Semantic.USER.sem_ty.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Document => ppm_value
    | Triples  => list rgb_triple
    end.

End PPM_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := PPM_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export PPM_Parser := Make D.

Definition ppmGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Document, [T P3; T NAT ; T NAT ; T NAT ; NT Triples])
            (fun tup =>
               match tup with
               | (_, (w, (h, (m, (ts, _))))) =>
                   width_x_height_eq_length w h ts && triples_le_max ts m
               end,
             fun tup =>
               match tup with
               | (_, (w, (h, (m, (ts, _))))) =>
                 mkPPMValue w h m ts
               end)
            
  ; @existT _ _
            (Triples, [])
            (fun _ => true, fun _ => [])
            
  ; @existT _ _
            (Triples, [T NAT; T NAT; T NAT; NT Triples])
            (fun _ => true,
             fun tup =>
               match tup with
               | (x, (y, (z, (tpls, _)))) =>
                 mkRGBTriple x y z :: tpls
               end)
  ].

Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ WS _ => false
  | _ => true
  end.

Definition lex_sem  := Verbatim.Examples.PPM.Lexer.Semantic.SemLexer.Impl.lex_sem.
Definition lex_rus  := Verbatim.Examples.PPM.Lexer.Literal.rus.
Definition lex_ppm' := lex_sem lex_rus.
Definition lex_ppm  (s : String) : option (list token) * String :=
  let res' := lex_ppm' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

Definition parse_ppm       := parse (grammarOfEntryList ppmGrammarEntries) (grammarOfEntryList_wf _) Document.
Definition show_ppm_result := PPM_Parser.ParserAndProofs.PEF.PS.P.showResult Document.
