Require Import Floats String.
Require Import Verbatim.Examples.Newick.Lexer.Literal.
Require Import Verbatim.Examples.Newick.Lexer.Semantic.
Require Import CoStar.Defs CoStar.Main.

Inductive newick_tree : Type :=
| NewickLeaf (label : nat) (branch_length : Decimal.decimal)
| NewickNode (descendants : list newick_tree) (branch_length : Decimal.decimal).

Module Newick_Symbol_Types <: SYMBOL_TYPES.

  Definition terminal := Label.

  Definition showT (x : terminal) : string :=
    match x with
    | NAT => "NAT"
    | COLON => "COLON"
    | COMMA => "COMMA"
    | DECIMAL_POINT => "DECIMAL_POINT"
    | L_PAREN => "L_PAREN"
    | R_PAREN => "R_PAREN"
    | SEMICOLON => "SEMICOLON"
    | WS => "WS"               
    end.

  Require Import CoStar.Tactics CoStar.Utils.

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
  | Root
  | Tree
  | Trees
  | Trees'
  | BranchLength.
  
  Definition nonterminal := nonterminal'.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Root => "Root"
    | Tree => "Tree"
    | Trees => "Trees"
    | Trees' => "Trees'"
    | BranchLength => "BranchLength"
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
    Verbatim.Examples.Newick.Lexer.Semantic.USER.sem_ty.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Root => list newick_tree
    | Tree => newick_tree
    | Trees => list newick_tree
    | Trees' => list newick_tree
    | BranchLength => Decimal.decimal
    end.

End Newick_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := Newick_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export Newick_Parser := Make D.
Require Import List.
Import ListNotations.

Definition newickGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Root, [NT Trees ; T SEMICOLON])
            (fun _ => true, fun tup =>
                              match tup with
                              | (ts, (_, _)) => ts
                              end)
    ; @existT _ _ (Trees, [T L_PAREN ; NT Tree ; NT Trees' ; T R_PAREN])
              (fun _ => true, fun tup =>
                                match tup with
                                | (_, (t, (ts, (_, _)))) => t :: ts
                                end)

    ; @existT _ _ (Trees', [T COMMA ; NT Tree ; NT Trees'])
              (fun _ => true, fun tup =>
                                match tup with
                                | (_, (t, (ts, _))) => t :: ts
                                end)

    ; @existT _ _ (Trees', [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Tree, [NT Trees ; T COLON ; NT BranchLength])
              (fun _ => true, fun tup =>
                                match tup with
                                | (ts, (_, (l, _))) => NewickNode ts l
                                end)

    ; @existT _ _ (Tree, [T NAT ; T COLON ; NT BranchLength])
              (fun _ => true, fun tup =>
                                match tup with
                                | (n, (_, (l, _))) => NewickLeaf n l
                                end)
              (* INCORRECT -- change *)
    ; @existT _ _ (BranchLength, [T NAT ; T DECIMAL_POINT ; T NAT])
              (fun _ => true, fun tup =>
                                match tup with
                                | (i, (_, (m, _))) => Decimal.Decimal (Nat.to_int i) (Nat.to_uint m)
                                end)
                                    
    
  ].

Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ WS _ => false
  | _ => true
  end.

Definition lex_sem   := Verbatim.Examples.Newick.Lexer.Semantic.SemLexer.Impl.lex_sem.
Definition lex_rus   := Verbatim.Examples.Newick.Lexer.Literal.rus.
Definition lex_newick' := lex_sem lex_rus.
Definition lex_newick (s : String) : option (list token) * String :=
  let res' := lex_newick' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

Definition parse_newick       := parse (grammarOfEntryList newickGrammarEntries) (grammarOfEntryList_wf _) Root.
Definition show_newick_result := showResult Root.