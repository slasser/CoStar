Require Import Floats String.
Require Import Verbatim.Examples.Newick.Lexer.Literal.
Require Import Verbatim.Examples.Newick.Lexer.Semantic.
Require Import CoStar.Defs CoStar.Main.

Inductive newick_tree : Type :=
| Leaf (label : nat) (branch_length : float)
| Node (descendants : list newick_tree) (label : nat) (branch_length : float).

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
  | Subtree
  | SubtreeList
  | BranchLength.
  
  Definition nonterminal := nonterminal'.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Root => "Root"
    | Subtree => "Subtree"
    | SubtreeList => "SubtreeList"
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
    | Subtree => newick_tree
    | SubtreeList => list newick_tree
    | BranchLength => float
    end.

End Newick_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := Newick_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export Newick_Parser := Make D.


