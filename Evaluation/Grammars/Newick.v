Require Import List QArith String.
Require Import Verbatim.Examples.Newick.Lexer.Literal.
Require Import Verbatim.Examples.Newick.Lexer.Semantic.
Require Import CoStar.Tactics CoStar.Utils CoStar.Defs CoStar.Main.
Import ListNotations.

Inductive newick_node : Type :=
| NkLeaf (label : N) (branch_length : Q)
| NkINode (descendants : list newick_node) (branch_length : Q).

Inductive newick_tree : Type :=
| NkTree : list newick_node -> newick_tree.

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
  | Trees
  | Tree
  | Subtree
  | Subtrees
  | Subtrees'
  | BranchLength.
  
  Definition nonterminal := nonterminal'.

  Definition showNT (x : nonterminal) : string :=
    match x with
    | Trees => "Trees"
    | Tree => "Tree"
    | Subtree => "Subtree"
    | Subtrees => "Subtrees"
    | Subtrees' => "Subtrees'"
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
    | Trees => list newick_tree
    | Tree => newick_tree
    | Subtree => newick_node
    | Subtrees => list newick_node
    | Subtrees' => list newick_node
    | BranchLength => Q
    end.

End Newick_Symbol_Types.

Module D <: Defs.T.
  Module        SymTy := Newick_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export Newick_Parser := Make D.

Definition newickGrammarEntries : list grammar_entry :=
  [ @existT _ _
            (Trees, [])
            (fun _ => true, fun _ => [])

  ; @existT _ _
            (Trees, [NT Tree ; NT Trees])
            (fun _ => true, fun tup =>
                              match tup with
                              | (t, (ts, _)) => t :: ts
                              end) 
  ; @existT _ _
            (Tree, [NT Subtrees ; T SEMICOLON])
            (fun _ => true, fun tup =>
                              match tup with
                              | (ts, (_, _)) => NkTree ts
                              end)
            
  ; @existT _ _ (Subtrees, [T L_PAREN ; NT Subtree ; NT Subtrees' ; T R_PAREN])
            (fun _ => true, fun tup =>
                              match tup with
                              | (_, (t, (ts, (_, _)))) => t :: ts
                              end)

  ; @existT _ _ (Subtrees', [T COMMA ; NT Subtree ; NT Subtrees'])
            (fun _ => true, fun tup =>
                              match tup with
                              | (_, (t, (ts, _))) => t :: ts
                              end)

  ; @existT _ _ (Subtrees', [])
            (fun _ => true, fun _ => [])

  ; @existT _ _ (Subtree, [NT Subtrees ; T COLON ; NT BranchLength])
            (fun _ => true, fun tup =>
                              match tup with
                              | (ts, (_, (l, _))) => NkINode ts l
                              end)

  ; @existT _ _ (Subtree, [T NAT ; T COLON ; NT BranchLength])
            (fun _ => true, fun tup =>
                              match tup with
                              | (n, (_, (l, _))) => NkLeaf n l 
                              end)

  ; @existT _ _ (BranchLength, [T NAT ; T DECIMAL_POINT ; T NAT])
            (fun _ => true, fun tup =>
                              match tup with
                              | (i, (_, (m, _))) =>
                                  let q1 :=  Z.of_N i # 1            in
                                  let q2 := (Z.of_N m # 1) / 1000000 in
                                  q1 + q2
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

Definition parse_newick       := parse (grammarOfEntryList newickGrammarEntries) (grammarOfEntryList_wf _) Trees.
Definition show_newick_result := showResult Trees.
