Require Import FMaps List MSets PeanoNat String.
Require Import GallStar.Tactics.
Import ListNotations.

(* Representations of grammar symbols *)
Definition terminal    := string.
Definition nonterminal := nat.
Inductive symbol       := T  : terminal -> symbol 
                        | NT : nonterminal -> symbol.

Lemma t_eq_dec : forall a a' : terminal,
    {a = a'} + {a <> a'}.
Proof. repeat decide equality. Defined.

Lemma nt_eq_dec : forall x x' : nonterminal,
    {x = x'} + {x <> x'}.
Proof. decide equality. Defined.

Lemma gamma_eq_dec : forall gamma gamma' : list symbol,
    {gamma = gamma'} + {gamma <> gamma'}.
Proof. repeat decide equality. Defined.

Definition beqGamma (xs ys : list symbol) : bool :=
  if gamma_eq_dec xs ys then true else false.

(* Finite sets of nonterminals *)
Module MDT_NT.
  Definition t      := nonterminal.
  Definition eq_dec := Nat.eq_dec.
End MDT_NT.
Module NT_as_DT   := Make_UDT(MDT_NT).
Module NtSet      := MSetWeakList.Make NT_as_DT.
Module Export NF  := WFactsOn NT_as_DT NtSet.
Module Export NP  := MSetProperties.Properties NtSet.
Module Export NE  := EqProperties NtSet.
Module Export ND  := WDecideOn NT_as_DT NtSet.

(* Grammar-related definitions *)               
Definition production := (nonterminal * list symbol)%type.            
Definition grammar    := list production.

Definition lhs (p : production) : nonterminal :=
  let (x, _) := p in x.

Definition lhss (g : grammar) : list nonterminal :=
  map lhs g.

Definition rhs (p : production) : list symbol :=
  let (_, gamma) := p in gamma.

Definition rhss (g : grammar) : list (list symbol) :=
  map rhs g.

Fixpoint rhssForNt (ps : list production) (x : nonterminal) : list (list symbol) :=
  match ps with
  | []                 => []
  | (x', gamma) :: ps' => 
    if nt_eq_dec x' x then 
      gamma :: rhssForNt ps' x
    else 
      rhssForNt ps' x
  end.

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition allNts (g : grammar) : NtSet.t := 
  fromNtList (lhss g).

(* Definitions related to input that the parser consumes. *)
Definition literal := string.
Definition token   := (terminal * literal)% type.

(* Parser return values *)
Inductive tree    := Leaf : literal -> tree
                   | Node : nonterminal -> list tree -> tree.

Definition forest := list tree.

(* LL(1)-related definitions -- THESE WILL GET DELETED *)
Inductive lookahead := LA : terminal -> lookahead 
                     | EOF : lookahead.

Definition pt_key := (nonterminal * lookahead)%type.

Definition pt_key_eq_dec :
  forall k k2 : pt_key,
    {k = k2} + {k <> k2}.
Proof. repeat decide equality. Defined.

Module MDT_PtKey.
  Definition t := pt_key.
  Definition eq_dec := pt_key_eq_dec.
End MDT_PtKey.

Module PtKey_as_DT := Make_UDT(MDT_PtKey).

Module ParseTable := FMapWeakList.Make PtKey_as_DT.

Definition parse_table := ParseTable.t (list symbol).

Definition peek (input : list token) : lookahead :=
  match input with
  | nil => EOF
  | (a, lit) :: _ => LA a
  end.

Definition ntKeys (tbl : parse_table) : list nonterminal :=
  List.map (fun pr => match pr with 
                      | ((x, _), _) => x
                      end)
           (ParseTable.elements tbl).

Definition fromNtList' (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition allNts' (tbl : parse_table) : NtSet.t := 
  fromNtList (ntKeys tbl).

Definition entryLengths (tbl : parse_table) : list nat :=
  List.map (fun pr => match pr with
                      | (_, gamma) => List.length gamma
                      end)
           (ParseTable.elements tbl).

Definition listMax (xs : list nat) : nat := 
  fold_right max 0 xs.

Definition maxEntryLength (tbl : parse_table) : nat :=
  listMax (entryLengths tbl).

(* Grammar locations *)
Record location := Loc { lopt : option nonterminal
                       ; rpre : list symbol
                       ; rsuf : list symbol
                       }.

(* Semantic value stacks *)
Definition sem_stack  := (forest * list forest)%type.

Inductive sym_derivation (g : grammar) : symbol -> list token -> tree -> Prop :=
| T_der  : 
    forall (a : terminal) (l : literal),
      sym_derivation g (T a) [(a, l)] (Leaf l)
| NT_der : 
    forall (x  : nonterminal) (ys : list symbol) (w : list token) (sts : forest),
      In (x, ys) g
      -> gamma_derivation g ys w sts
      -> sym_derivation g (NT x) w (Node x sts)
with gamma_derivation (g : grammar) : list symbol -> list token-> forest-> Prop :=
     | Nil_der  : 
         gamma_derivation g [] [] []
     | Cons_der : 
         forall (s : symbol) (ss : list symbol) (wpre wsuf : list token) 
                (tr : tree) (trs : list tree),
           sym_derivation g s wpre tr
           -> gamma_derivation g ss wsuf trs
           -> gamma_derivation g (s :: ss) (wpre ++ wsuf) (tr :: trs).

Hint Constructors sym_derivation gamma_derivation.

(* LEMMAS *)

Lemma in_rhssForNt_production_in_grammar :
  forall g x ys,
    In ys (rhssForNt g x)
    -> In (x, ys) g.
Proof.
  intros g x ys hin.
  induction g as [| (x', ys') g]; sis; tc.
  destruct (nt_eq_dec x' x); subst; auto.
  inv hin; auto.
Qed.
