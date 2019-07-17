Require Import FMaps MSets PeanoNat String.

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

(* Finite sets of nonterminals *)
Module MDT_NT.
  Definition t      := nonterminal.
  Definition eq_dec := Nat.eq_dec.
End MDT_NT.
Module NT_as_DT   := Make_UDT(MDT_NT).
Module NtSet      := MSetWeakList.Make NT_as_DT.
Module Export NF  := WFactsOn NT_as_DT NtSet.
Module Export NP  := MSetProperties.Properties NtSet.
Module Export NEP := EqProperties NtSet.
Module Export ND  := WDecideOn NT_as_DT NtSet.

(* Grammar-related definitions *)               
Definition production := (nonterminal * list symbol)%type.            
Definition grammar    := list production.

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

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition allNts (tbl : parse_table) : NtSet.t := 
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

Record parser_frame := parserFrame { syms    : list symbol
                                   ; sem_val : forest
                                   }.

Definition parser_stack := (parser_frame * list parser_frame)%type.

Record parser_state := parserState { avail  : NtSet.t
                                   ; stack  : parser_stack 
                                   ; tokens : list token
                                   }.


