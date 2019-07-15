Require Import MSets PeanoNat String.

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

(* Generally useful definitions *)
Definition id A (x : A) := x.