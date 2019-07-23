Require Import List.
Require Import Tactics.
Import ListNotations.

Lemma in_singleton_eq :
  forall A (x x' : A), In x' [x] -> x' = x.
Proof.
  intros A x x' Hin.
  destruct Hin as [Hhd | Htl]; auto.
  inv Htl.
Qed.