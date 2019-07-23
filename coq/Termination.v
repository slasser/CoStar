Require Import Arith List Omega.
Require Import Defs.
Import ListNotations.

(* Definitions related to well-founded measures *)

Definition headFrameSize (fr : l_frame) : nat :=
  List.length (symbolsToProcess fr).

Definition headFrameScore (fr : l_frame) (b : nat) (e : nat) : nat :=
  headFrameSize fr * (b ^ e).

Definition tailFrameSize (fr : l_frame) : nat :=
  match (symbolsToProcess fr) with
  | []        => 0
  | _ :: suf' => List.length suf'
  end.

Definition tailFrameScore (fr : l_frame) (b : nat) (e : nat) : nat :=
  tailFrameSize fr * (b ^ e).

Fixpoint tailFramesScore (frs : list l_frame) (b : nat) (e : nat) : nat :=
  match frs with
  | []         => 0
  | fr :: frs' => tailFrameScore fr b e + tailFramesScore frs' b (1 + e)
  end.

Definition stackScore (stk : l_stack) (b : nat) (e : nat) : nat :=
  let (h_fr, t_frs) := stk
  in  headFrameScore h_fr b e + tailFramesScore t_frs b (1 + e).

Definition stackHeight (stk : l_stack) : nat :=
  let (_, frs) := stk in List.length frs.

Definition rhsLengths (g : grammar) : list nat :=
  map (fun rhs => List.length rhs) (rhss g).

Definition maxRhsLength (g : grammar) : nat :=
  listMax (rhsLengths g).

(* Termination-related lemmas *)

Lemma nonzero_exponents_lt_powers_le :
  forall b e1 e2, 0 < e1 < e2 -> b ^ e1 <= b ^ e2.
Proof.
  intros b e1 e2 [Hlt Hlt']. 
  destruct b as [| b']. 
  - destruct e1; destruct e2; auto.
    omega.
  - destruct b' as [| b''].
    + repeat rewrite Nat.pow_1_l; auto.
    + pose proof Nat.pow_lt_mono_r. 
      specialize (H (S (S b'')) e1 e2). 
      assert (fact : forall n m, n < m -> n <= m) by (intros; omega).
      apply fact.
      apply Nat.pow_lt_mono_r; auto.
      omega.
Qed.

Lemma nonzero_exponents_lt_tailFrameScore_le :
  forall fr b e1 e2,
    0 < e1 < e2
    -> tailFrameScore fr b e1 <= tailFrameScore fr b e2.
Proof.
  intros fr b e1 e2 Hlt.
  unfold tailFrameScore. 
  apply Nat.mul_le_mono_l.
  apply nonzero_exponents_lt_powers_le; auto.
Qed.

Lemma nonzero_exponents_lt_tailFramesScore_le :
  forall frs b e1 e2,
    0 < e1 < e2
    -> tailFramesScore frs b e1 <= tailFramesScore frs b e2.
Proof.
  intros frs.
  induction frs as [| fr frs IH]; intros b e1 e2 Hlt; simpl; auto.
  apply plus_le_compat.
  - apply nonzero_exponents_lt_tailFrameScore_le; auto.
  - apply IH; omega.
Qed.

Lemma nonzero_exponents_lt_stackScore_le :
  forall v b e1 e2 e3 e4 frs,
    0 < e1 < e2
    -> 0 < e3 < e4
    -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
       v * (b ^ e2) + tailFramesScore frs b e4.
Proof.
  intros v b e1 e2 e3 e4 frs [H0e1 He1e2] [H0e3 He3e4].
  apply plus_le_compat.
  - apply Nat.mul_le_mono_l. 
    apply nonzero_exponents_lt_powers_le; auto.
  - apply nonzero_exponents_lt_tailFramesScore_le; auto.
Qed.

Lemma mem_true_cardinality_neq_0 :
  forall x s,
    NtSet.mem x s = true -> NtSet.cardinal s <> 0.
Proof.
  intros x s Hm; unfold not; intros Heq.
  rewrite NtSet.mem_spec in Hm.
  apply cardinal_inv_1 in Heq.
  unfold NtSet.Empty in Heq. 
  eapply Heq; eauto.
Qed.

Lemma mem_true_cardinality_gt_0 :
  forall x s,
    NtSet.mem x s = true -> 0 < NtSet.cardinal s.
Proof.
  intros x s Hm.
  apply mem_true_cardinality_neq_0 in Hm; omega.
Qed.

Lemma stackScore_le_after_return :
  forall callee caller caller' x av frs b,
    symbolsToProcess callee = []
    -> symbolsToProcess caller = NT x :: symbolsToProcess caller'
    -> stackScore (caller', frs) b (NtSet.cardinal (NtSet.add x av)) <= stackScore (callee, caller :: frs) b (NtSet.cardinal av).
Proof.
  intros callee caller caller' x av frs b Hcallee Hcaller.
  unfold stackScore. 
  unfold headFrameScore; unfold headFrameSize; rewrite Hcallee; simpl; clear Hcallee.
  unfold tailFrameScore; unfold tailFrameSize; rewrite Hcaller; clear Hcaller.
  destruct (NtSet.mem x av) eqn:Hm.
  - rewrite add_cardinal_1; auto.
    eapply nonzero_exponents_lt_stackScore_le.
    + split; auto.
      eapply mem_true_cardinality_gt_0; eauto.
    + split; omega.
  - rewrite add_cardinal_2; auto.
Qed.