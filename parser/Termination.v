Require Import Arith List Omega.
Require Import CoStar.Defs.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module TerminationFn (Export D : Defs.T).

  (* Definitions related to well-founded measures *)

  Definition headFrameSize (fr : suffix_frame) : nat :=
    match fr with
    | SF _ suf => length suf
    end.

  Definition headFrameScore (fr : suffix_frame) (b : nat) (e : nat) : nat :=
    headFrameSize fr * (b ^ e).

  Definition tailFrameSize (fr : suffix_frame) : nat :=
    match fr with
    | SF _ []          => 0
    | SF _ (_ :: suf') => length suf'
    end.

  Definition tailFrameScore (fr : suffix_frame) (b : nat) (e : nat) : nat :=
    tailFrameSize fr * (b ^ e).

  Fixpoint tailFramesScore (frs : list suffix_frame) (b : nat) (e : nat) : nat :=
    match frs with
    | []         => 0
    | fr :: frs' => tailFrameScore fr b e + tailFramesScore frs' b (1 + e)
    end.

  Definition stackScore (stk : suffix_stack) (b : nat) (e : nat) : nat :=
    let (fr, frs) := stk in
    headFrameScore fr b e + tailFramesScore frs b (1 + e).

  Definition stackHeight {A} (stk : A * list A) : nat :=
    let (_, frs) := stk in length frs.

  (* Termination-related lemmas *)
  
  Lemma nonzero_exponents_le__powers_le :
    forall b e1 e2,
      0 < e1 <= e2
      -> b ^ e1 <= b ^ e2.
  Proof.
    intros b e1 e2 [Hlt Hlt']. 
    destruct b as [| b']. 
    - destruct e1; destruct e2; auto; omega.
    - apply Nat.pow_le_mono_r; auto. 
  Qed.
  
  Lemma nonzero_exponents_le__tailFrameScore_le :
    forall fr b e1 e2,
      0 < e1 <= e2
      -> tailFrameScore fr b e1 <= tailFrameScore fr b e2.
  Proof.
    intros fr b e1 e2 Hlt.
    unfold tailFrameScore. 
    apply Nat.mul_le_mono_l.
    apply nonzero_exponents_le__powers_le; auto.
  Qed.

  Lemma nonzero_exponents_le__tailFramesScore_le :
    forall frs b e1 e2,
      0 < e1 <= e2
      -> tailFramesScore frs b e1 <= tailFramesScore frs b e2.
  Proof.
    intros frs.
    induction frs as [| fr frs' IH]; intros b e1 e2 Hlt; simpl; auto.
    apply plus_le_compat.
    - apply nonzero_exponents_le__tailFrameScore_le; auto.
    - apply IH; omega.
  Qed.

  Lemma nonzero_exponents_le__stackScore_le :
    forall v b e1 e2 e3 e4 frs,
      0 < e1 <= e2
      -> 0 < e3 <= e4
      -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
         v * (b ^ e2) + tailFramesScore frs b e4.
  Proof.
    intros v b e1 e2 e3 e4 frs [H0e1 He1e2] [H0e3 He3e4].
    apply plus_le_compat.
    - apply Nat.mul_le_mono_l. 
      apply nonzero_exponents_le__powers_le; auto.
    - apply nonzero_exponents_le__tailFramesScore_le; auto.
  Qed.

  Lemma mem_true_cardinality_neq_0 :
    forall x s,
      NtSet.mem x s = true -> NtSet.cardinal s <> 0.
  Proof.
    intros x s Hm; unfold not; intros Heq.
    apply NF.mem_iff in Hm.
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

  Lemma cardinal_diff_remove_gt_0 :
    forall x s s',
      NtSet.In x s
      -> 0 < NtSet.cardinal (NtSet.diff s (NtSet.remove x s')).
  Proof.
    intros x s s' hm.
    apply mem_true_cardinality_gt_0 with (x := x).
    apply NF.mem_iff; ND.fsetdec.
  Qed.

  Lemma cardinal_diff_gt_0 :
    forall x s s',
      NtSet.In x s
      -> ~ NtSet.In x s'
      -> 0 < NtSet.cardinal (NtSet.diff s s').
  Proof.
    intros x s s' hi hn.
    apply mem_true_cardinality_gt_0 with (x := x).
    apply NF.mem_iff; ND.fsetdec.
  Qed.

  Lemma diff_remove_equal_add_diff :
    forall x s s',
      NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s'))
                     (NtSet.add x (NtSet.diff s s')).
  Proof.
    intros; ND.fsetdec.
  Qed.

  Lemma diff_remove_equal_diff_1 :
    forall x s s',
      ~ NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s')) (NtSet.diff s s').
  Proof.
    intros x s s' hm; ND.fsetdec.
  Qed.
  
  Lemma diff_remove_equal_diff_2 :
    forall x s s',
      ~ NtSet.In x s'
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s')) (NtSet.diff s s').
  Proof.
    intros x s s' hm; ND.fsetdec.
  Qed.
  
  Lemma cardinal_diff_remove_le :
    forall x s s',
      NtSet.In x s
      -> NtSet.In x s'
      -> NtSet.cardinal (NtSet.diff s (NtSet.remove x s')) <=
         S (NtSet.cardinal (NtSet.diff s s')).
    intros x s s' hi hm.
    rewrite diff_remove_equal_add_diff; auto.
    rewrite add_cardinal_2; auto.
    apply not_mem_iff; ND.fsetdec.
  Qed.

  Lemma diff_remove_equal_diff :
    forall x s s',
      ~ NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s'))
                     (NtSet.diff s s').
  Proof.
    intros; ND.fsetdec.
  Qed.
  
  Lemma stackScore_le_after_return :
    forall callee caller caller' o o' x suf vi u locs b,
      callee     = SF o' []
      -> caller  = SF o (NT x :: suf)
      -> caller' = SF o suf
      -> NtSet.In x u
      -> stackScore (caller', locs) b (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <= stackScore (callee, caller :: locs) b (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros ce cr cr' o o' x suf vi u locs b hce hcr hcr' hi; subst.
    unfold stackScore; simpl.
    unfold headFrameScore; unfold headFrameSize.
    unfold tailFrameScore; unfold tailFrameSize.
    destruct (NtSet.mem x vi) eqn:hm.
    - apply NF.mem_iff in hm.
      assert (hi' : NtSet.In x u) by ND.fsetdec.
      apply nonzero_exponents_le__stackScore_le; split; try omega.
      + apply cardinal_diff_remove_gt_0; auto. 
      + apply cardinal_diff_remove_le; auto.
      + apply le_n_S; apply cardinal_diff_remove_le; auto. 
    - apply not_mem_iff in hm.
      rewrite diff_remove_equal_diff_2; auto.
      apply nonzero_exponents_le__stackScore_le; split; try omega.
      eapply cardinal_diff_gt_0; eauto.
  Qed.      

  (* this version might be easier to apply *)
  Lemma stackScore_le_after_return' :
    forall suf_cr o o' x b vi u frs,
      NtSet.In x u 
      -> stackScore (SF o suf_cr, frs) 
                    b 
                    (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <= 
         stackScore (SF o' [], SF o (NT x :: suf_cr) :: frs) 
                    b 
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros; eapply stackScore_le_after_return; sis; eauto.
  Qed.

  Lemma remove_cardinal_minus_1 :
    forall (x : nonterminal) (s : NtSet.t),
      NtSet.mem x s = true
      -> NtSet.cardinal (NtSet.remove x s) = NtSet.cardinal s - 1.
  Proof.
    intros x s Hm.
    rewrite <- remove_cardinal_1 with (s := s) (x := x); auto.
    omega.
  Qed.

  Lemma lt_lt_mul_nonzero_r :
    forall y x z,
      x < y -> 0 < z -> x < y * z.
  Proof.
    intros y x z Hxy Hz.
    destruct z as [| z]; try omega.
    rewrite Nat.mul_succ_r. 
    apply Nat.lt_lt_add_l; auto.
  Qed.

  Lemma base_gt_zero_power_gt_zero :
    forall b e,
      0 < b
      -> 0 < b ^ e.
  Proof.
    intros b e Hlt; induction e as [| e IH]; simpl in *; auto.
    destruct b as [| b]; try omega.
    apply lt_lt_mul_nonzero_r; auto.
  Qed.

  Lemma less_significant_value_lt_more_significant_digit :
    forall e2 e1 v b,
      v < b
      -> e1 < e2
      -> v * (b ^ e1) < b ^ e2.
  Proof.
    intros e2; induction e2 as [| e2 IH]; intros e1 v b Hvb Hee; sis; try omega.
    destruct b as [| b]; try omega.
    destruct e1 as [| e1].
    - rewrite Nat.mul_1_r.
      apply lt_lt_mul_nonzero_r; auto.
      apply base_gt_zero_power_gt_zero; omega.    
    - rewrite Nat.pow_succ_r; try omega. 
      rewrite <- Nat.mul_comm.
      rewrite <- Nat.mul_assoc.
      apply mult_lt_compat_l; try omega.
      rewrite Nat.mul_comm.
      apply IH; omega. 
  Qed.

  Lemma diff_add_equal_remove_diff :
    forall x s s',
      NtSet.Equal (NtSet.diff s (NtSet.add x s'))
                  (NtSet.remove x (NtSet.diff s s')).
  Proof.
    intros x s s'; ND.fsetdec.
  Qed.

  Lemma cardinal_diff_minus_1 :
    forall x s s',
      NtSet.In x s
      -> ~ NtSet.In x s'
      -> S (NtSet.cardinal (NtSet.diff s (NtSet.add x s'))) =
         NtSet.cardinal (NtSet.diff s s').
  Proof.
    intros x s s' hi hn.
    rewrite diff_add_equal_remove_diff.
    apply remove_cardinal_1.
    apply NF.mem_iff; ND.fsetdec.
  Qed.
  
  Lemma stackScore_lt_after_push :
    forall pm callee caller o o' x suf' u vi rhs locs,
      callee    = SF o rhs
      -> caller = SF o' (NT x :: suf')
      -> NtSet.In x u
      -> ~ NtSet.In x vi
      -> In (x, rhs) (grammarOf pm)
      -> stackScore (callee, caller :: locs)
                    (1 + maxRhsLength (grammarOf pm))
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stackScore (caller, locs)
                    (1 + maxRhsLength (grammarOf pm))
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros pm callee caller o o' x suf' u vi rhs locs
           Hcallee Hcaller Hin Hnin Hi'; subst; simpl.
    rewrite cardinal_diff_minus_1; auto.
    unfold headFrameScore; unfold headFrameSize.
    unfold tailFrameScore; unfold tailFrameSize; simpl.
    repeat rewrite plus_assoc; repeat apply plus_lt_compat_r.
    apply less_significant_value_lt_more_significant_digit.
    - eapply grammar_rhs_length_lt_max_plus_1; eauto.
    - apply subset_cardinal_lt with (x := x); ND.fsetdec. 
  Qed.

  Lemma stackScore_lt_after_push' :
    forall pm suf_cr rhs o o' x u vi locs,
      NtSet.In x u
      -> ~ NtSet.In x vi
      -> In (x, rhs) (grammarOf pm)
      -> stackScore (SF o rhs, SF o' (NT x :: suf_cr) :: locs)
                    (1 + maxRhsLength (grammarOf pm))
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stackScore (SF o' (NT x :: suf_cr), locs)
                    (1 + maxRhsLength (grammarOf pm))
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros; eapply stackScore_lt_after_push; sis; eauto.
  Qed.

End TerminationFn.

