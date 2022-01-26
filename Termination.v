Require Import Arith List Omega.
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module TerminationFn (Export D : Defs.T).

  (* Definitions related to well-founded measures *)

  Definition headFrameSize {A} (ys : list A) : nat :=
    length ys.
  
  Definition headFrameScore {A} (ys : list A) (b e : nat) : nat :=
    headFrameSize ys * (b ^ e).

  Definition tailFrameSize {A} (ys : list A) : nat :=
    match ys with
    | []       => 0
    | _ :: suf => length suf
    end.
                                                  
  Definition tailFrameScore {A} (ys : list A) (b e : nat) : nat :=
    tailFrameSize ys * (b ^ e).

  Fixpoint tailFramesScore {A} (yss : list (list A)) (b e : nat) : nat :=
    match yss with
    | []         => 0
    | ys :: yss' => tailFrameScore ys b e + tailFramesScore yss' b (1 + e)
    end.

  Definition stackScore {A} (stk : list A * list (list A)) (b e : nat) : nat :=
    match stk with
    | (fr, frs) => headFrameScore fr b e + tailFramesScore frs b (1 + e)
    end.

  Definition stackHeight {A} (stk : A * list A) : nat :=
    match stk with
    | (fr, frs) => List.length (fr :: frs)
    end.

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
    forall A (fr : list A) b e1 e2,
      0 < e1 <= e2
      -> tailFrameScore fr b e1 <= tailFrameScore fr b e2.
  Proof.
    intros A fr b e1 e2 Hlt.
    unfold tailFrameScore. 
    apply Nat.mul_le_mono_l.
    apply nonzero_exponents_le__powers_le; auto.
  Qed.

  Lemma nonzero_exponents_le__tailFramesScore_le :
    forall A (frs : list (list A)) b e1 e2,
      0 < e1 <= e2
      -> tailFramesScore frs b e1 <= tailFramesScore frs b e2.
  Proof.
    intros A frs.
    induction frs as [| fr frs' IH]; intros b e1 e2 Hlt; simpl; auto.
    apply plus_le_compat.
    - apply nonzero_exponents_le__tailFrameScore_le; auto.
    - apply IH; omega.
  Qed.

  Lemma nonzero_exponents_le__stackScore_le :
    forall A v b e1 e2 e3 e4 (frs : list (list A)),
      0 < e1 <= e2
      -> 0 < e3 <= e4
      -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
         v * (b ^ e2) + tailFramesScore frs b e4.
  Proof.
    intros A v b e1 e2 e3 e4 frs [H0e1 He1e2] [H0e3 He3e4].
    apply plus_le_compat.
    - apply Nat.mul_le_mono_l. 
      apply nonzero_exponents_le__powers_le; auto.
    - apply nonzero_exponents_le__tailFramesScore_le; auto.
  Qed.

  (*
  Lemma nonzero_exponents_le__stackScore_le :
    forall A v b e1 e2 e3 e4 (frs : list (list A)),
      0 < e1 <= e2
      -> 0 < e3 <= e4
      -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
         v * (b ^ e2) + tailFramesScore frs b e4.
  Proof.
    intros.
    
    intros ? ? ? ? ? ? ? ; intros.
    unfold stackScore.
    apply nonzero_exponents_le__tailFramesScore_le; auto.
  Qed.
   *)
  
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
    forall callee_suf caller_suf caller_suf' x suf vi u locs b,
      callee_suf = []
      -> caller_suf = NT x :: suf
      -> caller_suf' = suf
      -> NtSet.In x u
      -> stackScore (caller_suf', locs) b (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <= stackScore (callee_suf, caller_suf :: locs) b (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros ce cr cr' x suf vi u locs b hce hcr hcr' hi; subst.
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

  Lemma stackScore_le_after_return' :
    forall x suf b vi u frs,
      NtSet.In x u 
      -> stackScore (suf, frs) 
                    b 
                    (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <= 
         stackScore ([], (NT x :: suf) :: frs) 
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
    forall all_rhss rhs caller_suf x suf' u vi locs,
      caller_suf = NT x :: suf'
      -> NtSet.In x u
      -> ~ NtSet.In x vi
      -> In rhs all_rhss
      -> stackScore (rhs, caller_suf :: locs)
                    (1 + maxLength all_rhss)
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stackScore (caller_suf, locs)
                    (1 + maxLength all_rhss)
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros all_rhss rhs cr_suf x suf' u vi locs
           hcr hi hn hi'; subst; simpl.
    rewrite cardinal_diff_minus_1; auto.
    unfold tailFrameScore.
    repeat rewrite plus_assoc; repeat apply plus_lt_compat_r.
    apply less_significant_value_lt_more_significant_digit.
    - eapply mem_length_lt_max_plus_1; eauto.
    - apply subset_cardinal_lt with (x := x); ND.fsetdec. 
  Qed.    

  (*
  Lemma stackScore_lt_after_push' :
    forall all_rhss suf_cr rhs x u vi locs,
      NtSet.In x u
      -> ~ NtSet.In x vi
      -> In rhs all_rhss
      -> stackScore (rhs, suf_cr :: locs)
                    (1 + maxLength all_rhss)
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stackScore ((NT x :: suf_cr), locs)
                    (1 + maxLength all_rhss)
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros; eapply stackScore_lt_after_push; sis; eauto.
  Qed.
   *)
  
  (* A subparser invariant used to prove termination *)

  Inductive pushes_from_keyset (rm : rhs_map) : list (list symbol) -> Prop :=
  | PK_bottom :
      forall suf,
        pushes_from_keyset rm [suf]
  | PK_upper :
      forall x suf suf' sufs,
        NtSet.In x (keySet rm)
        -> pushes_from_keyset rm (        (NT x :: suf) :: sufs)
        -> pushes_from_keyset rm (suf' :: (NT x :: suf) :: sufs).

  Hint Constructors pushes_from_keyset : core.
  
  Ltac inv_pk hk  hi hk' := inversion hk as [? | ? ? ? ? hi hk']; subst; clear hk.
  
(*
  Definition sll_stack_lhss_from_keyset (rm : rhs_map) (stk : suffix_stack) : Prop :=
    match stk with
    | (fr, frs) => upper_lhss_from_keyset rm (fr :: frs)
    end.

  Definition sll_sp_lhss_from_keyset (rm : rhs_map) (sp : sll_subparser) : Prop :=
    match sp with
    | SllSp _ stk => sll_stack_lhss_from_keyset rm stk
    end.

  Definition all_sll_sp_lhss_from_keyset (rm : rhs_map) (sps : list sll_subparser) :=
    forall sp, In sp sps -> sll_sp_lhss_from_keyset rm sp.

  Lemma sll_ulk_list__ulk_mem :
    forall rm sps sp,
      all_sll_sp_lhss_from_keyset rm sps
      -> In sp sps
      -> sll_sp_lhss_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.
 *)

  Lemma return_preserves_keyset_invar :
    forall rm x suf frs,
      pushes_from_keyset rm ([] :: (NT x :: suf) :: frs)
      -> pushes_from_keyset rm (suf :: frs).
  Proof.
    intros rm x suf frs hk. 
    inv_pk hk hi hk'.
    inv hk'; auto.
  Qed.

  Lemma consume_preserves_keyset_invar :
    forall rm s suf frs,
      pushes_from_keyset rm ((s :: suf) :: frs)
      -> pushes_from_keyset rm (suf :: frs).
  Proof.
    intros rm suf suf' frs hk.
    inv_pk hk hi hk'; auto.
  Qed.

  Lemma push_preserves_keyset_invar :
    forall rm x suf suf' frs,
      NtSet.In x (keySet rm)
      -> pushes_from_keyset rm ((NT x :: suf) :: frs)
      -> pushes_from_keyset rm (suf' :: (NT x :: suf) :: frs).
  Proof.
    intros ? ? ? ? ? hi hk; inv hk; auto.
  Qed.
  
(*
  Lemma sll_return_preserves_keyset_invar :
    forall rm o_ce o_cr suf_ce suf_cr frs,
      upper_lhss_from_keyset rm (SF o_ce suf_ce :: SF o_cr suf_cr :: frs)
      -> upper_lhss_from_keyset rm (SF o_cr suf_cr :: frs).
  Proof.
    intros rm oce ocr sufce sufcr frs hk.
    inv_ulk hk hi hk'.
    inv_ulk hk' hi' hk''; auto.
  Qed.

  Lemma sll_consume_preserves_keyset_invar :
    forall rm o suf suf' frs,
      upper_lhss_from_keyset rm (SF o suf :: frs)
      -> upper_lhss_from_keyset rm (SF o suf' :: frs).
  Proof.
    intros rm o suf suf' frs hk. 
    inv_ulk hk hi hk'; auto.
  Qed.

  Lemma sll_push_preserves_keyset_invar :
    forall rm x o_cr suf_cr suf_cr' suf_ce frs,
      NtSet.In x (keySet rm)
      -> upper_lhss_from_keyset rm (SF o_cr suf_cr :: frs)
      -> upper_lhss_from_keyset rm (SF (Some x) suf_ce :: SF o_cr suf_cr' :: frs).
  Proof.
    intros ? ? ? ? ? ? ? hi hk; inv hk; auto.
  Qed.
 *)
  
  (* Now lift the invariant to LL subparser and parser stacks *)

  Definition suffix_stack_pushes_from_keyset (rm : rhs_map) (stk : list symbol * list (list symbol)) : Prop :=
    match stk with
    | (fr, frs) =>
      pushes_from_keyset rm (fr :: frs)
    end.

  (*
  Definition sp_lhss_from_keyset (rm : rhs_map) (sp : subparser) : Prop :=
    sll_sp_lhss_from_keyset rm (sllifySp sp).

  Definition all_sp_lhss_from_keyset (rm : rhs_map) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> sp_lhss_from_keyset rm sp.

  Lemma ulk_list__ulk_mem :
    forall rm sps sp,
      all_sp_lhss_from_keyset rm sps
      -> In sp sps
      -> sp_lhss_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.

   *)
  
  (* A measure function *)

  Definition meas (rm : rhs_map) (vi : NtSet.t) (sk : list symbol * list (list symbol)) : nat * nat :=
    let m  := maxLength (allRhss rm) in
    let e  := NtSet.cardinal (NtSet.diff (keySet rm) vi)
    in  (stackScore sk (1 + m) e, stackHeight sk).

  Lemma meas_lt_after_return :
    forall rm sk sk' vi vi' x suf frs,
      sk = ([], (NT x :: suf) :: frs)
      -> sk' = (suf, frs)
      -> vi' = NtSet.remove x vi
      -> suffix_stack_pushes_from_keyset rm sk
      -> lex_nat_pair (meas rm vi' sk') (meas rm vi sk).
  Proof.
    intros rm sk sk' vi vi' x suf frs ? ? ? hk; subst.
    unfold meas.
    pose proof stackScore_le_after_return' as hle.
    specialize hle with (suf := suf) (x := x).
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq]; sis.
    - apply pair_fst_lt; eauto.
    - rewrite heq; apply pair_snd_lt; auto.
    - inv hk; auto. 
  Defined.

  Lemma meas_lt_after_push :
    forall rm vi vi' sk sk' fr_cr fr_ce x suf rhs frs,
      sk     = (fr_cr, frs)
      -> sk' = (fr_ce, fr_cr :: frs)
      -> fr_cr  = NT x :: suf
      -> fr_ce  = rhs
      -> vi' = NtSet.add x vi
      -> ~ NtSet.In x vi
      -> NtSet.In x (keySet rm)
      -> In rhs (allRhss rm)
      -> lex_nat_pair (meas rm vi' sk') (meas rm vi sk).
  Proof.
    intros; subst.
    apply pair_fst_lt.
    eapply stackScore_lt_after_push; sis; eauto.
  Defined.

(*
  Definition sll_meas (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) : nat * nat :=
    match sp with
    | SllSp _ stk =>
      let m  := maxLength (allRhss rm) in
      let e  := NtSet.cardinal (NtSet.diff (keySet rm) vi)
      in  (stackScore (sllSuffixes stk) (1 + m) e, stackHeight stk)
    end.

  Lemma sll_meas_lt_after_return :
    forall rm sp sp' vi vi' pred o suf x frs,
      sp = SllSp pred (SF (Some x) [], SF o suf :: frs)
      -> sp' = SllSp pred (SF o suf, frs)
      -> vi' = NtSet.remove x vi
      -> sll_sp_lhss_from_keyset rm sp
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros rm sp sp' vi vi' pred o suf x frs ? ? ? hk; subst.
    pose proof stackScore_le_after_return' as hle.
    specialize hle with (suf_cr := suf) (x := x).
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq]; sis.
    - apply pair_fst_lt; eauto.
    - rewrite heq; apply pair_snd_lt; auto.
    - inv hk; auto. 
  Defined.

  Lemma sll_meas_lt_after_push :
    forall rm vi vi' sp sp' pred fr_cr fr_cr' fr_ce o x suf rhs frs,
      sp     = SllSp pred (fr_cr, frs)
      -> sp' = SllSp pred (fr_ce, fr_cr' :: frs)
      -> fr_cr  = SF o (NT x :: suf)
      -> fr_cr' = SF o suf
      -> fr_ce  = SF (Some x) rhs
      -> vi' = NtSet.add x vi
      -> ~ NtSet.In x vi
      -> NtSet.In x (keySet rm)
      -> In rhs (allRhss rm)
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros; subst.
    apply pair_fst_lt.
    eapply stackScore_lt_after_push; sis; eauto.
  Defined.
  *)

  Definition stack_pushes_from_keyset (rm : rhs_map) (stk : parser_stack) :=
    suffix_stack_pushes_from_keyset rm (stackSuffixes stk).

  Definition sp_pushes_from_keyset (rm : rhs_map) (sp : subparser) : Prop :=
    match sp with
    | Sp _ stk => stack_pushes_from_keyset rm stk
    end.

  Definition all_sp_pushes_from_keyset (rm : rhs_map) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> sp_pushes_from_keyset rm sp.

  Lemma pki_list__pki_mem :
    forall rm sps sp,
      all_sp_pushes_from_keyset rm sps
      -> In sp sps
      -> sp_pushes_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.

  (* Lift the invariant to SLL stacks and subparsers *)

  Definition sll_stack_pushes_from_keyset (rm : rhs_map) (stk : sll_stack) :=
    suffix_stack_pushes_from_keyset rm (sllStackSuffixes stk).

  Definition sll_sp_pushes_from_keyset (rm : rhs_map) (sp : sll_subparser) : Prop :=
    match sp with
    | SllSp _ stk => sll_stack_pushes_from_keyset rm stk
    end.

  Definition all_sll_sp_pushes_from_keyset (rm : rhs_map) (sps : list sll_subparser) : Prop :=
    forall sp, In sp sps -> sll_sp_pushes_from_keyset rm sp.

  Lemma sll_pki_list__pki_mem :
    forall rm sps sp,
      all_sll_sp_pushes_from_keyset rm sps
      -> In sp sps
      -> sll_sp_pushes_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.
  
End TerminationFn.
