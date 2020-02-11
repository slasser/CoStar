Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module PredictionErrorFreeFn (Import D : Defs.T).

  Module Export P := PredictionFn D.

  (* BREAKING THIS INTO TWO GROUPS OF LEMMAS
   FOR THE TWO TYPES OF PREDICTION ERRORS *)

  (* SP INVALID STATE CASE *)

  Inductive stable_config : suffix_stack -> Prop :=
  | SC_empty :
      stable_config (SF [], [])
  | SC_terminal :
      forall a suf frs,
        stable_config (SF (T a :: suf), frs).

  Hint Constructors stable_config.

  Definition all_stacks_stable sps :=
    forall sp, In sp sps -> stable_config sp.(stack).

  Lemma spClosureStep_never_returns_SpInvalidState :
    forall g sp,
      suffix_stack_wf g sp.(stack)
      -> spClosureStep g sp <> SpClosureStepError SpInvalidState.
  Proof.
    intros g sp hw; unfold not; intros hs.
    unfold spClosureStep in hs; dms; tc; inv hw.
  Qed.

  Lemma spClosure_never_returns_SpInvalidState :
    forall (g    : grammar)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (sp   : subparser)
           (a'   : Acc lex_nat_pair (meas g sp)),
      pair = meas g sp
      -> suffix_stack_wf g sp.(stack)
      -> spClosure g sp a' <> inl SpInvalidState.
  Proof.
    intros g pair a'.
    induction a' as [pair hlt IH].
    intros sp a heq hw; unfold not; intros hs; subst.
    apply spClosure_error_cases in hs.
    destruct hs as [hs | [sps [hs [crs [heq heq']]]]]; subst.
    - eapply spClosureStep_never_returns_SpInvalidState; eauto.
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply spClosureStep_meas_lt; eauto.
      + eapply spClosureStep_preserves_suffix_stack_wf_invar; eauto.
  Qed.
  
  Lemma closure_never_returns_SpInvalidState :
    forall g sps,
      all_suffix_stacks_wf g sps
      -> closure g sps <> inl SpInvalidState.
  Proof.
    intros g sps hw; unfold not; intros hc.
    unfold closure in hc.
    apply aggrClosureResults_error_in_input in hc.
    apply in_map_iff in hc; destruct hc as [sp [hs hi]].
    eapply spClosure_never_returns_SpInvalidState; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma startState_never_returns_SpInvalidState :
    forall g fr frs x suf,
      suffix_stack_wf g (fr, frs)
      -> fr = SF (NT x :: suf)
      -> startState g x (fr, frs) <> inl SpInvalidState.
  Proof.
    intros g fr frs x suf hw heq; unfold not; intros hss.
    eapply closure_never_returns_SpInvalidState; eauto.
    intros sp hi.
    unfold initSps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [heq' hi]]; subst; simpl.
    (* LEMMA *)
    clear hss.
    inv hw; sis; subst.
    - wf_upper_nil. 
      apply rhssForNt_in_iff; eauto.
    - wf_upper_nil. 
      apply rhssForNt_in_iff; auto.
  Qed.

  Lemma handleFinalSubparsers_never_returns_error :
    forall sps e,
      handleFinalSubparsers sps <> PredError e.
  Proof.
    intros sps e; unfold not; intro hh.
    unfold handleFinalSubparsers in hh; dms; tc.
  Qed.

  Lemma moveSp_never_returns_SpInvalidState_for_ready_sp :
    forall g t sp,
      stable_config sp.(stack)
      -> moveSp g t sp <> SpMoveError SpInvalidState.
  Proof.
    intros g t sp hr; unfold not; intros hm.
    unfold moveSp in hm.
    dms; tc; sis; inv hr.
  Qed.

  Lemma move_never_returns_SpInvalidState_for_ready_sps :
    forall g t sps,
      all_stacks_stable sps
      -> move g t sps <> inl SpInvalidState.
  Proof.
    intros g t sps ha; unfold not; intros hm.
    unfold move in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply moveSp_never_returns_SpInvalidState_for_ready_sp; eauto.
  Qed.

  Lemma moveSp_preserves_suffix_stack_wf_invar :
    forall g t sp sp',
      suffix_stack_wf g sp.(stack)
      -> moveSp g t sp = SpMoveSucc sp'
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g t sp sp' hw hm.
    unfold moveSp in hm; dms; tc; inv hm; sis.
    inv_suffix_frames_wf hw hi hw'; auto.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  Lemma move_preserves_suffix_stack_wf_invar :
    forall g t sps sps',
      all_suffix_stacks_wf g sps
      -> move g t sps = inr sps'
      -> all_suffix_stacks_wf g sps'.
  Proof.
    intros g t sps sps' ha hm.
    unfold all_suffix_stacks_wf.
    intros sp' hi.
    unfold move in hm.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi']].
    eapply moveSp_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma spClosure_preserves_suffix_stack_wf_invar :
    forall g pr (a : Acc lex_nat_pair pr) sp sp' a' sps',
      pr = meas g sp
      -> suffix_stack_wf g sp.(stack)
      -> spClosure g sp a' = inr sps'
      -> In sp' sps'
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g pr a'.
    induction a' as [pr hlt IH]; intros sp sp' a sps' heq hw hs hi; subst.
    apply spClosure_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply spClosureStep_meas_lt; eauto.
      + eapply spClosureStep_preserves_suffix_stack_wf_invar; eauto.
  Qed.
  
  Lemma closure_preserves_suffix_stack_wf_invar :
    forall g sps sps',
      all_suffix_stacks_wf g sps
      -> closure g sps = inr sps'
      -> all_suffix_stacks_wf g sps'.
  Proof.
    intros g sps sps' ha hc.
    unfold closure in hc.
    unfold all_suffix_stacks_wf.
    intros sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    apply in_map_iff in hi'.
    destruct hi' as [sp [hs hi']]; subst.
    eapply spClosure_preserves_suffix_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma spClosureStepDone_stable_config :
    forall g sp,
      spClosureStep g sp = SpClosureStepDone
      -> stable_config sp.(stack).
  Proof.
    intros g sp hs.
    unfold spClosureStep in hs; dms; tc; sis; eauto.
  Qed.

  Lemma sp_in_spClosure_result_stable_config :
    forall g pr (a : Acc lex_nat_pair pr) sp sp' a' sps',
      pr = meas g sp
      -> spClosure g sp a' = inr sps'
      -> In sp' sps'
      -> stable_config sp'.(stack).
  Proof.
    intros g pr a'.
    induction a' as [pr hlt IH]; intros sp sp' a sps' heq hs hi; subst.
    apply spClosure_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
      eapply spClosureStepDone_stable_config; eauto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      eapply spClosureStep_meas_lt; eauto.
  Qed.

  Lemma all_stacks_stable_after_closure :
    forall g sps sps',
      closure g sps = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g sps sps' hc.
    unfold closure in hc.
    unfold all_stacks_stable.
    intros sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    apply in_map_iff in hi'.
    destruct hi' as [sp [hs hi']].
    eapply sp_in_spClosure_result_stable_config; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma llPredict'_never_returns_SpInvalidState :
    forall g ts sps,
      all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llPredict' g sps ts <> PredError SpInvalidState.
  Proof.
    intros g ts; induction ts as [| t ts IH]; intros sps ha ha'; unfold not; intros hl; sis.
    - destruct sps as [| sp sps']; tc; dm; tc.
      eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc.
      dm; tc.
      dmeq hm; tc.
      + inv hl.
        eapply move_never_returns_SpInvalidState_for_ready_sps; eauto.
      + dmeq hc; tc.
        * inv hl.
          eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
          eapply closure_never_returns_SpInvalidState; eauto.
        * eapply IH in hl; eauto.
          -- eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
             eapply closure_preserves_suffix_stack_wf_invar; eauto.
          -- eapply all_stacks_stable_after_closure; eauto.
  Qed.

  Lemma stacks_wf_in_startState_result :
    forall g fr frs x suf sps,
      suffix_stack_wf g (fr, frs)
      -> fr = SF (NT x :: suf)
      -> startState g x (fr, frs) = inr sps
      -> all_suffix_stacks_wf g sps.
  Proof.
    intros g [suf'] frs x suf sps hw heq hs; sis; subst.
    eapply closure_preserves_suffix_stack_wf_invar; eauto.
    unfold all_suffix_stacks_wf; intros sp hi.
    eapply initSps_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma llPredict_never_returns_SpInvalidState :
    forall g fr frs x suf ts,
      suffix_stack_wf g (fr, frs)
      -> fr = SF (NT x :: suf)
      -> llPredict g x (fr, frs) ts <> PredError SpInvalidState.
  Proof.
    intros g fr frs x suf ts hw heq; unfold not; intros hl.
    unfold llPredict in hl.
    dmeq hss.
    - inv hl.
      eapply startState_never_returns_SpInvalidState; eauto.
    - eapply llPredict'_never_returns_SpInvalidState; eauto.
      + eapply stacks_wf_in_startState_result; eauto.
      + unfold startState in hss.
        eapply all_stacks_stable_after_closure; eauto.
  Qed.

  (* LEFT RECURSION CASE *)

  Lemma spClosureStep_LeftRecursion_facts :
    forall g av pred fr frs x,
      spClosureStep g (Sp av pred (fr, frs)) = SpClosureStepError (SpLeftRecursion x)
      -> ~ NtSet.In x av
         /\ NtSet.In x (allNts g)
         /\ exists suf,
             fr = SF (NT x :: suf).
  Proof.
    intros g av pred fr frs x hs.
    unfold spClosureStep in hs; repeat dmeq h; tc; inv hs; sis.
    repeat split; eauto.
    - unfold not; intros hi.
      apply NtSet.mem_spec in hi; tc.
    - apply NtSet.mem_spec; auto.
  Qed.

  Lemma spClosureStep_never_finds_left_recursion :
    forall g sp x,
      no_left_recursion g
      -> unavailable_nts_invar g sp
      -> spClosureStep g sp <> SpClosureStepError (SpLeftRecursion x).
  Proof.
    intros g [av pred (fr, frs)] x hn hu; unfold not; intros hs.
    pose proof hs as hs'.
    apply spClosureStep_LeftRecursion_facts in hs'.
    destruct hs' as [hn' [hi [suf' heq]]]; subst.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & suf & ? & ? & hf); subst.
    eapply frnp_grammar_nullable_path in hf; eauto.
    firstorder.
  Qed.

  Lemma spClosure_never_finds_left_recursion :
    forall g pr (a : Acc lex_nat_pair pr) sp a' x,
      no_left_recursion g
      -> unavailable_nts_invar g sp
      -> pr = meas g sp
      -> spClosure g sp a' <> inl (SpLeftRecursion x).
  Proof.
    intros g pr a'; induction a' as [pr hlt IH]. 
    intros sp a x hn hu heq; unfold not; intros hs; subst.
    apply spClosure_error_cases in hs.
    destruct hs as [hs | [sps [hs [crs [hc ha]]]]]; subst.
    - eapply spClosureStep_never_finds_left_recursion; eauto.
    - apply aggrClosureResults_error_in_input in ha.
      eapply dmap_in in ha; eauto.
      destruct ha as [sp' [hi [hi' hs']]].
      eapply IH with (sp := sp'); eauto.
      + eapply spClosureStep_meas_lt; eauto.
      + eapply spClosureStep_preserves_unavailable_nts_invar; eauto.
  Qed.

  Lemma closure_never_finds_left_recursion :
    forall g x sps,
      no_left_recursion g
      -> sps_unavailable_nts_invar g sps
      -> closure g sps <> inl (SpLeftRecursion x).
  Proof.
    intros g x sps hn hu; unfold not; intros hc.
    unfold closure in hc.
    apply aggrClosureResults_error_in_input in hc.
    apply in_map_iff in hc.
    destruct hc as [sp [hs hi]].
    eapply spClosure_never_finds_left_recursion; eauto.
    apply lex_nat_pair_wf.
  Qed.        

  Lemma startState_never_finds_left_recursion :
    forall g x x' fr frs suf,
      no_left_recursion g
      -> fr = SF (NT x :: suf)
      -> startState g x (fr, frs) <> inl (SpLeftRecursion x').
  Proof.
    intros g x x' [suf'] frs suf hn heq; unfold not; intros hs; sis; inv heq; subst.
    eapply closure_never_finds_left_recursion; eauto.
    unfold sps_unavailable_nts_invar; intros sp hi.
    eapply initSps_sat_unavailable_nts_invar; eauto.
  Qed.

  Lemma moveSp_never_returns_SpLeftRecursion :
    forall g t sp x,
      moveSp g t sp <> SpMoveError (SpLeftRecursion x).
  Proof.
    intros g t sp x; unfold not; intros hm.
    unfold moveSp in hm; dms; tc.
  Qed.

  Lemma move_never_returns_SpLeftRecursion :
    forall g t sps x,
      move g t sps <> inl (SpLeftRecursion x).
  Proof.
    intros g t sps x; unfold not; intros hm.
    unfold move in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply moveSp_never_returns_SpLeftRecursion; eauto.
  Qed.

  Lemma unavailable_nts_invar_holds_after_moveSp :
    forall g t sp sp',
      moveSp g t sp = SpMoveSucc sp'
      -> unavailable_nts_invar g sp'.
  Proof.
    intros g t sp sp' hm.
    unfold moveSp in hm; dms; tc; inv hm.
    unfold unavailable_nts_are_open_calls.
    intros x hi hni; ND.fsetdec.
  Qed.

  Lemma unavailable_nts_invar_holds_after_move :
    forall g t sps sps',
      move g t sps = inr sps'
      -> sps_unavailable_nts_invar g sps'.
  Proof.
    intros g t sps sps' hm.
    unfold sps_unavailable_nts_invar.
    intros sp' hi.
    unfold move in hm.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi']].
    eapply unavailable_nts_invar_holds_after_moveSp; eauto.
  Qed.

  Lemma llPredict'_never_returns_SpLeftRecursion :
    forall g ts sps x,
      no_left_recursion g
      -> llPredict' g sps ts <> PredError (SpLeftRecursion x).
  Proof.
    intros g ts; induction ts as [| t ts IH]; intros sps x hn; unfold not; intros hl; sis.
    - dm; tc; dm; tc.
      eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc; dm; tc; dmeq hm; tc.
      + inv hl.
        eapply move_never_returns_SpLeftRecursion; eauto.
      + dmeq hc.
        * inv hl.
          eapply unavailable_nts_invar_holds_after_move in hm.
          eapply closure_never_finds_left_recursion in hc; eauto.
        * eapply IH in hl; eauto.
  Qed.

  Lemma llPredict_never_returns_SpLeftRecursion :
    forall g x x' fr frs ts suf,
      no_left_recursion g
      -> fr = SF (NT x :: suf)
      -> llPredict g x (fr, frs) ts <> PredError (SpLeftRecursion x').
  Proof.
    intros g x x' fr frs ts suf hn heq; unfold not; intros hl.
    unfold llPredict in hl.
    dmeq hss.
    - inv hl; eapply startState_never_finds_left_recursion; eauto.
    - eapply llPredict'_never_returns_SpLeftRecursion; eauto.
  Qed.

End PredictionErrorFreeFn.