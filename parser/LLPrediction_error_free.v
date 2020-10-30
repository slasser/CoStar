Require Import List.
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.LLPrediction.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module LLPredictionErrorFreeFn (Import D : Defs.T).

  Module Export LLP := LLPredictionFn D.

  (* BREAKING THIS INTO TWO GROUPS OF LEMMAS
   FOR THE TWO TYPES OF PREDICTION ERRORS *)

  (* SP INVALID STATE CASE *)

  Inductive stable_config : suffix_stack -> Prop :=
  | SC_empty :
      stable_config (SF None [], [])
  | SC_terminal :
      forall o a suf frs,
        stable_config (SF o (T a :: suf), frs).

  Hint Constructors stable_config : core.

  Definition all_stacks_stable sps :=
    forall sp, In sp sps -> stable_config sp.(stack).

  Lemma cstep_never_returns_SpInvalidState :
    forall g pm vi sp,
      suffix_stack_wf g sp.(stack)
      -> cstep pm vi sp <> CstepError SpInvalidState.
  Proof.
    intros g pm vi sp hw; unfold not; intros hs.
    unfold cstep in hs; dms; tc; inv hw.
  Qed.

  Lemma llc_never_returns_SpInvalidState :
    forall (g    : grammar)
           (pm   : production_map)
           (pair : nat * nat)
           (ha   : Acc lex_nat_pair pair)
           (vi   : NtSet.t)
           (sp   : subparser)
           (hk   : sp_pushes_from_keyset pm sp)
           (ha'  : Acc lex_nat_pair (meas pm vi sp)),
      pair = meas pm vi sp
      -> production_map_correct pm g
      -> suffix_stack_wf g sp.(stack)
      -> llc pm vi sp hk ha' <> inl SpInvalidState.
  Proof.
    intros g pm pair a'.
    induction a' as [pair hlt IH].
    intros vi sp hk ha heq hc hw; unfold not; intros hs; subst.
    apply llc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [heq heq']]]]]]; subst.
    - eapply cstep_never_returns_SpInvalidState; eauto.
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_suffix_stack_wf_invar; eauto.
  Qed.
  
  Lemma llClosure_never_returns_SpInvalidState :
    forall g pm sps hk,
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> llClosure pm sps hk <> inl SpInvalidState.
  Proof.
    intros g pm sps hk hp hw; unfold not; intros hc.
    unfold llClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    eapply dmap_in in hc; eauto.
    destruct hc as [sp [hi [_ hc]]].
    eapply llc_never_returns_SpInvalidState; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma llStartState_never_returns_SpInvalidState :
    forall g pm fr frs o x suf hk,
      production_map_correct pm g
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF o (NT x :: suf)
      -> llStartState pm o x suf frs hk <> inl SpInvalidState.
  Proof.
    intros g pm fr frs o x suf hk hp hw heq; unfold not; intros hss.
    eapply llClosure_never_returns_SpInvalidState; eauto.
    intros sp hi.
    unfold llInitSps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [heq' hi]]; subst; simpl.
    (* LEMMA *)
    clear hss; inv hw; sis; subst.
    - wf_upper_nil. 
      eapply rhssFor_in_iff; eauto.
    - wf_upper_nil. 
      eapply rhssFor_in_iff; eauto.
  Qed.

  Lemma handleFinalSubparsers_never_returns_error :
    forall sps e,
      handleFinalSubparsers sps <> PredError e.
  Proof.
    intros sps e; unfold not; intro hh.
    unfold handleFinalSubparsers in hh; dms; tc.
  Qed.

  Lemma moveSp_never_returns_SpInvalidState_for_ready_sp :
    forall t sp,
      stable_config sp.(stack)
      -> moveSp t sp <> MoveError SpInvalidState.
  Proof.
    intros t sp hr; unfold not; intros hm.
    unfold moveSp in hm.
    dms; tc; sis; inv hr.
  Qed.

  Lemma move_never_returns_SpInvalidState_for_ready_sps :
    forall t sps,
      all_stacks_stable sps
      -> move t sps <> inl SpInvalidState.
  Proof.
    intros t sps ha; unfold not; intros hm.
    unfold move in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply moveSp_never_returns_SpInvalidState_for_ready_sp; eauto.
  Qed.

  Lemma moveSp_preserves_suffix_stack_wf_invar :
    forall g t sp sp',
      suffix_stack_wf g sp.(stack)
      -> moveSp t sp = MoveSucc sp'
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
      -> move t sps = inr sps'
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

  Lemma llc_preserves_suffix_stack_wf_invar :
    forall g pm pr (a : Acc lex_nat_pair pr) vi sp sp' hk a' sps',
      pr = meas pm vi sp
      -> production_map_correct pm g
      -> suffix_stack_wf g sp.(stack)
      -> llc pm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g pm pr a'.
    induction a' as [pr hlt IH]; intros vi sp sp' hk a sps' heq hp hw hs hi; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_suffix_stack_wf_invar; eauto.
  Qed.
  
  Lemma llClosure_preserves_suffix_stack_wf_invar :
    forall g pm sps hk sps',
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> llClosure pm sps hk = inr sps'
      -> all_suffix_stacks_wf g sps'.
  Proof.
    intros g pm sps hk sps' hp ha hc.
    unfold llClosure in hc.
    unfold all_suffix_stacks_wf.
    intros sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply llc_preserves_suffix_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma cstepDone_stable_config :
    forall g pm vi sp,
      suffix_stack_wf g sp.(stack)
      -> cstep pm vi sp = CstepDone
      -> stable_config sp.(stack).
  Proof.
    intros g pm vi sp hw hs.
    unfold cstep in hs; dms; tc; sis; inv hw; auto.
  Qed.

  Lemma sp_in_llc_result_stable_config :
    forall g pm pr (a : Acc lex_nat_pair pr) vi sp sp' hk a' sps',
      pr = meas pm vi sp
      -> production_map_correct pm g
      -> suffix_stack_wf g sp.(stack)
      -> llc pm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> stable_config sp'.(stack).
  Proof.
    intros g pm pr a'.
    induction a' as [pr hlt IH]; intros vi sp sp' hk a sps' heq hp hw hs hi; subst.
    apply llc_success_cases in hs.
    destruct hs as [[hd heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
      eapply cstepDone_stable_config; eauto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma all_stacks_stable_after_closure :
    forall g pm sps hk sps',
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> llClosure pm sps hk = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g pm sps hk sps' hp hw hc.
    unfold llClosure in hc.
    unfold all_stacks_stable.
    intros sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sp_in_llc_result_stable_config; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma llTarget_never_returns_SpInvalidState :
    forall g pm a sps hk,
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llTarget pm a sps hk <> inl SpInvalidState.
  Proof.
    intros g pm a sps hk hp hw hs; unfold not; intros ht.
    apply llTarget_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply move_never_returns_SpInvalidState_for_ready_sps; eauto.
    - eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
      eapply llClosure_never_returns_SpInvalidState; eauto.
  Qed.

  Lemma llTarget_preserves_suffix_stacks_wf_invar :
    forall g pm a sps hk sps',
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> llTarget pm a sps hk = inr sps'
      -> all_suffix_stacks_wf g sps'.
  Proof.
    intros g pm a sps hk sps' hp hw ht.
    apply llTarget_cases in ht.
    destruct ht as [sps'' [hk' [hm hc]]].
    eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
    eapply llClosure_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma llTarget_preserves_stacks_stable_invar :
    forall g pm a sps hk sps',
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llTarget pm a sps hk = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g pm a sps hk sps' hp hw hs ht; unfold llTarget in ht.
    apply llTarget_cases in ht.
    destruct ht as [sps'' [hk' [hm hc]]].
    eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
    eapply all_stacks_stable_after_closure; eauto.
  Qed.

  Lemma llPredict'_never_returns_SpInvalidState :
    forall g pm ts sps hk,
      production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llPredict' pm sps ts hk <> PredError SpInvalidState.
  Proof.
    intros g pm ts; induction ts as [| (a,l) ts IH]; intros sps hk hp ha ha';
      unfold not; intros hl; sis.
    - eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc.
      dm; tc.
      apply llPredict'_cont_cases in hl.
      destruct hl as [ht | [sps'' [ht hl]]].
      + eapply llTarget_never_returns_SpInvalidState; eauto.
      + eapply IH in hl; eauto.
        * eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
        * eapply llTarget_preserves_stacks_stable_invar; eauto.
  Qed.

  Lemma llStartState_preserves_stacks_wf_invar :
    forall g pm fr frs o x suf hk sps,
      production_map_correct pm g
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF o (NT x :: suf)
      -> llStartState pm o x suf frs hk = inr sps
      -> all_suffix_stacks_wf g sps.
  Proof.
    intros g pm [suf'] frs o x suf hk sps hp hw heq hs; sis; subst.
    eapply llClosure_preserves_suffix_stack_wf_invar; eauto.
    unfold all_suffix_stacks_wf; intros sp hi.
    eapply llInitSps_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma llStartState_all_stacks_stable :
    forall g pm cr o x suf frs hk sps,
      production_map_correct pm g
      -> cr = SF o (NT x :: suf)
      -> suffix_stack_wf g (cr, frs)
      -> llStartState pm o x suf frs hk = inr sps
      -> all_stacks_stable sps.
  Proof.
    intros g pm cr o x suf frs hk sps hp ? hw hs sp hi.
    eapply all_stacks_stable_after_closure; eauto.
    eapply llInitSps_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma llPredict_never_returns_SpInvalidState :
    forall g pm fr frs o x suf ts hk,
      production_map_correct pm g
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF o (NT x :: suf)
      -> llPredict pm o x suf frs ts hk <> PredError SpInvalidState.
  Proof.
    intros g pm fr frs o x suf ts hk hp hw heq; unfold not; intros hl.
    apply llPredict_cases in hl.
    destruct hl as [hl | [sps [hs hl]]].
    - eapply llStartState_never_returns_SpInvalidState; eauto.
    - eapply llPredict'_never_returns_SpInvalidState; eauto.
      + eapply llStartState_preserves_stacks_wf_invar; eauto. 
      + eapply llStartState_all_stacks_stable; eauto.
  Qed.

  (* LEFT RECURSION CASE *)

  Lemma find_allNts :
    forall g pm x ys,
      production_map_correct pm g
      -> NM.find x pm = Some ys
      -> NtSet.In x (allNts g).
  Proof.
    intros g pm x ys [hs [hs' hc]] hi.
    apply allNts_lhss_iff.
    apply hs; apply NMF.in_find_iff; tc.
  Qed.

  Lemma cstep_LeftRecursion_facts :
    forall g pm vi pred fr frs x,
      production_map_correct pm g
      -> cstep pm vi (Sp pred (fr, frs)) = CstepError (SpLeftRecursion x)
      -> NtSet.In x vi
         /\ NtSet.In x (allNts g)
         /\ exists o suf,
             fr = SF o (NT x :: suf).
  Proof.
    intros g pm vi pred fr frs x hp hs.
    unfold cstep in hs; repeat dmeq h; tc; inv hs; sis.
    repeat split; eauto.
    - apply NF.mem_iff; auto. 
    - eapply find_allNts; eauto.
  Qed.

  Lemma cstep_never_finds_left_recursion :
    forall g pm vi sp x,
      no_left_recursion g
      -> production_map_correct pm g
      -> unavailable_nts_invar g vi sp
      -> cstep pm vi sp <> CstepError (SpLeftRecursion x).
  Proof.
    intros g pm vi [pred (fr, frs)] x hn hc hu; unfold not; intros hs.
    pose proof hs as hs'.
    eapply cstep_LeftRecursion_facts in hs'; eauto.
    destruct hs' as [hn' [hi [o [suf' heq]]]]; subst.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & hf); subst.
    eapply frnp_grammar_nullable_path in hf; eauto.
    firstorder.
  Qed.

  Lemma llc_never_finds_left_recursion :
    forall g pm pr (a : Acc lex_nat_pair pr) vi sp hk a' x,
      no_left_recursion g
      -> production_map_correct pm g
      -> unavailable_nts_invar g vi sp
      -> pr = meas pm vi sp
      -> llc pm vi sp hk a' <> inl (SpLeftRecursion x).
  Proof.
    intros g pm pr a'; induction a' as [pr hlt IH]. 
    intros vi sp hk a x hn hc hu heq; unfold not; intros hs; subst.
    apply llc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [hc' ha]]]]]]; subst.
    - eapply cstep_never_finds_left_recursion; eauto.
    - apply aggrClosureResults_error_in_input in ha.
      eapply dmap_in in ha; eauto.
      destruct ha as [sp' [hi [hi' hs']]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_unavailable_nts_invar; eauto.
  Qed.

  Lemma closure_never_finds_left_recursion :
    forall g pm sps hk x,
      no_left_recursion g
      -> production_map_correct pm g
      -> llClosure pm sps hk <> inl (SpLeftRecursion x).
  Proof.
    intros g pm sps hk x hn hp; unfold not; intros hc.
    unfold llClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    eapply dmap_in in hc; eauto.
    destruct hc as [[pred (fr, frs)] [hi [_ hs]]].
    eapply llc_never_finds_left_recursion; eauto.
    - apply lex_nat_pair_wf.
    - apply unavailable_nts_empty.
  Qed.        

  Lemma moveSp_never_returns_SpLeftRecursion :
    forall t sp x,
      moveSp t sp <> MoveError (SpLeftRecursion x).
  Proof.
    intros t sp x; unfold not; intros hm.
    unfold moveSp in hm; dms; tc.
  Qed.

  Lemma move_never_returns_SpLeftRecursion :
    forall t sps x,
      move t sps <> inl (SpLeftRecursion x).
  Proof.
    intros t sps x; unfold not; intros hm.
    unfold move in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply moveSp_never_returns_SpLeftRecursion; eauto.
  Qed.

  Lemma llTarget_never_returns_SpLeftRecursion :
    forall g pm a sps hk x,
      no_left_recursion g
      -> production_map_correct pm g
      -> llTarget pm a sps hk <> inl (SpLeftRecursion x).
  Proof.
    intros g pm a sps hk x hn hp; unfold not; intros ht.
    apply llTarget_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply move_never_returns_SpLeftRecursion; eauto.
    - eapply closure_never_finds_left_recursion; eauto.
  Qed.
  
  Lemma llPredict'_never_returns_SpLeftRecursion :
    forall g pm ts sps hk x,
      no_left_recursion g
      -> production_map_correct pm g
      -> llPredict' pm sps ts hk <> PredError (SpLeftRecursion x).
  Proof.
    intros g pm ts; induction ts as [| (a,l) ts IH];
      intros sps hk x hn hp hl; sis.
    - eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps']; tc; dm; tc.
      apply llPredict'_cont_cases in hl.
      destruct hl as [ht | [sps'' [ht hl]]].
      + eapply llTarget_never_returns_SpLeftRecursion; eauto.
      + eapply IH in hl; eauto.
  Qed.

  Lemma llPredict_never_returns_SpLeftRecursion :
    forall g pm o x suf frs ts hk x',
      no_left_recursion g
      -> production_map_correct pm g
      -> llPredict pm o x suf frs ts hk <> PredError (SpLeftRecursion x').
  Proof.
    intros g pm o x suf frs ts hk x' hn hp hl.
    apply llPredict_cases in hl.
    destruct hl as [hs | [sps [hs hp']]].
    - eapply closure_never_finds_left_recursion; eauto.
    - eapply llPredict'_never_returns_SpLeftRecursion; eauto.
  Qed.
  
  (* For convenience, some lemmas that generalize over both 
     types of prediction errors *)

  Lemma llTarget_never_returns_error :
    forall g pm a sps hk e,
      no_left_recursion g
      -> production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llTarget pm a sps hk <> inl e.
  Proof.
    unfold not; intros g pm a sps hk e hn hc hw hs hl; destruct e.
    - eapply llTarget_never_returns_SpInvalidState ; eauto.
    - eapply llTarget_never_returns_SpLeftRecursion; eauto.
  Qed.

  Lemma llStartState_never_returns_error :
    forall g pm o x suf fr frs hk e,
      no_left_recursion g
      -> production_map_correct pm g
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF o (NT x :: suf)
      -> llStartState pm o x suf frs hk <> inl e.
  Proof.
    intros ? ? ? ? ? ? ? ? ? hn hp hw ? hs; subst; destruct e.
    - eapply llStartState_never_returns_SpInvalidState; eauto.
    - eapply closure_never_finds_left_recursion; eauto.
  Qed.

  Lemma llPredict'_never_returns_error :
    forall g pm sps ts hk e,
      no_left_recursion g
      -> production_map_correct pm g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llPredict' pm sps ts hk <> PredError e.
  Proof.
    intros g pm sps ts hk e hn hp hw hs hl; destruct e.
    - eapply llPredict'_never_returns_SpInvalidState ; eauto.
    - eapply llPredict'_never_returns_SpLeftRecursion; eauto.
  Qed.
  
  Lemma llPredict_never_returns_error :
    forall g pm o x suf fr frs ts hk e,
      fr = SF o (NT x :: suf)
      -> no_left_recursion g
      -> production_map_correct pm g
      -> suffix_stack_wf g (fr, frs)
      -> llPredict pm o x suf frs ts hk <> PredError e.
  Proof.
    unfold not; intros g pm o x suf fr frs ts hk e ? hn hp hw hl; subst; destruct e.
    - eapply llPredict_never_returns_SpInvalidState;  eauto.
    - eapply llPredict_never_returns_SpLeftRecursion; eauto.
  Qed.

End LLPredictionErrorFreeFn. 
