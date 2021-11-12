Require Import List.
Require Import CoStar.SLLPrediction_error_free.
Require Import CoStar.Tactics.
Import ListNotations.

Module SllPredictionCompleteFn (Import D : Defs.T).

  Module Export SLLPEF := SllPredictionErrorFreeFn D.

  Lemma overapprox_nil_cons_contra :
    forall sp sps,
      ~ overapprox [] (sp :: sps).
  Proof.
    intros sp sps ho.
    assert (hi : In sp (sp :: sps)) by apply in_eq.
    apply ho in hi; destruct hi as [? [hi ?]]; inv hi.
  Qed.

  Lemma handleFinalSubparsers_overapprox_reject :
    forall xs ys,
      overapprox ys xs
      -> sllHandleFinalSubparsers ys = PredReject
      -> handleFinalSubparsers xs = PredReject.
  Proof.
    intros xs ys ho hh.
    unfold handleFinalSubparsers in *; unfold sllHandleFinalSubparsers in *.
    destruct (filter _ ys) eqn:hf'; [.. | exfalso; dms; tc].
    destruct (filter _ xs) as [| x' xs'] eqn:hf; auto.
    eapply overapprox_finalConfig in ho; eauto.
    exfalso; eapply overapprox_nil_cons_contra; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  Lemma sllPredict'_reject__llPredict'_neq_succ :
    forall gr hw rm cm ts sps sps' ca ca' hk hk' hc rhs,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps ts
      -> overapprox sps' sps
      -> sllPredict' rm cm sps' ts ca hk' hc = (PredReject, ca')
      -> llPredict' gr hw rm sps ts hk <> PredSucc rhs.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca ca' hk hk' hc rhs hn hp hmc hw' hs he ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handleFinalSubparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (allPredictionsEqual _ _ sp' sps') eqn:ha'; tc.
        clear hll.
        eapply esp_llPredict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        apply sllPredict'_cont_cases in hsll. 
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  (* This might belong somewhere else *)
  Lemma esp_llPredict'_succ__exists_target : 
    forall gr hw rm sps a l ts hk ys,
      no_left_recursion gr
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> llPredict' gr hw rm sps (@existT _ _ a l :: ts) hk = PredAmbig ys
      -> exists sps' hk',
          llTarget gr hw rm (@existT _ _ a l) sps hk = inr sps'
          /\ llPredict' gr hw rm sps' ts hk' = PredAmbig ys.
  Proof.
    intros gr hw rm sps a l ts hk ys hn hw' hs hl; sis; dms; tc.
    apply llPredict'_cont_cases in hl; destruct hl as [sps'' [ht hl]]; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  Lemma sllPredict'_reject__llPredict'_neq_ambig :
    forall gr hw rm cm ts sps sps' hk hk' ca hc ca' rhs,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> overapprox sps' sps
      -> sllPredict' rm cm sps' ts ca hk' hc = (PredReject, ca')
      -> llPredict' gr hw rm sps ts hk <> PredAmbig rhs.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' hk hk' ca hc ca' rhs hn hp hmc hw' hs ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handleFinalSubparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (allPredictionsEqual _ _ sp sps) eqn:ha; tc.
        apply llPredict'_cont_cases in hll.
        destruct hll as [sps'' [ht hll]].
        destruct (allPredictionsEqual _ _ sp' sps') eqn:ha'; tc.
        apply sllPredict'_cont_cases in hsll.
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  Lemma ussr_sllPredict_neq_reject :
    forall gr (hw : grammar_wf gr) rm cm fr pre vs x suf frs ts ca hc ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_pushes_from_keyset rm (fr, frs)
      -> stack_wf gr (fr, frs)
      -> stack_accepts_suffix gr (fr, frs) ts
      -> sllPredict rm cm x ts ca hc <> (PredReject, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc ca'
           hn hpc hmc ? hk hw' hg hp'; pose proof hmc as [hsou hcom]; subst.
    unfold sllPredict in hp'.
    apply sllPredict_cases in hp'.
    destruct hp' as [sps' [hss' hp']].
    destruct (llStartState gr hw rm pre vs x suf frs hk) as [? | sps] eqn:hs; tc.
    - eapply llStartState_never_returns_error; eauto.
    - destruct (llPredict' gr hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ hs))
        as [rhs | rhs | | e] eqn:hp.
      + eapply sllPredict'_reject__llPredict'_neq_succ; eauto.
        * eapply llStartState_preserves_stacks_wf_invar; eauto.
        * eapply llStartState_all_stacks_stable; eauto.
        * eapply llStartState_preserves_esp_invar; eauto.
        * eapply overapprox_startState; eauto. 
      + eapply sllPredict'_reject__llPredict'_neq_ambig; eauto.
        * eapply llStartState_preserves_stacks_wf_invar; eauto.
        * eapply llStartState_all_stacks_stable; eauto.
        * eapply overapprox_startState; eauto. 
      + eapply esp_llPredict'_neq_reject; eauto.
        * eapply llStartState_preserves_stacks_wf_invar; eauto.
        * eapply llStartState_all_stacks_stable; eauto.
        * eapply llStartState_preserves_esp_invar; eauto.
      + eapply llPredict'_never_returns_error; eauto.
        * eapply llStartState_preserves_stacks_wf_invar; eauto.
        * eapply llStartState_all_stacks_stable; eauto.
  Qed.
  
  (* THE PRIZE *)
  Theorem sas_adaptivePredict_neq_reject :
    forall gr hw rm cm fr pre vs x suf frs ts ca hc hk ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_wf gr (fr, frs)
      -> stack_accepts_suffix gr (fr, frs) ts
      -> adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk <> (PredReject, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc hk ca' hn hp hm ? hw' hr ha; subst; simpl in hr.
    unfold adaptivePredict in ha.
    dmeq hsll; dms; tc; inv ha.
    - eapply ussr_llPredict_neq_reject; eauto.
    - eapply ussr_sllPredict_neq_reject; eauto.
  Qed.
  
End SllPredictionCompleteFn.
