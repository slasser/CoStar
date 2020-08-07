Require Import List.
Require Import GallStar.SLLPrediction_error_free.
Require Import GallStar.Tactics.
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
      -> handleFinalSubparsers ys = PredReject
      -> handleFinalSubparsers xs = PredReject.
  Proof.
    intros xs ys ho hh; unfold handleFinalSubparsers in *.
    destruct (filter _ ys) eqn:hf'; [.. | exfalso; dms; tc].
    destruct (filter _ xs) as [| x' xs'] eqn:hf; auto.
    eapply overapprox_finalConfig in ho; eauto.
    exfalso; eapply overapprox_nil_cons_contra; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  Lemma sllPredict'_reject__llPredict'_neq_succ :
    forall g cm ts sps sps' ca ca' rhs,
      no_left_recursion g
      -> closure_map_correct g cm
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> exists_successful_sp g sps ts
      -> cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (PredReject, ca')
      -> llPredict' g sps ts <> PredSucc rhs.
  Proof.
    intros g cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca ca' rhs hn hmc hw hs he hc ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handleFinalSubparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (allPredictionsEqual sp' sps') eqn:ha'; tc.
        clear hll.
        eapply esp_llPredict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        destruct (Cache.find _ _) as [sps''' |] eqn:hf.
        * apply hc in hf.
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * destruct (sllTarget _ _ _ _) as [? | sps'''] eqn:ht'; tc.
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- eapply sllTarget_add_preserves_cache_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  (* This might belong somewhere else *)
  Lemma esp_llPredict'_succ__exists_target : 
    forall g sps a l ts ys,
      no_left_recursion g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> llPredict' g sps ((a, l) :: ts) = PredAmbig ys
      -> exists sps',
          llTarget g a sps = inr sps'
          /\ llPredict' g sps' ts = PredAmbig ys.
  Proof.
    intros g sps a l ts ys hn hw hs hl; sis; dms; tc; eauto.
  Qed.

  (* to do : it might be possible to remove some assumptions here *)
  Lemma sllPredict'_reject__llPredict'_neq_ambig :
    forall g cm ts sps sps' ca ca' rhs,
      no_left_recursion g
      -> closure_map_correct g cm
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (PredReject, ca')
      -> llPredict' g sps ts <> PredAmbig rhs.
  Proof.
    intros g cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca ca' rhs hn hmc hw hs hc ho hsll hll;
      pose proof hll as hll'; simpl in hsll, hll.
    - injection hsll; intros heq' heq; subst.
      eapply handleFinalSubparsers_overapprox_reject in heq; eauto; tc.
    - destruct sps as [| sp sps]; tc.
      destruct sps' as [| sp' sps'].
      + (* all SLL sps are exhausted *)
        eapply overapprox_nil_cons_contra; eauto.
      + (* at least one SLL sp remains *)
        destruct (allPredictionsEqual sp sps) eqn:ha; tc.
        destruct (llTarget _ _ _) as [? | sps''] eqn:ht; tc.        
        destruct (allPredictionsEqual sp' sps') eqn:ha'; tc.
        destruct (Cache.find _ _) as [sps''' |] eqn:hf.
        * apply hc in hf.
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
        * destruct (sllTarget _ _ _ _) as [? | sps'''] eqn:ht'; tc.
          eapply IH in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply sllTarget_add_preserves_cache_invar; eauto.
          -- destruct hmc; eapply target_preserves_overapprox; eauto.
  Qed.

  Lemma ussr_sllPredict_neq_reject :
    forall g cm fr o x suf frs w ca ca',
      no_left_recursion g
      -> closure_map_correct g cm
      -> fr = SF o (NT x :: suf)
      -> suffix_stack_wf g (fr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> sllPredict g cm x w ca <> (PredReject, ca').
  Proof.
    intros g cm fr o x suf frs w ca ca' hn hmc ? hw hc hg hp'; pose proof hmc as [hsou hcom]; subst.
    unfold sllPredict in hp'.
    destruct (sllStartState _ _ _) as [? | sps'] eqn:hss'; tc.
    destruct (llStartState g x (SF o (NT x :: suf), frs)) as [? | sps] eqn:hs; tc.
    - eapply llStartState_never_returns_error; eauto.
    - destruct (llPredict' g sps w) as [rhs | rhs | | e] eqn:hp.
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
  Theorem ussr_adaptivePredict_neq_reject :
    forall g cm fr o x suf frs w ca ca',
      no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> fr = SF o (NT x :: suf)
      -> suffix_stack_wf g (fr, frs)
      -> gamma_recognize g (unprocStackSyms (fr, frs)) w
      -> adaptivePredict g cm x (fr, frs) w ca <> (PredReject, ca').
  Proof.
    intros g cm fr o x suf frs w ca ca' ?
           hn hm hc hw hr hp; subst; simpl in hr.
    unfold adaptivePredict in hp.
    dmeq hsll; dms; tc; inv hp.
    - eapply ussr_llPredict_neq_reject; eauto.
    - eapply ussr_sllPredict_neq_reject; eauto.
  Qed.

End SllPredictionCompleteFn.
