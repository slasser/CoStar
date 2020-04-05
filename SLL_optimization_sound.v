Require Import List.
Require Import GallStar.SLLPrediction.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module SllOptimizationSoundFn (Import D : Defs.T).

  Module Export SLLP := SllPredictionFn D.

  (* Definitions to capture the fact that SLL prediction overapproximates 
     LL prediction. For each LL subparser in play, there exists a corresponding
     SLL subparser that carries the same prediction and has a stack that matches
     the stack top of the LL subparser. There might also be SLL subparsers in 
     play that don't correspond to any of the LL subparsers, but prediction will
     fail over to LL mode if SLL mode finds more than one viable right-hand side.
     That's why SLL prediction is a _sound_ overapproximation of LL prediction. *)
  Definition approx (sp' sp : subparser) : Prop :=
    match sp', sp with
    | Sp pred' (fr', frs'), Sp pred (fr, frs) =>
      pred' = pred
      /\ exists ctx, fr' :: frs' ++ ctx = fr :: frs
    end.
  
  Lemma approx_finalConfig_true :
    forall sp sp',
      approx sp' sp
      -> finalConfig sp  = true
      -> finalConfig sp' = true.
  Proof.
    intros [pred stk] [pred' (fr', frs')] ha hf.
    eapply finalConfig_empty_stack in hf; eauto; subst.
    unfold approx in ha. destruct ha as [? [ctx heq]]; subst.
    injection heq; intros heq' ?; subst.
    apply app_eq_nil in heq'; destruct heq'; subst; auto.
  Qed.

  Lemma approx_predictions_eq :
    forall sp sp',
      approx sp' sp
      -> prediction sp' = prediction sp. 
  Proof.
    unfold approx; intros sp sp' ha; dms; destruct ha; auto.
  Qed.
  
  Definition overapprox (sps' sps : list subparser) : Prop :=
    forall sp, In sp sps -> exists sp', In sp' sps' /\ approx sp' sp.
  
  Lemma overapprox_finalConfig :
    forall sps sps' sps'' sps''',
      overapprox sps''' sps''
      -> filter finalConfig sps''  = sps
      -> filter finalConfig sps''' = sps'
      -> overapprox sps' sps.
  Proof.
    intros sps sps' sps'' sps''' ho hf hf' sp'' hi; subst.
    apply filter_In in hi; destruct hi as [hi hf].
    apply ho in hi; destruct hi as [sp''' [hi ha]].
    eexists; split; eauto.
    eapply approx_finalConfig_true in hf; eauto; apply filter_In; auto.
  Qed.

  Lemma overapprox_ape_pointwise :
    forall x y xs ys,
      overapprox (y :: ys) xs
      -> allPredictionsEqual y ys = true
      -> In x xs
      ->  prediction y = prediction x.
  Proof.
    intros x y xs ys ho ha hi.
    apply ho in hi; destruct hi as [y' [hi he]].
    apply eq_trans with (y := prediction y').
    - inv hi; auto.
      eapply allPredictionsEqual_prop in ha; firstorder.
    - apply approx_predictions_eq; auto.
  Qed.

  (* to do : refactor *)
  Lemma overapprox_allPredictionsEqual_big_small :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> allPredictionsEqual y ys = true
      -> allPredictionsEqual x xs = true.
  Proof.
    intros x y xs ys ho ha; unfold allPredictionsEqual; unfold allEqual.
    apply forallb_forall; intros pred hi.
    apply beqGamma_eq_iff.
    apply in_map_iff in hi; destruct hi as [x' [? hi]]; subst.
    apply eq_trans with (y := prediction y).
    - symmetry; eapply overapprox_ape_pointwise; eauto; apply in_eq.
    - eapply overapprox_ape_pointwise; eauto.
      apply in_cons; auto.
  Qed.

  Lemma overapprox_final_subparsers_succ_eq :
    forall sps sps' rhs rhs',
      overapprox sps' sps
      -> handleFinalSubparsers sps  = PredSucc rhs
      -> handleFinalSubparsers sps' = PredSucc rhs'
      -> rhs' = rhs.
  Proof.
    intros sps sps' rhs rhs' ho hl hs; unfold handleFinalSubparsers in *.
    destruct (filter _ sps)  as [| x xs] eqn:hf  ; tc.
    destruct (filter _ sps') as [| y ys] eqn:hf' ; tc.
    destruct (allPredictionsEqual x xs)  eqn:ha  ; tc; inv hl.
    destruct (allPredictionsEqual y ys)  eqn:ha' ; tc; inv hs.
    eapply overapprox_finalConfig in ho; eauto.
    eapply overapprox_ape_pointwise; eauto.
    apply in_eq.
  Qed.

  (*
  Lemma overapprox_allPredictionsEqual_false :
    forall sp sps sps',
      overapprox sps' sps
      -> allPredictionsEqual sp sps = false
      -> ~ all_predictions_equal sp sps'.
  Proof.
    intros sp sps sps' ho ha ha'.
    apply allPredictionsEqual_false_exists_diff_rhs in ha.
    destruct ha as [sp' [hi hneq]]; apply hneq; clear hneq.
    apply ho in hi; destruct hi as [sp'' [hi ha]]; clear ho.
    apply eq_trans with (y := prediction sp'').
    - symmetry; apply approx_predictions_eq; auto.
    - firstorder.
  Qed.
   *)

  (* try proving something about :
     ~ all_predictions_equal sp sps -> allPredictionsEqual sp sps = false *)
  Lemma overapprox_allPredictionsEqual_false :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> allPredictionsEqual x xs = false
      -> allPredictionsEqual y ys = false.
  Proof.
    intros x y xs ys ho ha.
    apply allPredictionsEqual_false_exists_diff_rhs in ha.
    destruct ha as [x' [hi hneq]].
  Abort.

  Lemma sllPredict'_llPredict'_succ_eq :
    forall g cm ts sps' sps ca ys ca' ys',
      no_left_recursion g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> exists_successful_sp g sps ts
      -> cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> llPredict' g sps ts = PredSucc ys
      -> sllPredict' g cm sps' ts ca = (PredSucc ys', ca')
      -> ys' = ys.
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH];
      intros sps' sps ca ys ca' ys' hn hw hs he hc ho hll hsll;
      pose proof hll as hll'; simpl in hll, hsll.
    - inv hsll; eapply overapprox_final_subparsers_succ_eq; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps  as [| sp  sps ]; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha'.
      + inv hsll.
        assert (ha : allPredictionsEqual sp sps = true).
        { eapply overapprox_allPredictionsEqual_big_small; eauto. }
        rewrite ha in hll; inv hll.
        eapply overapprox_ape_pointwise; eauto.
        apply in_eq.
      + apply esp_llPredict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        destruct (Cache.find _ _) as [sps''' |] eqn:hf.
        * apply hc in hf.
          eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- admit.
        * destruct (sllTarget _ _ _ _) as [?| sps'''] eqn:ht';tc.
          eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- eapply sllTarget_add_preserves_cache_invar; eauto.
          -- admit.
  Admitted.
  
  Lemma sllPredict_llPredict_succ_eq :
    forall g cm cr o x suf frs w ca rhs rhs' ca',
      cr = SF o (NT x :: suf)
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> llPredict g x (cr, frs) w = PredSucc rhs
      -> sllPredict g cm x w ca = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros g cm ? o x suf frs w ca rhs rhs' ca' ? hn hw hc hr hl hs; subst.
    unfold sllPredict in hs; unfold llPredict in hl.
    destruct (sllStartState _ _ _) as [? | sps'] eqn:hss'; tc.
    destruct (startState _ _ _) as [? | sps] eqn:hss; tc.
    eapply sllPredict'_llPredict'_succ_eq; eauto.
    - eapply startState_preserves_stacks_wf_invar; eauto.
    - eapply startState_all_stacks_stable; eauto.
    - eapply startState_preserves_esp_invar; eauto. 
    - (* overapprox should be true of sllStartState and llStartState *)
      admit.
  Admitted.

  Lemma sllPredict'_succ__llPredict'_neq_ambig :
    forall g cm ts sps sps' ca ca' ys ys',
      cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (PredSucc ys, ca')
      -> llPredict' g sps ts <> PredAmbig ys'.
  Proof.
    intros g cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca ca' ys ys' hc ho hs hl; sis.
    - inv hs.
      admit.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual sp sps) eqn:ha; tc.
      assert (Hass : allPredictionsEqual sp' sps' = false) by admit.
      rewrite Hass in hs.
      destruct (llTarget _ _ _) as [? | sps''] eqn:ht; tc.
      destruct (Cache.find _ _) as [sps''' |] eqn:hf.
      + apply hc in hf.
        eapply IH in hs; eauto. 
        (* lemma : sllTarget and llTarget preserve overapprox *)
        admit.
      + destruct (sllTarget _ _ _ _) as [? | sps'''] eqn:ht'; tc.
        eapply IH in hs; eauto.
        * eapply sllTarget_add_preserves_cache_invar; eauto.
        * (* same lemma as above *)
          admit.
  Admitted.

  Lemma sllPredict_succ__llPredict_neq_ambig :
    forall g cm x fr frs ts ca ys ca' ys',
      cache_stores_target_results g cm ca
      -> sllPredict g cm x ts ca = (PredSucc ys, ca')
      -> llPredict g x (fr, frs) ts <> PredAmbig ys'.
  Proof.
    intros g cm x fr frs ts ca ys ca' ys' hc hs hl.
    unfold sllPredict in hs; unfold llPredict in hl.
    destruct (sllStartState _ _ _) as [? | sps'] eqn:hss'; tc.
    destruct (startState _ _ _) as [? | sps]     eqn:hss ; tc.
    eapply sllPredict'_succ__llPredict'_neq_ambig; eauto.
    (* lemma : overapprox holds after sllStartState, llStartState *)
    admit.
  Admitted.
  
    Lemma sllPredict_succ_eq_llPredict_succ :
    forall g cm cr o x suf frs w ca rhs ca',
      cr = SF o (NT x :: suf)
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> sllPredict g cm x w ca = (PredSucc rhs, ca')
      -> llPredict g x (cr, frs) w = PredSucc rhs.
  Proof.
    intros g cm ? o x suf frs w ca rhs' ca' ? hn hw hc hr hs; subst.
    destruct (llPredict _ _ _ _) as [rhs | rhs | | e] eqn:hl.
    - symmetry; f_equal; eapply sllPredict_llPredict_succ_eq; eauto.
    - exfalso; eapply sllPredict_succ__llPredict_neq_ambig; eauto.
    - exfalso; eapply ussr_llPredict_neq_reject; eauto.
    - exfalso; eapply llPredict_never_returns_error; eauto.
  Qed.

  Lemma adaptivePredict_succ_eq_llPredict_succ :
    forall g cm cr x o suf frs w ca rhs ca',
      cr = SF o (NT x :: suf)
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> adaptivePredict g cm x (cr, frs) w ca = (PredSucc rhs, ca')
      -> llPredict g x (cr, frs) w = PredSucc rhs.
  Proof.
    intros g cm ? x o suf frs w ca rhs ca' ? hn hw hc hr ha; subst.
    unfold adaptivePredict in ha.
    destruct (sllPredict _ _ _ _ _) as ([? | ? | | ?], ?) eqn:hs; tc; inv ha.
    eapply sllPredict_succ_eq_llPredict_succ; eauto.
  Qed.

  Lemma adaptivePredict_succ_at_most_one_rhs_applies :
    forall g cm cr o x suf frs w ca rhs rhs' ca',
      cr = SF o (NT x :: suf)
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> In (x, rhs) g
      -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms frs) w
      -> adaptivePredict g cm x (cr, frs) w ca = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros g cm ? o x suf frs w ca rhs rhs' ca' ? hn hw hc hi hr ha; subst.
    eapply adaptivePredict_succ_eq_llPredict_succ in ha; eauto.
    - eapply llPredict_succ_at_most_one_rhs_applies; eauto.
    - eapply gamma_recognize_fold_head_nt; eauto.
  Qed.

  Lemma adaptivePredict_ambig_llPredict_ambig :
    forall g cm x ss w ca rhs ca',
      adaptivePredict g cm x ss w ca = (PredAmbig rhs, ca')
      -> llPredict g x ss w = PredAmbig rhs.
  Proof.
    unfold adaptivePredict; intros; dms; tc. 
  Qed.
  
End SllOptimizationSoundFn.
