Require Import List.
Require Import GallStar.SLLPrediction.
Require Import GallStar.Tactics.
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

  Definition overapprox (sps' sps : list subparser) : Prop :=
    forall sp, In sp sps -> exists sp', In sp' sps' /\ approx sp' sp.

  Lemma sllPredict'_llPredict'_succ_eq :
    forall g cm ts sps' sps ca ys ca' ys',
      all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> exists_successful_sp g sps ts
      -> cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> llPredict' g sps ts = PredSucc ys
      -> sllPredict' g cm sps' ts ca = (PredSucc ys', ca')
      -> ys' = ys.
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH];
      intros sps' sps ca ys ca' ys' hw hs he hc ho hll hsll;
      pose proof hll as hll'; simpl in hll, hsll.
    - (* no more tokens left *)
      (* lemma *)
      inv hsll.
      admit.
    - (* there's a head token left *)
      destruct sps' as [| sp' sps']; tc.
      destruct sps  as [| sp  sps ]; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha'.
      + inv hsll.
        (* sp :: sps must all be equal *)
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        rewrite Hass in hll; inv hll.
        admit.
      + clear hll.
        assert (Hass : exists sps'', llTarget g a (sp :: sps) = inr sps''
                                     /\ (llPredict' g sps'' ts = PredSucc ys \/ llPredict' g sps'' ts = PredReject)) by admit.
        clear hll'.
        destruct Hass as [sps'' [ht [hsuc | hrej]]].
        * destruct (Cache.find _ _) as [sps''' |] eqn:hf.
          -- apply hc in hf.
             eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
             ++ eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
             ++ eapply llTarget_preserves_stacks_stable_invar; eauto.
             ++ eapply llTarget_preserves_successful_sp_invar; eauto.
             ++ admit.
          -- destruct (sllTarget _ _ _ _) as [?| sps'''] eqn:ht';tc.
             eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
             ** eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
             ** eapply llTarget_preserves_stacks_stable_invar; eauto.
             ** eapply llTarget_preserves_successful_sp_invar; eauto.
             ** eapply sllTarget_add_preserves_cache_invar; eauto.
             ** admit.
        * exfalso.
          eapply exists_successful_sp_llPredict'_neq_reject with (sps := sps''); eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
  Admitted.

  (* maybe change this to gamma_recognize rhs ++ ... *)
  (* next: write a lemma that does case analysis on the
     llPredict result to show that it must be equal to
     the sllPredict result *)
  (*
  Lemma sllPredict_succ_at_most_one_rhs_applies :
    forall g cm cr ce frs o x suf w rhs rhs' ca ca',
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> llPredict g x (cr, frs) w = PredSucc rhs
      -> sllPredict g cm x w ca    = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros g cm ? ? frs o x suf w rhs rhs' ca ca' ? ?
           hn hw hc hr hl hs; subst.
    unfold llPredict in hl; unfold sllPredict in hs.
    destruct (startState _ _ _) as [? | sps] eqn:hss; tc.
    destruct (sllStartState _ _ _) as [? | sps'] eqn:hss'; tc.
    eapply sllPredict'_llPredict'_succ_eq with
        (sps := sps) (sps' := sps'); eauto.
    - eapply startState_preserves_stacks_wf_invar; eauto. 
    - eapply startState_all_stacks_stable; eauto. 
    - (* lemma *)
      eapply closure_preserves_successful_sp_invar; eauto.
      eapply initSps_preserves_exists_successful_sp_invar; eauto.
    - (* lemma : startState preserves overapprox invar *)
      admit.
  Admitted.
   *)
  
  Lemma sllPredict_llPredict_succ_eq :
    forall g cm cr o x suf frs w ca rhs rhs' ca',
      cr = SF o (NT x :: suf)
      -> suffix_stack_wf g (cr, frs)
      -> cache_stores_target_results g cm ca
      -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
      -> llPredict g x (cr, frs) w = PredSucc rhs
      -> sllPredict g cm x w ca = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros g cm ? o x suf frs w ca rhs rhs' ca' ? hw hc hr hl hs; subst.
    unfold sllPredict in hs; unfold llPredict in hl.
    destruct (sllStartState _ _ _) as [? | sps'] eqn:hss'; tc.
    destruct (startState _ _ _) as [? | sps] eqn:hss; tc.
    eapply sllPredict'_llPredict'_succ_eq; eauto.
    - eapply startState_preserves_stacks_wf_invar; eauto.
    - eapply startState_all_stacks_stable; eauto.
    - (* lemma *)
      eapply closure_preserves_successful_sp_invar; eauto.
      eapply initSps_preserves_exists_successful_sp_invar; eauto.
    - (* overapprox should be true of sllStartState and llStartState *)
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
    - exfalso. admit.
    - exfalso; eapply ussr_llPredict_neq_reject; eauto.
    - exfalso; eapply llPredict_never_returns_error; eauto.
  Admitted.

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
