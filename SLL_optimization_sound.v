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

  (*
  (* need some more invariants here *)
  Lemma sllPredict'_overapprox_llPredict' :
    forall g cm ts sps' sps ca ca' sll_res ll_res,
      cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (sll_res, ca')
      -> llPredict' g sps ts = ll_res
      -> match sll_res with
         | PredAmbig ys => True
         | PredSucc ys  =>
           ll_res = PredSucc ys \/ ll_res = PredReject
         | PredReject =>
           ll_res = PredReject
         | PredError e =>
           True
         end.
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH]; intros sps' sps ca ca' sll_res ll_res hc ho hs hl; sis.
    - (* no more tokens left *)
      destruct sps as [| sp sps]; subst.
      + destruct sps' as [| sp' sps'].
        * inv hs; auto.
        * destruct (allPredictionsEqual sp' sps') eqn:ha'; inv hs; auto.
          dm; auto.
      + destruct sps' as [| sp' sps'].
        * (* overapprox contra *)
          admit.
        * destruct (allPredictionsEqual sp' sps') eqn:ha'; inv hs; auto.
          -- assert (Hass : allPredictionsEqual sp sps = true) by admit.
          rewrite Hass.
          admit.
          -- dmeq hh; auto.
             ++ unfold handleFinalSubparsers in hh. dmeqs H; tc; auto.
                ** inv hh.
          assert (
          -- inv hs; auto.
          -- 
      + destruct 
        * inv hs.
          
      destruct sps' as [| sp' sps']; destruct sps as [| sp sps]; inv hs; auto.
            destruct sps as [| sp sps]; auto.
      destruct (allPredictionsEqual sp' sps') eqn:ha.
      + (* overapprox + SLL allPredictionsEqual = LL allPredictionsEqual *)
        inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        admit.
      + inv hs. rename H0 into hh.
        unfold handleFinalSubparsers in *.
        (* handleFinalSubparsers will extract the sps in final
           configurations, and the resulting ones will have
           allPredictionsEqual = true, so allPredictionsEqual
           will also be true for the LL subparsers in final 
           configurations *)
        admit.
    - (* there's a head token left *)
      destruct sps  as [| sp sps]; auto.
      destruct sps' as [| sp' sps']; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha'.
      + inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        (* same as the case above *)
        admit.
      + destruct (allPredictionsEqual sp sps) eqn:ha in hl.
        * (* tricky case: LL prediction has converged on a 
             prediction, but SLL prediction hasn't *)
          (* maybe we can prove that if llPredict' returns 
             PredSucc ys when there's a token left, then 
             llPredict' on the tail returns either the same prediction 
             or reject *)
          destruct (Cache.find _ _) as [sps''' |] eqn:hf.
          -- apply hc in hf.
             subst. left.
             
             assert (Hass : exists sps'' ll_r,
                        llPredict' g sps'' ts = ll_r
                        /\ (ll_r = PredSucc (prediction sp)
                            \/ ll_r = PredReject)) by admit.
             destruct Hass as [sps'' [ll_r' [ heq htail]]].
             eapply IH with (sps := sps'')
                            (ll_r := ll_r') in hs; eauto.
             ++ destruct hs; destruct htail; subst.
                ** inv H0; auto.
                ** inv H0.
                ** inv H0.
                ** right. rewrite <- hl'. rewrite <- heq.
             ++ 
             destruct htail as [hsuc | hrej].
             ++ subst.
                eapply IH with (sps := sps'') in hs; eauto.
                (* overapprox invariant is preserved *)
                admit.
             ++ eapply IH with (sps := sps'')
                               (ll_r := ll_r') in hs; eauto.
                ** subst.
                   left.
                   admit.
                ** admit.
          -- 
                ** subst.
                eapp
                (ll_r := ll_r') in hs; eauto.
             clear hl. clear hl'.

             ++ eapply IH with (sps  := sps''); eauto.
                               (ll_r := PredSucc (prediction sp)) in hs; eauto.
                ** admit.
                ** 
          assert (Hass : exists sps'', llPredict' g sps'' ts =
                                       PredSucc (prediction sp) \/ llPredict' g sps'' ts = PredReject) by admit.
          destruct Hass as [sps'' htail].
          destruct (Cache.find _ _) as [sps''' |] eqn:hf.
          -- apply hc in hf.
             destruct htail.
             ++ eapply IH with (sps := sps'') in hs; eauto.
                ** (* invariant preserved *)
                  admit.
                ** subst; auto.
             ++ eapply IH with (sps := sps'') (ll_r := PredReject) in hs; eauto.
                ** subst; auto.
        * eapply IH in hs; eauto.
        inv hs.
inv hs.

    
         | ll_r = PredSucc ys \/ ll_r = PredReject.
  Proof.
   *)

  (* to do : maybe I should redefine llPredict'
     and sllPredict' so that they call handleFinalSubparsers
     right away when the remaining token list is empty *)
  (* need some more invariants here *)
  Lemma sllPredict'_succ_llPredict'_succ_or_reject :
    forall g cm ts sps' sps ca ys ca' ll_r,
      cache_stores_target_results g cm ca
      -> overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (PredSucc ys, ca')
      -> llPredict' g sps ts = ll_r
      -> ll_r = PredSucc ys \/ ll_r = PredReject.
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH]; intros sps' sps ca ys ca' ll_r hc ho hs hl; simpl in hs; pose proof hl as hl'; simpl in hl.
    - (* no more tokens left *)
      destruct sps as [| sp sps]; auto.
      destruct sps' as [| sp' sps']; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha.
      + (* overapprox + SLL allPredictionsEqual = LL allPredictionsEqual *)
        inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        admit.
      + inv hs. rename H0 into hh.
        unfold handleFinalSubparsers in *.
        (* handleFinalSubparsers will extract the sps in final
           configurations, and the resulting ones will have
           allPredictionsEqual = true, so allPredictionsEqual
           will also be true for the LL subparsers in final 
           configurations *)
        destruct (allPredictionsEqual sp sps) eqn:ha'.
        * dmeqs H; tc. inv hh.
        admit.
    - (* there's a head token left *)
      destruct sps  as [| sp sps]; auto.
      destruct sps' as [| sp' sps']; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha'.
      + inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        (* same as the case above *)
        admit.
      + destruct (allPredictionsEqual sp sps) eqn:ha in hl.
        * (* tricky case: LL prediction has converged on a 
             prediction, but SLL prediction hasn't *)
          (* maybe we can prove that if llPredict' returns 
             PredSucc ys when there's a token left, then 
             llPredict' on the tail returns either the same prediction 
             or reject *)
          destruct (Cache.find _ _) as [sps''' |] eqn:hf.
          -- apply hc in hf.
             subst. left.
             
             assert (Hass : exists sps'' ll_r,
                        llPredict' g sps'' ts = ll_r
                        /\ (ll_r = PredSucc (prediction sp)
                            \/ ll_r = PredReject)) by admit.
             destruct Hass as [sps'' [ll_r' [ heq htail]]].
             eapply IH with (sps := sps'')
                            (ll_r := ll_r') in hs; eauto.
             ++ destruct hs; destruct htail; subst.
                ** inv H0; auto.
                ** inv H0.
                ** inv H0.
                ** right. rewrite <- hl'. rewrite <- heq.
             ++ 
             destruct htail as [hsuc | hrej].
             ++ subst.
                eapply IH with (sps := sps'') in hs; eauto.
                (* overapprox invariant is preserved *)
                admit.
             ++ eapply IH with (sps := sps'')
                               (ll_r := ll_r') in hs; eauto.
                ** subst.
                   left.
                   admit.
                ** admit.
          -- 
                ** subst.
                eapp
                (ll_r := ll_r') in hs; eauto.
             clear hl. clear hl'.

             ++ eapply IH with (sps  := sps''); eauto.
                               (ll_r := PredSucc (prediction sp)) in hs; eauto.
                ** admit.
                ** 
          assert (Hass : exists sps'', llPredict' g sps'' ts =
                                       PredSucc (prediction sp) \/ llPredict' g sps'' ts = PredReject) by admit.
          destruct Hass as [sps'' htail].
          destruct (Cache.find _ _) as [sps''' |] eqn:hf.
          -- apply hc in hf.
             destruct htail.
             ++ eapply IH with (sps := sps'') in hs; eauto.
                ** (* invariant preserved *)
                  admit.
                ** subst; auto.
             ++ eapply IH with (sps := sps'') (ll_r := PredReject) in hs; eauto.
                ** subst; auto.
        * eapply IH in hs; eauto.
        inv hs.
inv hs.
        
  Admitted.

  
  (* need some more invariants here *)
  Lemma sllPredict'_succ_llPredict'_succ_or_reject :
    forall g cm ts sps' sps ca ys ca',
      overapprox sps' sps
      -> sllPredict' g cm sps' ts ca = (PredSucc ys, ca')
      -> llPredict' g sps ts = PredSucc ys
         \/ llPredict' g sps ts = PredReject.
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH]; intros sps' sps ca ys ca' ho hs; simpl in hs.
    - (* no more tokens left *)
      destruct sps as [| sp sps]; auto.
      destruct sps' as [| sp' sps']; tc.
      destruct (allPredictionsEqual _ _) eqn:ha.
      + (* overapprox + SLL allPredictionsEqual = LL allPredictionsEqual *)
        inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        admit.
      + inv hs. rename H0 into hh.
        unfold handleFinalSubparsers in *.
        (* handleFinalSubparsers will extract the sps in final
           configurations, and the resulting ones will have
           allPredictionsEqual = true, so allPredictionsEqual
           will also be true for the LL subparsers in final 
           configurations *)
        admit.
    - (* there's a head token left *)
      destruct sps as [| sp sps]; auto.
      destruct sps' as [| sp' sps']; tc.
      destruct (allPredictionsEqual sp' sps') eqn:ha'.
      + inv hs.
        assert (Hass : allPredictionsEqual sp sps = true) by admit.
        simpl. rewrite Hass.
        (* same as the case above *)
        admit.
      + simpl. subst.
        destruct (allPredictionsEqual sp sps) eqn:ha.
        * (* tricky case: LL prediction has converged on a 
             prediction, but SLL prediction hasn't *)
        destruct (Cache.find _ _) as [sps'' |] eqn:hf.
        * eapply IH in hs; eauto.
        inv hs.
inv hs.
        
  Admitted.

  Lemma sllPredict_succ_llPredict_succ_or_reject :
    forall g cm ss o x suf frs ts ca ys ca',
      ss = (SF o (NT x :: suf), frs)
      -> no_left_recursion g
      -> suffix_stack_wf g ss
      -> sllPredict g cm x ts ca = (PredSucc ys, ca')
      -> llPredict g x ss ts  = PredSucc ys
         \/ llPredict g x ss ts  = PredReject.
  Proof.
    intros g cm ss o x suf frs ts ca ys ca' ? hn hw hp; subst.
    unfold llPredict; unfold sllPredict in hp; dmeqs H; tc; inv hp.
    - exfalso; eapply startState_never_returns_error; eauto.
    - eapply sllPredict'_succ_llPredict'_succ_or_reject; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_llPredict_succ_or_reject :
    forall g cm x ss ts ca ys ca',
      adaptivePredict g cm x ss ts ca = (PredSucc ys, ca')
      -> llPredict g x ss ts = PredSucc ys
         \/ llPredict g x ss ts = PredReject.
  Proof.
    intros g cm x ss ts ca ys ca' hp.
    unfold adaptivePredict in hp; dmeqs H; tc; inv hp; auto.
    eapply sllPredict_succ_llPredict_succ_or_reject; eauto.
  Qed.

End SllOptimizationSoundFn.

        
(*
Lemma sll'_ll'_equiv_succ :
    forall g cm sps sps' ts c c' ys,
      sllPredict' g cm sps ts c = (PredSucc ys, c')
      -> llPredict' g sps' ts = PredReject
         \/llPredict' g sps' ts = PredSucc ys.
  Proof.
    intros g cm sps sps' ts c c' ys hs.
    unfold sllPredict' in hs.
    induction ts as [| t ts IH].
    - destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual sp sps) eqn:ha.
      + (* SLL all equal *)
        inv hs.
        destruct sps' as [| sp' sps']; auto.
        right. simpl.
        (* an invariant relating the LL and SLL subaparsers
           should prove that SLL all equal -> LL all equal *)
  Abort.

  (* Equivalence of LL and SLL *)
(*
Lemma sll'_ll'_equiv_succ :
  forall g cm sps sps' ts c c' ys,
    
sllPredict' g cm sps ts c = (PredSucc ys, c')
    -> llPredict' g sps' ts = PredReject
       \/llPredict' g sps' ts = PredSucc ys.
Proof.
  intros g cm sps sps' ts c c' ys hs.
  unfold SLL.sllPredict' in hs.
  induction ts as [| t ts IH].
  - destruct sps as [| sp sps]; tc.
    destruct (SLL.allPredictionsEqual sp sps) eqn:ha.
    + (* SLL all equal *)
      destruct sps' as [| sp' sps']; auto.
      right.
Abort.

Lemma sll_ll_equiv_succ :
  forall g cm fr frs x suf ts c c' ys,
    no_left_recursion g
    -> suffix_stack_wf g (fr, frs)
    -> fr = SF (NT x :: suf)
    -> SLL.sllPredict g cm x ts c = (PredSucc ys, c')
    -> llPredict g x (fr, frs) ts = PredSucc ys.
Proof.
  intros g cm fr frs x suf ts c c' ys hn hw ? hs; subst.
  unfold SLL.sllPredict in hs.
  destruct (SLL.startState g cm x) as [e | sps] eqn:hss; tc.
  unfold llPredict.
  destruct (startState g x _) as [e | sps'] eqn:hss'.
  - (* lemma *)
    destruct e as [ | x'].
    + exfalso; eapply startState_never_returns_SpInvalidState; eauto.
    + exfalso; eapply closure_never_finds_left_recursion; eauto.
  - (* what do we know at this point?
         - sllPredict' succeeded, so there must be an sp in sps with label ys
         - there must also be an sp' in sps' with label ys *)
    admit.
Abort.

Lemma adaptivePredict_equiv_llPredict :
  forall g cm x stk ts c c' r,
    SLL.adaptivePredict g cm x stk ts c = (r, c')
    -> llPredict g x stk ts = r.
Proof.
  intros g cm x stk ts c c' r ha.
  unfold SLL.adaptivePredict in ha.
  destruct (SLL.sllPredict _ _ _ _ _) as (r', c'') eqn:hs.
  destruct r' as [ys | ys | | e]; inv ha; auto.
  - (* PredSucc *)
    admit.
  - admit.
  - admit.
Admitted.
*)
*)
