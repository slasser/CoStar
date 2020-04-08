Require Import List.
Require Import GallStar.Lex.
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
    - eapply overapprox_ape_pointwise; eauto; apply in_cons; auto.
  Qed.

  Lemma overapprox_final_subparsers_succ_eq :
    forall sps sps' rhs rhs',
      overapprox sps' sps
      -> handleFinalSubparsers sps  = PredSucc rhs
      -> handleFinalSubparsers sps' = PredSucc rhs'
      -> rhs' = rhs.
  Proof.
    intros sps sps' rhs rhs' ho hl hs; unfold handleFinalSubparsers in *.
    destruct (filter _ sps ) as [| x xs] eqn:hf  ; tc.
    destruct (filter _ sps') as [| y ys] eqn:hf' ; tc.
    destruct (allPredictionsEqual x xs)  eqn:ha  ; tc; inv hl.
    destruct (allPredictionsEqual y ys)  eqn:ha' ; tc; inv hs.
    eapply overapprox_finalConfig in ho; eauto.
    eapply overapprox_ape_pointwise; eauto; apply in_eq.
  Qed.
  
  Lemma overapprox_allPredictionsEqual_false :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> allPredictionsEqual x xs = false
      -> allPredictionsEqual y ys = false.
  Proof.
    intros x y xs ys ho ha.
    apply ape_false__allPredictionsEqual_false; intros ha'.
    apply allPredictionsEqual_false_exists_diff_rhs in ha.
    destruct ha as [x' [hi hneq]]; apply hneq; clear hneq.
    apply eq_trans with (y := prediction y).
    (* These could probably be lemmas *)
    - apply in_cons with (a := x) in hi.
      apply ho in hi; destruct hi as [y' [hi hx]].
      apply approx_predictions_eq in hx.
      apply ape_cons_head_eq in ha'; apply ha' in hi; tc.
    - assert (hh : In x (x :: xs)) by apply in_eq.
      apply ho in hh; destruct hh as [y' [hh hx]].
      apply approx_predictions_eq in hx.
      apply ape_cons_head_eq in ha'; apply ha' in hh; tc.
  Qed.

  Lemma overapprox_handleFinalSubparsers_contra :
    forall xs ys rhs rhs',
      overapprox ys xs
      -> handleFinalSubparsers ys = PredSucc rhs'
      -> handleFinalSubparsers xs <> PredAmbig rhs.
  Proof.
    intros xs ys rhs rhs' ho hh' hh; unfold handleFinalSubparsers in *.
    destruct (filter _ ys) as [| y' ys'] eqn:hf'; tc.
    destruct (filter _ xs) as [| x' xs'] eqn:hf ; tc.
    eapply overapprox_finalConfig in ho; eauto.
    destruct (allPredictionsEqual x' xs') eqn:ha; tc; inv hh.
    eapply overapprox_allPredictionsEqual_false in ha; eauto.
    rewrite ha in hh'; tc.
  Qed.

  (* refactor *)
  Lemma approx_moveSp :
    forall a x x' y,
      approx y x
      -> moveSp a x = MoveSucc x'
      -> exists y',
          moveSp a y = MoveSucc y'
          /\ approx y' x'.
  Proof.
    intros a x x' y hx hm; unfold moveSp in hm.
    dms; tc; inv hm.
    destruct y as [pred (fr, frs)]; simpl in hx.
    destruct hx as [? [ctx heq]]; inv heq.
    eexists; split.
    - unfold moveSp; dm; tc.
    - firstorder; eexists; eauto.
  Qed.
  
  Lemma move_preserves_overapprox :
    forall a xs xs' ys ys',
      overapprox ys xs
      -> move a xs = inr xs'
      -> move a ys = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros a xs xs' ys ys' ho hm hm' x' hi.
    eapply aggrMoveResults_map_backwards in hi; eauto.
    destruct hi as [x [hi hm'']].
    apply ho in hi; destruct hi as [y [hi hx]].
    eapply approx_moveSp in hm''; eauto.
    destruct hm'' as [y' [hm'' hx']].
    eapply aggrMoveResults_succ_all_sps_step in hm''; eauto.
  Qed.

  Lemma llc_sllc_approx :
    forall g cm av av' x y xs' ys' a a',
      approx y x
      -> spClosure g av x a  = inr xs'
      -> sllc' g cm av' y a' = inr ys'
      -> overapprox ys' xs'.
  Admitted.
  
  Lemma closure_preserves_overapprox :
    forall g cm xs xs' ys ys',
      overapprox ys xs
      -> llClosure g xs = inr xs'
      -> sllClosure g cm ys = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros g cm xs xs'' ys ys'' ho hl hc x'' hi.
    unfold llClosure in hl.
    unfold sllClosure in hc.
    eapply aggrClosureResults_map_backwards in hi; eauto.
    destruct hi as [x [xs' [hi [hc' hi']]]].
    apply ho in hi; destruct hi as [y [hi hyx]].
    eapply aggrClosureResults_map_succ_elt_succ in hc; eauto.
    destruct hc as [ys' [hs' ha]].
    eapply llc_sllc_approx in hs'; eauto.
    apply hs' in hi'; destruct hi' as [? [? ? ]]; eauto.
  Qed.
  
  (* probably need some invariant about closure_map here *)
  Lemma target_preserves_overapprox :
    forall g cm sps sps' sps'' sps''' a,
      overapprox sps' sps
      -> llTarget g a sps = inr sps''
      -> sllTarget g cm a sps' = inr sps'''
      -> overapprox sps''' sps''.
  Proof.
    intros g cm xs ys xs'' ys'' a ho hl hs.
    unfold llTarget in hl; unfold sllTarget in hs.
    destruct (move a xs) as [? | xs'] eqn:hm  ; tc.
    destruct (move a ys) as [? | ys'] eqn:hm' ; tc.
    destruct (llClosure _ _   ) eqn:hc ; tc; inv hl.
    destruct (sllClosure _ _ _) eqn:hc'; tc; inv hs.
    eapply move_preserves_overapprox in hm'; eauto.
    eapply closure_preserves_overapprox; eauto.
  Qed.

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
          -- eapply target_preserves_overapprox; eauto.
        * destruct (sllTarget _ _ _ _) as [?| sps'''] eqn:ht';tc.
          eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- eapply sllTarget_add_preserves_cache_invar; eauto.
          -- eapply target_preserves_overapprox; eauto. 
  Qed.
  
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
    - inv hs; eapply overapprox_handleFinalSubparsers_contra; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual sp sps) eqn:ha; tc.
      eapply overapprox_allPredictionsEqual_false in ha; eauto.
      rewrite ha in hs.
      destruct (llTarget _ _ _) as [? | sps''] eqn:ht; tc.
      destruct (Cache.find _ _) as [sps''' |] eqn:hf.
      + apply hc in hf.
        eapply IH in hs; eauto.
        eapply target_preserves_overapprox; eauto.
      + destruct (sllTarget _ _ _ _) as [? | sps'''] eqn:ht'; tc.
        eapply IH in hs; eauto.
        * eapply sllTarget_add_preserves_cache_invar; eauto.
        * eapply target_preserves_overapprox; eauto. 
  Qed.

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
