Require Import List Relation_Operators Operators_Properties.
Require Import CoStar.Lex.
Require Import CoStar.SLLPrediction.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
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

  Fixpoint sllify (frs : list parser_frame) : list sll_frame :=
    match frs with
    | [] => []
    | Fr _ _ suf :: frs' =>
      match frs' with
      | [] => [SllFr None suf]
      | Fr _ _ (NT x :: _) :: _ =>
        SllFr (Some x) suf :: sllify frs'
      (* impossible for a well-formed parser stack *)
      | _ => []
      end
    end.

  Lemma sllifyHead_cons__sllify_cons : forall g fr frs,
      stack_wf g (fr, frs)
      -> sllifyHead (fr, frs) :: sllify frs = sllify (fr :: frs).
  Proof.
    intros g [pre vs suf] frs hw.
    sis.
    destruct frs as [| [pre_cr vs_cr suf_cr] frs].
    - auto.
    - destruct suf_cr as [| [a|x] suf_cr]; inv hw; auto.
  Qed.

  Definition approx (sp' : sll_subparser) (sp : subparser) : Prop :=
    match sp', sp with
    | SllSp pred' (fr', frs'), Sp pred (fr, frs) =>
      pred' = pred
      /\ exists ctx, fr' :: frs' ++ ctx = sllify (fr :: frs)
    end.

  Lemma approx_inv :
    forall pred pre vs suf frs pred' o' suf' frs',
      approx (SllSp pred' (SllFr o' suf', frs')) (Sp pred (Fr pre vs suf, frs))
      -> pred' = pred
         /\ suf' = suf
         /\ ((frs = [] /\ frs' = [] /\ o' = None)
             \/ (exists pre_cr vs_cr x suf_cr frs'' ctx,
                    frs = Fr pre_cr vs_cr (NT x :: suf_cr) :: frs''
                    /\ o' = Some x
                    /\ frs' ++ ctx = sllify (Fr pre_cr vs_cr (NT x :: suf_cr) :: frs''))).
  Proof.
    intros pred pre vs suf frs pred' o' suf' frs' ha.
    red in ha.
    destruct ha as [heq [ctx heq']]; subst.
    split; auto.
    eauto 20.
    destruct frs as [| [pre_cr vs_cr [| [a|x] suf_cr]] frs'']; inv heq'; eauto 12.
    match goal with
    | H : ?xs ++ ?ys = [] |- _ =>
      apply app_eq_nil in H; destruct H; subst
    end; auto.
  Qed.

  Lemma approx_finalConfig_true :
    forall sp sp',
      approx sp' sp
      -> finalConfig sp  = true
      -> sllFinalConfig sp' = true.
  Proof.
    intros [pred stk] [pred' (fr', frs')] ha hf.
    eapply finalConfig_empty_stack in hf; eauto.
    destruct hf as (pre & vs & heq); subst.
    unfold approx in ha. destruct ha as [? [ctx heq]]; subst; sis.
    injection heq; intros heq' ?; subst.
    apply app_eq_nil in heq'; destruct heq'; subst; auto.
  Qed.

  Lemma approx_predictions_eq :
    forall sp sp',
      approx sp' sp
      -> sll_pred sp' = prediction sp.
  Proof.
    unfold approx; intros sp sp' ha; dms; destruct ha; auto.
  Qed.

  Lemma approx_moveSp :
    forall a l x x' y,
      approx y x
      -> moveSp (@existT _ _ a l) x = MoveSucc x'
      -> exists y',
          sllMoveSp a y = MoveSucc y'
          /\ approx y' x'.
  Proof.
    intros a l [pred ([pre vs suf], frs)] x' [pred' ([o' suf'], frs')] hx hm; unfold moveSp in hm; dms; tc; inv hm.
    apply approx_inv in hx.
    destruct hx as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      unfold sllMoveSp; dm; tc.
      eexists; split; eauto.
      split; auto.
      exists []; auto.
    - destruct hr as (pre_cr & vs_cr & x & suf_cr & frs'' & ctx & ? & ? & heq); subst. 
      unfold sllMoveSp; dm; tc.
      eexists; split; eauto.
      split; auto.
      exists ctx; rewrite heq; auto.
  Qed.

(*  Lemma approx_head_frames_eq :
    forall pred pred' fr fr' frs frs',
      approx (Sp pred' (fr', frs')) (Sp pred (fr, frs))
      -> fr' = fr.
  Proof.
    intros pred pred' fr fr' frs frs' ha.
    destruct ha as [? [? heq]]; inv heq; auto.
  Qed.
 *)

  Lemma approx_ll_done_simReturn_contra :
    forall gr hw rm cm vi sp sp' sps'',
      stack_wf gr (stack sp)
      -> approx sp' sp
      -> cstep gr hw rm vi sp = CstepDone
      -> simReturn cm sp' <> Some sps''.
  Proof.
    intros gr hw rm cm av [pred (fr, frs)] [pred' (fr', frs')] sps'' hw' ha hs hr.
    eapply cstepDone_stable_config in hs; eauto.
    apply simReturn_stack_shape in hr.
    destruct hr as [x heq]; simpl in heq.
    inv heq.
    destruct fr as [pre vs suf].
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); tc.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst; sis. 
      inv hs.
  Qed.

  Lemma approx_ll_done_sll_step_contra :
    forall gr hw rm vi vi' vi'' sp sp' sps'',
      stack_wf gr (stack sp)
      -> approx sp' sp
      -> cstep gr hw rm vi sp = CstepDone
      -> sllCstep rm vi' sp' <> CstepK vi'' sps''.
  Proof.
    intros gr hw rm vi vi' vi'' [pr ([pre vs suf], frs)] [pr' ([o' suf'], frs')] sps'' hw' ha hs hs'.
    eapply cstepDone_stable_config in hs; eauto.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      sis; dms; tc; inv hs; inv hs'.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      sis; dms; tc; inv hs; inv hs'.
  Qed.

  Lemma approx_ll_step_sll_done_contra :
    forall gr hw rm cm vi vi' vi'' x y xs',
      stack_wf gr (stack x)
      -> approx y x
      -> simReturn cm y = None
      -> cstep gr hw rm vi x = CstepK vi' xs'
      -> sllCstep rm vi'' y <> CstepDone.
  Proof.
    intros gr hw rm cm ? ? ? [pr (fr, frs)] [pr' (fr', frs')] xs' hw' ha hr hs hs'.
    sis; dms; tc; inv hs; inv hs'; destruct ha as [? [? heq]]; inv heq; inv hw.
  Qed.

  (* to do -- refactor *)
  Lemma approx_cstep :
    forall gr hw rm ax ax' ay ay' x x' y xs' ys',
      rhs_map_correct rm gr
      -> approx y x
      -> cstep gr hw rm ax x = CstepK ax' xs'
      -> sllCstep rm ay y = CstepK ay' ys'
      -> In x' xs'
      -> exists y', In y' ys' /\ approx y' x'.
  Proof.
    intros gr hw rm ax ax' ay ay' [pr ([pre vs suf], frs)] x' [pr' ([o' suf'], frs')] xs' ys'
           hc ha hs hs' hi.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr]); subst.
    - destruct hl as (? & ? & ?); subst.
      unfold cstep in *; unfold sllCstep in *; dmeqs H; tc; inv hs; inv hs'; try solve [inv hi].
      + exfalso.
        eapply NMF.in_find_iff; eauto.
        apply in_map_iff in hi; destruct hi as [ys [heq hi]]; subst.
        eapply rhssFor_in_iff in hi; eauto.
        red in hc.
        destruct hc as [hk [hs hc]].
        red in hk.
        red in hs.
        red in hc.
        apply hc in hi.
        destruct hi as [yss [hm hi]].
        eapply nm_mapsto_in; eauto.
      + apply in_map_iff in hi.
        destruct hi as [ys [heq hi]]; subst.
        eexists; split.
        * apply in_map_iff; eauto.
        * split; auto.
          exists []; auto.
    - destruct hr as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      unfold cstep in *; unfold sllCstep in *; dmeqs H; tc; inv hs; inv hs'; try solve [inv hi].
      + apply in_singleton_eq in hi; subst.
        eexists; split.
        * apply in_eq.
        * split; auto.
          destruct x3 as [| [pre_cr vs_cr [| [a'|x'] suf_cr]] frs'']; sis; inv H1; eauto.
      + exfalso.
        eapply NMF.in_find_iff; eauto.
        apply in_map_iff in hi; destruct hi as [ys [heq hi]]; subst.
        eapply rhssFor_in_iff in hi; eauto.
        red in hc.
        destruct hc as [hk [hs hc]].
        red in hk.
        red in hs.
        red in hc.
        apply hc in hi.
        destruct hi as [yss [hm hi]].
        eapply nm_mapsto_in; eauto.
      + apply in_map_iff in hi.
        destruct hi as [ys [heq hi]]; subst.
        eexists; split.
        * apply in_map_iff; eauto.
        * split; auto.
          eexists; auto.
          sis.
          rewrite H1; auto.
  Qed.

  Lemma stable_config__stable_sllifyHead :
    forall fr frs,
      stable_config (fr, frs) -> stable (sllifyHead (fr, frs)) = true.
  Proof.
    intros fr frs hs; inv hs; auto.
    destruct frs as [| [pre_cr vs_cr [| [a'|x'] suf_cr]] frs]; auto.
  Qed.

  (* refactor -- this should probably be several lemmas *)
  Lemma simReturn_approx :
    forall g cm av av' av'' x x' x'' y ys'',
      closure_map_complete g cm
      -> stack_wf g (stack x)
      -> approx y x
      -> closure_step g av x av' x'
      -> closure_multistep g av' x' av'' x''
      -> simReturn cm y = Some ys''
      -> exists y'', In y'' ys'' /\ approx y'' x''.
  Proof.
    intros g cm av av' av'' [pr ([pre vs suf], frs)] [pr' (fr', frs')] [pr'' (fr'', frs'')]
           [pr''' ([o''' suf'''], frs''')] ys'' hcm hw ha hs hm hr; simpl in hw.
    apply approx_inv in ha.
    destruct ha as (? & ? & [hl | hr']); subst.
    - exfalso.
      destruct hl as (? & ? & ?); subst.
      apply simReturn_stack_shape in hr.
      destruct hr as [x heq]; inv heq.
    - destruct hr' as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst.
      pose proof hr as hr'.
      apply simReturn_stack_shape in hr'.
      destruct hr' as [x' heq].
      simpl in heq.
      inv heq.
      simpl in H1. subst.
    assert (heq : pr'' = pr).
    { apply closure_step_preserves_label in hs; sis; subst.
      apply closure_multistep_preserves_label in hm; sis; subst; auto. } subst.
    assert (hw' : stack_wf g (fr', frs')).
    { apply closure_step_preserves_stack_wf_invar in hs; sis; auto. }
    assert (hw'' : stack_wf g (fr'', frs'')).
    { apply closure_multistep_preserves_stack_wf_invar in hm; auto. }
    assert (hst : stable_config (fr'', frs'')).
    { apply stable_config_after_closure_multistep in hm; sis; auto. }
    eapply closure_step__frame_step in hs; eauto.
    eapply closure_multistep__frame_step_trc in hm; eauto.
    assert (sllifyHead (Fr pre vs [], Fr x x0 (NT x' :: x2) :: x3) = SllFr (Some x') []).
    { simpl; auto. }
    rewrite H in hs.
    assert (hfm : frame_multistep g (SllFr (Some x') []) (sllifyHead (fr'', frs''))).
    { eapply clos_t_rt; eauto.
      apply clos_rt_rt1n_iff; auto. }
    exists (SllSp pr (sllifyHead (fr'', frs''), [])); split.
      + simpl in hr.
        inv hr.
        apply in_map_iff.
        eexists; split; eauto.
        unfold destFrames.
        pose proof hfm as hfm'.
        apply hcm in hfm'.
        destruct hfm' as [v [hf hi]].
        * apply stable_config__stable_sllifyHead; auto. 
        * apply FMF.find_mapsto_iff in hf.
          rewrite hf; auto.
      + red.
        split; auto.
        exists (sllify frs'').
        rewrite app_nil_l.
        eapply sllifyHead_cons__sllify_cons; eauto.
  Qed.

  Definition overapprox (sps' : list sll_subparser) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> exists sp', In sp' sps' /\ approx sp' sp.
  
  Lemma overapprox_finalConfig :
    forall sps sps' sps'' sps''',
      overapprox sps''' sps''
      -> filter finalConfig sps''  = sps
      -> filter sllFinalConfig sps''' = sps'
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
      -> allPredictionsEqual beqGamma sll_pred y ys = true
      -> In x xs
      ->  sll_pred y = prediction x.
  Proof.
    intros x y xs ys ho ha hi.
    apply ho in hi; destruct hi as [y' [hi he]].
    apply eq_trans with (y := sll_pred y').
    - inv hi; auto.
      eapply allPredictionsEqual_prop in ha.
      + firstorder.
      + apply beqGamma_eq_iff.
    - apply approx_predictions_eq; auto.
  Qed.

  Lemma overapprox_allPredictionsEqual_big_small :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> allPredictionsEqual beqGamma sll_pred y ys = true
      -> allPredictionsEqual beqGamma prediction x xs = true.
  Proof.
    intros x y xs ys ho ha; unfold allPredictionsEqual; unfold allEqual.
    apply forallb_forall; intros pred hi.
    apply beqGamma_eq_iff.
    apply in_map_iff in hi; destruct hi as [x' [? hi]]; subst.
    apply eq_trans with (y := sll_pred y).
    - symmetry; eapply overapprox_ape_pointwise; eauto; apply in_eq.
    - eapply overapprox_ape_pointwise; eauto; apply in_cons; auto.
  Qed.

  Lemma overapprox_final_subparsers_succ_eq :
    forall sps sps' rhs rhs',
      overapprox sps' sps
      -> handleFinalSubparsers sps     = PredSucc rhs
      -> sllHandleFinalSubparsers sps' = PredSucc rhs'
      -> rhs' = rhs.
  Proof.
    intros sps sps' rhs rhs' ho hl hs;
      unfold handleFinalSubparsers in *; unfold sllHandleFinalSubparsers in *.
    destruct (filter _ sps ) as [| x xs] eqn:hf  ; tc.
    destruct (filter _ sps') as [| y ys] eqn:hf' ; tc.
    destruct (allPredictionsEqual _ _ x xs)  eqn:ha  ; tc; inv hl.
    destruct (allPredictionsEqual _ _ y ys)  eqn:ha' ; tc; inv hs.
    eapply overapprox_finalConfig in ho; eauto.
    eapply overapprox_ape_pointwise; eauto; apply in_eq.
  Qed.
  
  Lemma overapprox_allPredictionsEqual_false :
    forall x y xs ys,
      overapprox (y :: ys) (x :: xs)
      -> allPredictionsEqual beqGamma prediction x xs = false
      -> allPredictionsEqual beqGamma sll_pred y ys = false.
  Proof.
    intros x y xs ys ho ha.
    apply ape_false__allPredictionsEqual_false; intros ha'.
    - apply beqGamma_eq_iff.
    - apply allPredictionsEqual_false_exists_diff_rhs in ha.
      destruct ha as [x' [hi hneq]]; apply hneq; clear hneq.
      apply eq_trans with (y := sll_pred y).
      (* These could probably be lemmas *)
      + apply in_cons with (a := x) in hi.
        apply ho in hi; destruct hi as [y' [hi hx]].
        apply approx_predictions_eq in hx.
        apply ape_cons_head_eq in ha'; apply ha' in hi; tc.
      + assert (hh : In x (x :: xs)) by apply in_eq.
        apply ho in hh; destruct hh as [y' [hh hx]].
        apply approx_predictions_eq in hx.
        apply ape_cons_head_eq in ha'; apply ha' in hh; tc.
      + apply beqGamma_eq_iff.
  Qed.

  Lemma overapprox_handleFinalSubparsers_contra :
    forall xs ys rhs rhs',
      overapprox ys xs
      -> sllHandleFinalSubparsers ys = PredSucc rhs'
      -> handleFinalSubparsers xs <> PredAmbig rhs.
  Proof.
    intros xs ys rhs rhs' ho hh' hh;
      unfold handleFinalSubparsers in *; unfold sllHandleFinalSubparsers in *.
    destruct (filter _ ys) as [| y' ys'] eqn:hf'; tc.
    destruct (filter _ xs) as [| x' xs'] eqn:hf ; tc.
    eapply overapprox_finalConfig in ho; eauto.
    destruct (allPredictionsEqual _ _ x' xs') eqn:ha; tc; inv hh.
    eapply overapprox_allPredictionsEqual_false in ha; eauto.
    rewrite ha in hh'; tc.
  Qed.
  
  Lemma move_preserves_overapprox :
    forall a l xs xs' ys ys',
      overapprox ys xs
      -> move (@existT _ _ a l) xs = inr xs'
      -> sllMove a ys = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros a l xs xs' ys ys' ho hm hm' x' hi.
    eapply aggrMoveResults_map_backwards in hi; eauto.
    destruct hi as [x [hi hm'']].
    apply ho in hi; destruct hi as [y [hi hx]].
    eapply approx_moveSp in hm''; eauto.
    destruct hm'' as [y' [hm'' hx']].
    eapply aggrMoveResults_succ_all_sll_sps_step in hm''; eauto.
  Qed.

  Lemma approx_overapprox_singleton :
    forall x y,
      approx y x
      -> overapprox [y] [x].
  Proof.
    intros x y ha ? hi; apply in_singleton_eq in hi; subst.
    eexists; split; [apply in_eq | auto].
  Qed.

  (* Interesting and complicated lemma -- make sure to write
     a note about it *)
  Lemma llc_sllc_approx_overapprox' :
    forall gr hw rm cm pr (a : Acc lex_nat_pair pr) vi vi' x y hk hk' xs' ys' a' a'',
      pr = ll_meas rm vi x
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (stack x)
      -> approx y x
      -> llc gr hw rm vi x hk a' = inr xs'
      -> sllc rm cm vi' y hk' a'' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros gr hw rm cm pr a''; induction a'' as [pr hlt IH].
    intros vix viy x y hk hk' xs''' ys''' a a'
           ? hp hm hw' hx hll hsll; subst.
    apply llc_success_cases in hll.
    destruct hll as [[hs ?] | [xs' [vix' [hs [? [? ha]]]]]]; subst.
    - (* the LL subparser is done *)
      apply sllc_success_cases in hsll.
      destruct hsll as [hr | [hr [[hs' ?] | [ys' [viy' [hs' [? [? ha']]]]]]]]; subst.
      + (* SLL subparser simulates a return -- contradiction *)
        exfalso; eapply approx_ll_done_simReturn_contra; eauto.
      + (* both subparsers are done -- easy *)
        apply approx_overapprox_singleton; auto.
      + (* SLL subparser steps -- contradiction *)
        exfalso; eapply approx_ll_done_sll_step_contra; eauto.
    - (* the LL subparser steps *)
      apply sllc_success_cases in hsll.
      destruct hsll as [hr | [hr [[hs' ?] | [ys' [viy' [hs' [? [? ha']]]]]]]]; subst.
      + (* INTERESTING CASE 
           SLL subparser simulates a return
           Prove a lemma about a correspondence between 
           simReturn and a cstep/llc operation *)
        intros x''' hi'''.
        eapply aggrClosureResults_succ_in_input in ha; eauto.
        destruct ha as [xs'' [hd hi'']].
        eapply dmap_in in hd; eauto.
        destruct hd as [x' [hi' [? hll]]].
        assert (Hcm : exists vix''',
                   closure_step gr vix x vix' x'
                   /\ closure_multistep gr vix' x' vix''' x''').
        { pose proof hs as hs''.
          eapply cstep_sound in hs''; eauto.
          eapply llc_sound_wrt_closure_multistep in hll; eauto.
          - destruct hll as [vix''' hcm]; eauto.
          - eapply closure_step_preserves_stack_wf_invar; eauto. }
        destruct Hcm as [vi''' [Hcs Hcm]].
        eapply simReturn_approx; eauto.
      + (* SLL subparser is done -- contradiction *)
        exfalso; eapply approx_ll_step_sll_done_contra; eauto.
      + (* both subparsers step -- IH *)
        intros x''' hi'''.
        eapply aggrClosureResults_succ_in_input in ha; eauto.
        destruct ha as [xs'' [hd hi'']].
        eapply dmap_in in hd; eauto.
        destruct hd as [x' [? [hi' hll]]].
        eapply approx_cstep in hi'; eauto.
        destruct hi' as [y' [hiy' hx']].
        eapply aggrClosureResults_dmap_succ_elt_succ in ha'; eauto.
        destruct ha' as [? [ys'' [hsll ha']]].
        eapply IH with (ys' := ys'') in hll; eauto.
        * apply hll in hi''; destruct hi'' as [y'' [hiy'' hx'']]; eauto.
        * eapply cstep_meas_lt; eauto.
        * eapply cstep_preserves_stack_wf_invar; eauto.
  Qed.

  Lemma llc_sllc_approx_overapprox :
    forall gr hw rm cm vi vi' x y hk hk' xs' ys' a a',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (stack x)
      -> approx y x
      -> llc gr hw rm vi x hk a = inr xs'
      -> sllc rm cm vi' y hk' a' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros; eapply llc_sllc_approx_overapprox' with (pr := ll_meas _ _ _); eauto.
  Qed.
  
  Lemma closure_preserves_overapprox :
    forall gr hw rm cm xs xs' ys ys' hk hk',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr xs
      -> overapprox ys xs
      -> llClosure gr hw rm xs hk = inr xs'
      -> sllClosure rm cm ys hk' = inr ys'
      -> overapprox ys' xs'.
  Proof.
    intros gr hw rm cm xs xs'' ys ys'' hk hk' hp hm hw' ho hl hc x'' hi.
    unfold llClosure in hl.
    unfold sllClosure in hc.
    eapply aggrClosureResults_dmap_backwards in hi; eauto.
    destruct hi as [x [hi [xs' [_ [hc' hi']]]]].
    pose proof hi as hw''; apply hw' in hw''.
    pose proof hi as hi''.
    apply ho in hi''; destruct hi'' as [y [hi'' hyx]].
    eapply aggrClosureResults_dmap_succ_elt_succ in hc; eauto.
    destruct hc as [hi''' [ys' [hs' ha]]].
    eapply llc_sllc_approx_overapprox in hs'; eauto.
    apply hs' in hi'; destruct hi' as [? [? ? ]]; eauto.
  Qed.
  
  Lemma target_preserves_overapprox :
    forall gr hw rm cm sps sps' hk hk' sps'' sps''' a l,
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> overapprox sps' sps
      -> llTarget gr hw rm (@existT _ _ a l) sps hk = inr sps''
      -> sllTarget rm cm a sps' hk' = inr sps'''
      -> overapprox sps''' sps''.
  Proof.
    intros gr hw rm cm xs ys hk hk' xs'' ys'' a l hp hf hw' ho hl hs.
    apply llTarget_cases in hl; destruct hl as [xs' [hk'' [hm hc]]].
    apply sllTarget_cases in hs; destruct hs as [ys' [hk''' [hm' hc']]].
    eapply move_preserves_overapprox in hm'; eauto.
    eapply move_preserves_stack_wf_invar in hw'; eauto.
    eapply closure_preserves_overapprox; eauto.
  Qed.

  Lemma overapprox_initSps :
    forall rm pre vs x suf frs sps sps',
      llInitSps rm pre vs x suf frs = sps
      -> sllInitSps rm x = sps'
      -> overapprox sps' sps.
  Proof.
    intros rm pre vs x suf frs sps sps' hl hs sp hi; subst.
    apply in_map_iff in hi; destruct hi as [ys [? hi]]; subst.
    eexists; split.
    - apply in_map_iff; eauto.
    - sis; eauto.
  Qed.
  
  Lemma overapprox_startState :
    forall gr hw rm cm fr pre vs x suf frs hk sps sps',
      fr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (fr, frs)
      -> llStartState gr hw rm pre vs x suf frs hk = inr sps
      -> sllStartState rm cm x = inr sps'
      -> overapprox sps' sps.
  Proof.
    intros gr hw rm cm fr pre vs x suf frs hk sps sps' ? hp hc hw' hl hs; subst.
    eapply closure_preserves_overapprox; eauto.
    - eapply llInitSps_preserves_stack_wf_invar; eauto.
    - eapply overapprox_initSps; eauto.
  Qed.

  (* The main results in this module: correspondences
     between LL and SLL prediction *)

  Lemma sllPredict'_llPredict'_succ_eq :
    forall gr hw rm cm ts sps' sps ca hk hk' hc ys ca' ys',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> all_stacks_stable sps
      -> exists_successful_sp gr sps ts
      -> overapprox sps' sps
      -> llPredict' gr hw rm sps ts hk = PredSucc ys
      -> sllPredict' rm cm sps' ts ca hk' hc = (PredSucc ys', ca')
      -> ys' = ys.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a,l) ts IH];
      intros sps' sps ca hk hk' hc ys ca' ys' hn hp hm hw' hs he ho hll hsll;
      pose proof hll as hll'; simpl in hll, hsll.
    - inv hsll; eapply overapprox_final_subparsers_succ_eq; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps  as [| sp  sps ]; tc.
      destruct (allPredictionsEqual _ _ sp' sps') eqn:ha'.
      + inv hsll.
        assert (ha : allPredictionsEqual beqGamma prediction sp sps = true).
        { eapply overapprox_allPredictionsEqual_big_small; eauto. }
        rewrite ha in hll; inv hll.
        eapply overapprox_ape_pointwise; eauto.
        apply in_eq.
      + eapply esp_llPredict'_succ__exists_target in hll'; eauto.
        destruct hll' as [sps'' [ht hll']].
        apply sllPredict'_cont_cases in hsll.
        destruct hsll as [[sps''' [hf hsll]] | [sps''' [ht' hsll]]].
        * pose proof hf as hf'; apply hc in hf'.
          destruct hf' as [hk'' ht'].
          eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- eapply target_preserves_overapprox; eauto.
        * eapply IH with (sps' := sps''') (sps := sps'') in hsll; eauto.
          -- eapply llTarget_preserves_stacks_wf_invar; eauto.
          -- eapply llTarget_preserves_stacks_stable_invar; eauto.
          -- eapply llTarget_preserves_successful_sp_invar; eauto.
          -- eapply target_preserves_overapprox; eauto. 
  Qed.

  Lemma sllPredict_llPredict_succ_eq :
    forall gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs rhs' ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> llPredict gr hw rm pre vs x suf frs ts hk = PredSucc rhs
      -> sllPredict rm cm x ts ca hc = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs rhs' ca' ? hn hp hc' hw' hg hl hs; subst.
    apply llPredict_cases in hl; destruct hl as [sps [hss hl]].
    apply sllPredict_cases in hs; destruct hs as [sps' [hss' hs]].
    eapply sllPredict'_llPredict'_succ_eq; eauto.
    - eapply llStartState_preserves_stacks_wf_invar; eauto.
    - eapply llStartState_all_stacks_stable; eauto.
    - eapply llStartState_preserves_esp_invar; eauto. 
    - eapply overapprox_startState; eauto. 
  Qed.

  Lemma sllPredict'_succ__llPredict'_neq_ambig :
    forall gr hw rm cm ts sps sps' ca hk hk' hc ca' ys ys',
      rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> all_stacks_wf gr sps
      -> overapprox sps' sps
      -> sllPredict' rm cm sps' ts ca hk' hc = (PredSucc ys, ca')
      -> llPredict' gr hw rm sps ts hk <> PredAmbig ys'.
  Proof.
    intros gr hw rm cm ts; induction ts as [| (a, l) ts IH];
      intros sps sps' ca hk hk' hc ca' ys ys' hp hm hw' ho hs hl; sis.
    - inv hs; eapply overapprox_handleFinalSubparsers_contra; eauto.
    - destruct sps' as [| sp' sps']; tc.
      destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual _ _ sp sps) eqn:ha; tc.
      eapply overapprox_allPredictionsEqual_false in ha; eauto.
      rewrite ha in hs.
      apply llPredict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      apply sllPredict'_cont_cases in hs.
      destruct hs as [[sps''' [hf hs]] | [sps''' [ht' hs]]].
      + pose proof hf as hf'; apply hc in hf'.
        destruct hf' as [hk'' ht'].
        eapply IH in hs; eauto.
        * eapply llTarget_preserves_stacks_wf_invar; eauto.
        * eapply target_preserves_overapprox; eauto.
      + eapply IH in hs; eauto.
        * eapply llTarget_preserves_stacks_wf_invar; eauto.
        * eapply target_preserves_overapprox; eauto. 
  Qed.

  Lemma sllPredict_succ__llPredict_neq_ambig :
    forall gr hw rm cm fr pre vs x suf frs ts ca hk hc ys ca' ys',
      fr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (fr, frs)
      -> sllPredict rm cm x ts ca hc = (PredSucc ys, ca')
      -> llPredict gr hw rm pre vs x suf frs ts hk <> PredAmbig ys'.
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hk hc ys ca' ys' ? hp hc' hw' hs hl; subst.
    apply sllPredict_cases in hs; destruct hs as [sps' [hss' hs]].
    apply llPredict_cases in hl; destruct hl as [sps [hss hl]].
    eapply sllPredict'_succ__llPredict'_neq_ambig; eauto.
    - eapply llStartState_preserves_stacks_wf_invar; eauto.
    - eapply overapprox_startState; eauto. 
  Qed.
  
  Lemma sllPredict_succ_eq_llPredict_succ :
    forall gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> sllPredict rm cm x ts ca hc = (PredSucc rhs, ca')
      -> llPredict gr hw rm pre vs x suf frs ts hk = PredSucc rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hk hc rhs' ca' ?
           hn hp hc' hw' hg hs; subst. 
    destruct (llPredict _ _ _ _) as [rhs | rhs | | e] eqn:hl.
    - symmetry; f_equal; eapply sllPredict_llPredict_succ_eq; eauto.
    - exfalso; eapply sllPredict_succ__llPredict_neq_ambig; eauto.
    - exfalso; eapply ussr_llPredict_neq_reject; eauto.
    - exfalso; eapply llPredict_never_returns_error; eauto.
  Qed.

  Lemma adaptivePredict_succ_eq_llPredict_succ :
    forall gr hw rm cm cr pre vs x suf frs ts ca hc hk rhs ca',
      cr = Fr pre vs (NT x :: suf)
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> stack_accepts_suffix gr (cr, frs) ts
      -> adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk = (PredSucc rhs, ca')
      -> llPredict gr hw rm pre vs x suf frs ts hk = PredSucc rhs.
  Proof.
    intros gr hw rm cm cr pre vs x suf frs ts ca hc hk rhs ca' ? hn hp hc' hw' hg ha; subst. 
    unfold adaptivePredict in ha.
    destruct (sllPredict _ _ _ _ _) as ([? | ? | | ?], ?) eqn:hs; tc; inv ha.
    eapply sllPredict_succ_eq_llPredict_succ; eauto.
  Qed.

  Theorem adaptivePredict_succ_at_most_one_rhs_applies :
    forall gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs rhs' ca',
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_complete gr cm
      -> stack_wf gr (cr, frs)
      -> PM.In (x, rhs) gr
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk = (PredSucc rhs', ca')
      -> rhs' = rhs.
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs rhs' ca' ? ? hn hr hc' hw' hi hg ha; subst.
    eapply adaptivePredict_succ_eq_llPredict_succ in ha; eauto.
    - eapply llPredict_succ_at_most_one_rhs_applies; eauto.
    - (* lemma *)
      destruct hg as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
      destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm & hp & hl); subst; sis.
      exists (wpre ++ wsuf'); exists wsuf''; eexists;
        repeat split; eauto; apps; econstructor; eauto.
  Qed.

  Lemma adaptivePredict_ambig_llPredict_ambig :
    forall gr hw rm cm pre vs x suf frs ts ca hc hk rhs ca',
      adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk = (PredAmbig rhs, ca')
      -> llPredict gr hw rm pre vs x suf frs ts hk = PredAmbig rhs.
  Proof.
    unfold adaptivePredict; intros; dms; tc. 
  Qed.

  Theorem adaptivePredict_ambig_rhs_unproc_stack_syms:
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (cm  : closure_map)
           (rm  : rhs_map)
           (cr  : parser_frame)
           (ce  : parser_frame)
           (pre : list symbol)
           (vs  : symbols_semty pre)
           (x   : nonterminal)
           (suf : list symbol)
           (frs : list parser_frame)
           (ts  : list token)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs))
           (rhs : list symbol)
           (ca' : cache),
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk = (PredAmbig rhs, ca')
      -> stack_accepts_suffix gr (ce, cr :: frs) ts. 
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs ts ca hc hk rhs ca' ? ? hn hp hw' ha; subst.
    eapply llPredict_ambig_rhs_unproc_stack_syms; eauto.
    eapply adaptivePredict_ambig_llPredict_ambig; eauto.
  Qed. 
    
End SllOptimizationSoundFn.
