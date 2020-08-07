Require Import List.
Require Import GallStar.Lex.
Require Import GallStar.SLL_optimization_sound.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module SllPredictionErrorFreeFn (Import D : Defs.T).

  Module Export SLLS := SllOptimizationSoundFn D.

  (* A more permissive well-formedness invariant that 
     places fewer restrictions on the bottom frame *)
  Inductive frames_top_wf (g : grammar) : list suffix_frame -> Prop :=
  | TWF_bottom :
      forall o ys,
        frames_top_wf g [SF o ys]
  | TWF_upper :
      forall x pre' suf suf' o frs,
        In (x, pre' ++ suf') g
        -> frames_top_wf g (SF o (NT x :: suf) :: frs)
        -> frames_top_wf g (SF (Some x) suf' :: SF o (NT x :: suf) :: frs).

  Hint Constructors frames_top_wf : core.

  (* invert an sframes_top_wf judgment, naming the hypotheses hi and hw' *)
  Ltac inv_twf hw  hi hw' :=
    inversion hw as [ ? ? | ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac twf_upper_nil := eapply TWF_upper with (pre' := []); sis; eauto. 

  (* The stack top well-formedness predicate *)
  Definition stack_top_wf (g : grammar) (stk : suffix_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_top_wf g (fr :: frs)
    end.

  Definition all_stack_tops_wf g sps :=
    forall sp, In sp sps -> stack_top_wf g (stack sp).

  Lemma suffix_frames_wf__frames_top_wf :
    forall g frs,
      suffix_frames_wf g frs -> frames_top_wf g frs.
  Proof.
    intros g frs hw; induction hw; eauto.
  Qed.
  
  Lemma suffix_stack_wf__stack_top_wf :
    forall g fr frs,
      suffix_stack_wf g (fr, frs) -> stack_top_wf g (fr, frs).
  Proof.
    intros; apply suffix_frames_wf__frames_top_wf; auto.
  Qed.

  Lemma return_preserves_frames_top_wf :
    forall g o o' suf_cr x frs,
      frames_top_wf g (SF o [] :: SF o' (NT x :: suf_cr) :: frs)
      -> frames_top_wf g (SF o' suf_cr :: frs).
  Proof.
    intros g o o' suf_cr x locs hw.
    inv_twf hw  hi hw'.
    inv_twf hw' hi' hw''; auto.
    rewrite app_cons_group_l in hi'; eauto.
  Qed.

  Lemma push_preserves_frames_top_wf :
    forall g o suf x rhs frs,
      In (x, rhs) g
      -> frames_top_wf g (SF o (NT x :: suf) :: frs)
      -> frames_top_wf g (SF (Some x) rhs :: SF o (NT x :: suf) :: frs).
  Proof.
    intros; twf_upper_nil. 
  Qed.
       
  Lemma consume_preserves_frames_top_wf_invar :
    forall g o suf a frs,
      frames_top_wf g (SF o (T a :: suf) :: frs)
      -> frames_top_wf g (SF o suf :: frs).
  Proof.
    intros g o suf a frs hw.
    inv_twf hw  hi hw'; auto.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  Lemma moveSp_preserves_stack_top_wf :
    forall g t sp sp',
      stack_top_wf g sp.(stack)
      -> moveSp t sp = MoveSucc sp'
      -> stack_top_wf g sp'.(stack).
  Proof.
    intros g t sp sp' hw hm.
    unfold moveSp in hm; dms; tc; inv hm; sis.
    eapply consume_preserves_frames_top_wf_invar; eauto.
  Qed.

  Lemma move_preserves_stack_top_wf :
    forall g t sps sps',
      all_stack_tops_wf g sps
      -> move t sps = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g t sps sps' ha hm sp' hi.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    apply in_map_iff in hm; destruct hm as [sp [hm hi']].
    eapply moveSp_preserves_stack_top_wf ; eauto.
  Qed.

  Lemma cstep_preserves_stack_top_wf :
    forall g sp sp' sps' av av',
      stack_top_wf g sp.(stack)
      -> cstep g av sp = CstepK av' sps'
      -> In sp' sps'
      -> stack_top_wf g sp'.(stack).
  Proof.
    intros g sp sp' sps' av av' hw hs hi.
    unfold cstep in hs; dms; tc; sis; inv hs.
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_frames_top_wf; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_frames_top_wf; auto.
      apply rhssForNt_in_iff; auto.
    - inv hi.
  Qed.

  (* refactor *)
  Lemma simReturn_stack_top_wf :
    forall g cm sp sp' sps',
      closure_map_correct g cm
      -> simReturn cm sp = Some sps'
      -> In sp' sps'
      -> stack_top_wf g (stack sp').
  Proof.
    intros g cm [pr (fr, frs)] sp' sps' [hs hc] hr hi.
    pose proof hr as heq; apply simReturn_stack_shape in heq.
    destruct heq as [x heq]; inv heq; inv hr.
    apply in_map_iff in hi. destruct hi as [fr [heq hi]]; subst; sis.
    unfold destFrames in hi.
    dmeq hf; tc.
    - (* lemma *)
      apply FMF.find_mapsto_iff in hf.
      eapply hs in hi; eauto.
      destruct hi as [hm hst].
      destruct fr as [[y |] [| [a | y'] suf]]; inv hst; auto.
    - inv hi.
  Qed.

  Lemma sllc_preserves_suffix_stack_wf_invar :
    forall g cm pr (a : Acc lex_nat_pair pr) av sp sp' a' sps',
      pr = meas g av sp
      -> closure_map_correct g cm
      -> stack_top_wf g sp.(stack)
      -> sllc g cm av sp a' = inr sps'
      -> In sp' sps'
      -> stack_top_wf g sp'.(stack).
  Proof.
    intros g cm pr a'.
    induction a' as [pr hlt IH]; intros av sp sp' a sps' heq hc hw hs hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply simReturn_stack_top_wf; eauto.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllClosure_preserves_stack_top_wf :
    forall g cm sps sps',
      closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllClosure g cm sps = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g cm sps sps' hc ha hs sp' hi.
    eapply aggrClosureResults_succ_in_input in hs; eauto.
    destruct hs as [sps'' [hi' hi'']].
    apply in_map_iff in hi'; destruct hi' as [sp [hs hi']].
    eapply sllc_preserves_suffix_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.
  
  Lemma sllTarget_preserves_stack_top_wf :
    forall g cm a sps sps',
      closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllTarget g cm a sps = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g cm a sps sps' hc hw ht; unfold sllTarget in ht.
    dmeq hm; tc; dmeq hs; tc; inv ht.
    eapply move_preserves_stack_top_wf in hm; eauto.
    eapply sllClosure_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllInitSps_stack_tops_wf :
    forall g x,
      all_stack_tops_wf g (sllInitSps g x).
  Proof.
    intros g x [pr (fr, frs)] hi; sis.
    apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; inv heq; auto.
  Qed.

  Lemma sllStartState_preserves_stack_top_wf :
    forall g cm x sps,
      closure_map_correct g cm
      -> sllStartState g cm x = inr sps
      -> all_stack_tops_wf g sps.
  Proof.
    intros g cm x sps hm hs sp hi.
    eapply sllClosure_preserves_stack_top_wf; eauto.
    apply sllInitSps_stack_tops_wf.
  Qed.


  (* Some facts about the stable_config invariant --
     these should eventually move elsewhere *)

  (* refactor *)
  Lemma simReturn_some__all_stacks_stable :
    forall g cm sp sps',
      closure_map_correct g cm
      -> simReturn cm sp = Some sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g cm sp sps' [hs hc] hr sp' hi.
    unfold simReturn in hr; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [fr [heq hi]]; subst; sis.
    unfold destFrames in hi; dmeq hf; try solve [inv hi].
    apply FMF.find_mapsto_iff in hf; eapply hs in hi; eauto.
    destruct hi as [_ hst].
    destruct fr as [[x |] [| [a|y] suf]]; sis; tc; auto.
  Qed.

  Lemma simReturn_none_cstepDone__stable_config :
    forall g cm av sp,
      stack_top_wf g sp.(stack)
      -> simReturn cm sp = None
      -> cstep g av sp = CstepDone
      -> stable_config sp.(stack).
  Proof.
    intros g cm av sp hw hr hs.
    unfold cstep in hs; dmeqs H; tc; sis; inv hw; auto.
    dm; tc.
  Qed.
  
  Lemma sllc_all_stacks_stable :
    forall g cm pr (a : Acc lex_nat_pair pr) av sp a' sps',
      pr = meas g av sp
      -> closure_map_correct g cm
      -> stack_top_wf g sp.(stack)
      -> sllc g cm av sp a' = inr sps'
      -> all_stacks_stable sps'. 
  Proof.
    intros g cm pr a'.
    induction a' as [pr hlt IH]; intros av sp a sps' ? hc hw hs sp' hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply simReturn_some__all_stacks_stable; eauto.
    - apply in_singleton_eq in hi; subst.
      eapply simReturn_none_cstepDone__stable_config; eauto.     - eapply aggrClosureResults_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllClosure__all_stacks_stable :
    forall g cm sps sps',
      closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllClosure g cm sps = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g cm sps sps' hm hw hc sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    apply in_map_iff in hi'; destruct hi' as [sp [hs hi']].
    eapply sllc_all_stacks_stable; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma sllTarget__all_stacks_stable :
    forall g cm a sps sps',
      closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllTarget g cm a sps = inr sps'
      -> all_stacks_stable sps'.
  Proof.
    intros g cm a sps sps' hc hw ht; unfold sllTarget in ht.
    dmeq hm; tc; dmeq hc'; tc; inv ht.
    eapply move_preserves_stack_top_wf in hm; eauto.
    eapply sllClosure__all_stacks_stable; eauto.
  Qed.
  
  (* X never returns SpInvalidState *)

  Lemma sll_cstep_never_returns_SpInvalidState :
    forall g av sp,
      stack_top_wf g sp.(stack)
      -> cstep g av sp <> CstepError SpInvalidState.
  Proof.
    intros g av sp hw hs; unfold cstep in hs; dms; tc; inv hw.
  Qed.

  Lemma sllc_never_returns_SpInvalidState :
    forall (g    : grammar)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (av   : NtSet.t)
           (sp   : subparser)
           (a'   : Acc lex_nat_pair (meas g av sp)),
      pair = meas g av sp
      -> stack_top_wf g sp.(stack)
      -> sllc g cm av sp a' <> inl SpInvalidState.
  Proof.
    intros g cm pair a'.
    induction a' as [pair hlt IH].
    intros av sp a heq hw hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [heq heq']]]]]]; subst.
    - eapply sll_cstep_never_returns_SpInvalidState; eauto.
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_stack_top_wf; eauto.
  Qed.
  
  Lemma sllClosure_neq_SpInvalidState :
    forall g cm sps,
      all_stack_tops_wf g sps
      -> sllClosure g cm sps <> inl SpInvalidState.
  Proof.
    intros g cm sps hw hc.
    unfold sllClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    apply in_map_iff in hc; destruct hc as [sp [hs hi]].
    eapply sllc_never_returns_SpInvalidState; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma sllTarget_neq_SpInvalidState :
    forall g cm a sps,
      all_stack_tops_wf g sps
      -> all_stacks_stable sps
      -> sllTarget g cm a sps <> inl SpInvalidState.
  Proof.
    intros g cm a sps hw hs ht; unfold sllTarget in ht; dmeq hm.
    - inv ht; eapply move_never_returns_SpInvalidState_for_ready_sps; eauto.
    - dmeq hc; tc; inv ht.
      eapply move_preserves_stack_top_wf in hm; eauto.
      eapply sllClosure_neq_SpInvalidState; eauto.
  Qed.    

  Lemma sllPredict'_neq_SpInvalidState :
    forall g cm ts sps ca ca',
      closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> cache_stores_target_results g cm ca
      -> all_stacks_stable sps
      -> sllPredict' g cm sps ts ca <> (PredError SpInvalidState, ca').
  Proof.
    intros g cm ts; induction ts as [| (a, l) ts IH];
    intros sps ca ca' hm hw hc hs hp; sis.
    - inv hp; eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      destruct (Cache.find _ _) as [sps' |] eqn:hf.
      + apply hc in hf.
        eapply IH in hp; eauto.
          * eapply sllTarget_preserves_stack_top_wf; eauto.
          * eapply sllTarget__all_stacks_stable; eauto.
      + destruct (sllTarget _ _ _ _) as [e | sps'] eqn:ht.
        * inv hp; eapply sllTarget_neq_SpInvalidState; eauto.
        * eapply IH in hp; eauto.
          -- eapply sllTarget_preserves_stack_top_wf; eauto.
          -- apply sllTarget_add_preserves_cache_invar; auto.
          -- eapply sllTarget__all_stacks_stable; eauto.
  Qed.

  Lemma sllStartState_neq_SpInvalidState :
    forall g cm x,
      sllStartState g cm x <> inl SpInvalidState.
  Proof.
    intros g cm x hss.
    eapply sllClosure_neq_SpInvalidState; eauto.
    apply sllInitSps_stack_tops_wf.
  Qed.
  
  Lemma sllPredict_neq_SpInvalidState :
    forall g cm x ts ca ca',
      closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> sllPredict g cm x ts ca <> (PredError SpInvalidState, ca').
  Proof.
    intros g cm x ts ca ca' hm hc hp.
    unfold sllPredict in hp.
    destruct (sllStartState _ _ _) as [[| y] | sps] eqn:hss; tc; inv hp.
    - eapply sllStartState_neq_SpInvalidState; eauto.
    - eapply sllPredict'_neq_SpInvalidState; eauto.
      + eapply sllStartState_preserves_stack_top_wf; eauto.
      + eapply sllClosure__all_stacks_stable; eauto.
        apply sllInitSps_stack_tops_wf.
  Qed.

  (* X never returns SpLeft Recursion *)

  Lemma sllc_neq_SpLeftRecursion :
    forall (g    : grammar)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (av   : NtSet.t)
           (sp   : subparser)
           (a'   : Acc lex_nat_pair (meas g av sp))
           (x    : nonterminal),
      no_left_recursion g
      -> unavailable_nts_invar g av sp
      -> pair = meas g av sp
      -> sllc g cm av sp a' <> inl (SpLeftRecursion x).
  Proof.
    intros g cm pair a'.
    induction a' as [pair hlt IH].
    intros av sp a x hn hu ? hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hs | [sps [av' [hs [crs [heq heq']]]]]]; subst.
    - eapply cstep_never_finds_left_recursion; eauto. 
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply cstep_meas_lt; eauto.
      + eapply cstep_preserves_unavailable_nts_invar; eauto.
  Qed.
  
  Lemma sllClosure_neq_SpLeftRecursion :
    forall g cm sps x,
      no_left_recursion g
      -> sllClosure g cm sps <> inl (SpLeftRecursion x).
  Proof.
    intros g cm sps x hn hc; unfold sllClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    apply in_map_iff in hc; destruct hc as [[pr (fr, frs)] [hs hi]].
    eapply sllc_neq_SpLeftRecursion; eauto.
    - apply lex_nat_pair_wf.
    - eapply unavailable_nts_allNts.
  Qed.

  Lemma sllTarget_neq_SpLeftRecursion :
    forall g cm a sps x,
      no_left_recursion g
      -> sllTarget g cm a sps <> inl (SpLeftRecursion x).
  Proof.
    intros g cm a sps x hn ht.
    unfold sllTarget in ht; dmeq hm; tc.
    - inv ht; eapply move_never_returns_SpLeftRecursion; eauto.
    - dmeq hc; tc; inv ht. eapply sllClosure_neq_SpLeftRecursion; eauto. 
  Qed.
  
  Lemma sllPredict'_neq_SpLeftRecursion :
    forall g cm ts sps ca ca' x,
      no_left_recursion g
      -> cache_stores_target_results g cm ca
      -> sllPredict' g cm sps ts ca <> (PredError (SpLeftRecursion x), ca').
  Proof.
    intros g cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca ca' x hn hc hl; sis.
    - inv hl; eapply handleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      dmeq hf.
      + apply hc in hf; eapply IH in hl; eauto.
      + dmeq ht.
        * inv hl; eapply sllTarget_neq_SpLeftRecursion; eauto.
        * eapply IH in hl; eauto.
          apply sllTarget_add_preserves_cache_invar; auto.
  Qed. 
  
  Lemma sllStartState_neq_SpLeftRecursion :
    forall g cm x x',
      no_left_recursion g
      -> sllStartState g cm x <> inl (SpLeftRecursion x').
  Proof.
    intros g cm x x' hn hss.
    eapply sllClosure_neq_SpLeftRecursion; eauto.
  Qed.

  Lemma sllPredict_neq_SpLeftRecursion :
    forall g cm x x' ts ca ca',
      no_left_recursion g
      -> cache_stores_target_results g cm ca
      -> sllPredict g cm x ts ca <> (PredError (SpLeftRecursion x'), ca').
  Proof.
    intros g cm x x' ts ca ca' hn hc hp.
    unfold sllPredict in hp.
    destruct (sllStartState _ _ _) as [[| y] | sps] eqn:hss; tc; inv hp.
    - eapply sllStartState_neq_SpLeftRecursion; eauto. 
    - eapply sllPredict'_neq_SpLeftRecursion; eauto. 
  Qed.  

  (* Putting it all together *)
  Lemma sllPredict_never_returns_error :
    forall g cm x ts ca ca' e,
      no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> sllPredict g cm x ts ca <> (PredError e, ca').
  Proof.
    intros g cm x ts ca ca' e hn hm hc hs; destruct e as [| x'].
    - eapply sllPredict_neq_SpInvalidState; eauto.
    - eapply sllPredict_neq_SpLeftRecursion; eauto.
  Qed.

  Theorem adaptivePredict_neq_error :
    forall g cm fr frs o x suf ts ca ca' e,
      no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> suffix_stack_wf g (fr, frs)
      -> fr = SF o (NT x :: suf)
      -> adaptivePredict g cm x (fr, frs) ts  ca <> (PredError e, ca').
  Proof.
    intros g cm fr frs o x suf ts ca ca' e hn hm hc hw ? ha; subst.
    unfold adaptivePredict in ha.
    dmeq hsll; dms; tc; inv ha.
    - eapply llPredict_never_returns_error; eauto.
    - eapply sllPredict_never_returns_error; eauto.
  Qed.

End SllPredictionErrorFreeFn.
