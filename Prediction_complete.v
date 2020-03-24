Require Import Bool List Omega.
Require Import GallStar.Defs. 
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module PredictionCompleteFn (Import D : Defs.T).

  Module Export PEF := PredictionErrorFreeFn D.

  Inductive move_step :
    subparser -> list token -> subparser -> list token -> Prop :=
  | MV_consume :
      forall pred suf o a l ts frs,
        move_step (Sp pred (SF o (T a :: suf), frs)) ((a, l) :: ts)
                  (Sp pred (SF o suf, frs)) ts.

  Hint Constructors move_step : core.

  Lemma move_step_preserves_label :
    forall sp sp' w w',
      move_step sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros sp sp' w w' hm; inv hm; auto.
  Qed.

  Lemma move_step_word_length_lt :
    forall sp sp' ts ts',
      move_step sp ts sp' ts'
      -> length ts' < length ts.
  Proof.
    intros sp sp' ts ts' hm; inv hm; auto.
  Qed.

  Lemma move_func_refines_move_step :
    forall a l ts sp sp' sps sps',
      In sp sps
      -> move_step sp ((a,l) :: ts) sp' ts
      -> move a sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros a l ts sp sp' sps sps' hi hr hf.
    inv hr.
    eapply move_succ_all_sps_step; eauto.
  Qed.

  Lemma moveSp_move_step :
    forall a l w' sp sp',
      move_step sp ((a,l) :: w') sp' w'
      -> moveSp a sp = MoveSucc sp'.
  Proof.
    intros a l w' sp sp' hm.
    inv hm; unfold moveSp; dms; tc.
  Qed.

  Lemma move_step_moveSp :
    forall a l w' sp sp',
      moveSp a sp = MoveSucc sp'
      -> move_step sp ((a,l) :: w') sp' w'.
  Proof.
    intros a l w' [pred ([o suf], frs)]
           [pred' ([o' suf'], frs')] hm.
    unfold moveSp in hm.
    destruct suf as [| [a' | x] suf]; try (dms; tc); subst.
    inv hm; constructor.
  Qed.

  Lemma move_step_preserves_suffix_stack_wf_invar :
    forall g sp sp' t w,
      move_step sp (t :: w) sp' w
      -> suffix_stack_wf g sp.(stack)
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g sp sp' (a,l) w' hm hw.
    eapply moveSp_preserves_suffix_stack_wf_invar; eauto.
    eapply moveSp_move_step; eauto.
  Qed.

  Lemma move_step_preserves_unprocStackSyms_recognize :
    forall g sp sp' t w',
      move_step sp (t :: w') sp' w'
      -> gamma_recognize g (unprocStackSyms sp.(stack)) (t :: w')
      -> gamma_recognize g (unprocStackSyms sp'.(stack)) w'.
  Proof.
    intros g sp sp' t w' hm hg; inv hm; sis.
    apply gamma_recognize_terminal_head in hg.
    destruct hg as [l' [w'' [heq hg]]]; inv heq; auto.
  Qed.

  Lemma move_step_recognize_cons :
    forall g sp t w',
      stable_config sp.(stack)
      -> gamma_recognize g (unprocStackSyms sp.(stack)) (t :: w')
      -> exists sp',
          move_step sp (t :: w') sp' w'.
  Proof.
    intros g [pred stk] t w' hs hg; sis.
    inv hs; auto; sis.
    - inv hg.
    - apply gamma_recognize_terminal_head in hg.
      destruct hg as (l & w'' & heq & hg); inv heq; eauto.
  Qed. 

  Inductive closure_step (g : grammar) : NtSet.t -> subparser -> NtSet.t -> subparser -> Prop :=
  | CS_ret :
      forall av pred o o' x suf' frs,
        closure_step g
                     av
                     (Sp pred (SF o [], SF o' (NT x :: suf') :: frs))
                     (NtSet.add x av)
                     (Sp pred (SF o' suf', frs))
  | CS_push :
      forall av pred o x suf frs rhs,
        NtSet.In x av
        -> In (x, rhs) g
        -> closure_step g
                        av 
                        (Sp pred (SF o (NT x :: suf), frs))
                        (NtSet.remove x av)
                        (Sp pred (SF (Some x) rhs, SF o (NT x :: suf) :: frs)).

  Hint Constructors closure_step : core.

  Ltac inv_cs hs hi hi' :=
    inversion hs as [? ? ? ? ? ? ? | ? ? ? ? ? ? ? hi hi']; subst; clear hs.

  Lemma closure_step_preserves_label :
    forall g av av' sp sp',
      closure_step g av sp av' sp'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g av av' sp sp' hc; inv hc; auto.
  Qed.

  Lemma closure_step_preserves_suffix_stack_wf_invar :
    forall g av av' sp sp',
      closure_step g av sp av' sp'
      -> suffix_stack_wf g sp.(stack)
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g sp sp' av av' hc hw; inv hc; sis; auto.
    - eapply return_preserves_suffix_frames_wf_invar; eauto.
    - eapply push_preserves_suffix_frames_wf_invar; eauto.
  Qed.    

  Lemma spClosureStep_sound :
    forall g av av' sp sp' sps',
      suffix_stack_wf g sp.(stack)
      -> spClosureStep g av sp = CstepK av' sps'
      -> In sp' sps'
      -> closure_step g av sp av' sp'.
  Proof.
    intros g av av' sp sp' sps' hw hs hi.
    unfold spClosureStep in hs; dmeqs h; tc; subst; sis.
    - inv hw; inv hs.
      apply in_singleton_eq in hi; subst; auto.
    - inv hs.
      apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      constructor.
      + apply NtSet.mem_spec; auto.
      + apply rhssForNt_in_iff; auto.
    - inv hs; inv hi.
  Qed.

  Inductive closure_multistep (g : grammar) :
    NtSet.t -> subparser -> NtSet.t -> subparser -> Prop :=
  | CMS_empty :
      forall av pred,
        closure_multistep g
                          av (Sp pred (SF None [], []))
                          av (Sp pred (SF None [], []))
  | CMS_terminal :
      forall av pred o a suf frs,
        closure_multistep g av (Sp pred (SF o (T a :: suf), frs))
                            av (Sp pred (SF o (T a :: suf), frs))
  | CMS_trans :
      forall av av' av'' sp sp' sp'',
        closure_step g av sp av' sp'
        -> closure_multistep g av' sp' av'' sp''
        -> closure_multistep g av sp av'' sp''.

  Hint Constructors closure_multistep : core.

  Ltac inv_cm hm hs hm' :=
    inversion hm as [ ? ? | ? ? ? ? ? ? | ? ? ? ? ? ? hs hm']; subst; clear hm.

  Ltac induct_cm hm hs hm' IH :=
    induction hm as [ ? ? | ? ? ? ? ? ? | ? ? ? ? ? ? hs hm' IH].

  Lemma closure_multistep_preserves_label :
    forall g av av' sp sp',
      closure_multistep g av sp av' sp'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g av av' sp sp' hm.
    induct_cm hm hs hm' IH; auto.
    apply closure_step_preserves_label in hs; tc.
  Qed.

  Lemma closure_multistep_done_eq :
    forall g av av' sp sp' sps,
      closure_multistep g av sp av' sp'
      -> spClosureStep g av sp = CstepDone sps
      -> sp = sp'.
  Proof.
    intros g av av' sp sp' sps hm hs; unfold spClosureStep in hs; dms; tc;
      inv_cm hm hs' hm'; auto; inv hs'.
  Qed.

  Lemma closure_multistep_not_done_middle_sp_in_continuation :
    forall g av av' av'' sp sp'' sps',
      closure_multistep g av sp av'' sp''
      -> spClosureStep g av sp = CstepK av' sps'
      -> exists sp',
          closure_step g av sp av' sp'
          /\ closure_multistep g av' sp' av'' sp''
          /\ In sp' sps'.
  Proof.
    intros g av av' av'' sp sp'' sps' hm hs; unfold spClosureStep in hs; dmeqs h; tc; inv hs; eauto.
    - inv_cm hm hs hm'; inv hs; eexists; repeat split; auto.
      apply in_eq.
    - inv_cm hm hs hm'; inv hs. 
      eexists; split.
      + constructor; eauto.
      + split; auto.
        apply in_map_iff; eexists; split; eauto.
        apply rhssForNt_in_iff; auto.
    - exfalso.
      inv_cm hm hs hm'.
      inv_cs hs hi hi'.
      apply lhs_mem_allNts_true in hi'; tc.
  Qed.

  Lemma spClosure_refines_closure_multistep' :
    forall (g  : grammar)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (av av'' : NtSet.t)
           (sp sp'' : subparser)
           (a' : Acc lex_nat_pair (meas g av sp))
           (sps'' : list subparser),
      pr = meas g av sp
      -> closure_multistep g av sp av'' sp''
      -> spClosure g av sp a'  = inr sps''
      -> In sp'' sps''.
  Proof.
    intros g pr a.
    induction a as [pr hlt IH]; intros av av'' sp sp'' a' sps'' heq hc hs; subst.
    unfold spClosure in hs.
    apply spClosure_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [av' [hs [crs [heq ha]]]]]]; subst.
    - (* sp must be in a "done" configuration, so sp = sp' *)
      eapply closure_multistep_done_eq in hc; subst; eauto.
      apply in_eq.
    - (* sp is in a non-final configuration, so we know something about what's in sps'' *)
      (* also, we know that sp must step to some intermediate subparser sp',
       and sp' multisteps to sp'' *)
      eapply closure_multistep_not_done_middle_sp_in_continuation in hc; eauto.
      destruct hc as [sp' [hs' [hm hi]]].
      eapply aggrClosureResults_dmap_succ_elt_succ in ha; eauto.
      destruct ha as [hi' [sps''' [heq hall]]].
      apply hall.
      eapply IH; eauto.
      eapply spClosureStep_meas_lt; eauto.
  Qed.

  Lemma spClosure_refines_closure_multistep :
    forall (g  : grammar) (av av'' : NtSet.t) (sp sp'' : subparser) (a : Acc lex_nat_pair (meas g av sp)) (sps'' : list subparser),
      closure_multistep g av sp av'' sp''
      -> spClosure g av sp a  = inr sps''
      -> In sp'' sps''.
  Proof.
    intros; eapply spClosure_refines_closure_multistep'; eauto.
  Qed.

  Lemma spClosure_sound_wrt_closure_multistep' :
    forall (g  : grammar)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (av : NtSet.t)
           (sp sp''' : subparser)
           (a' : Acc lex_nat_pair (meas g av sp))
           (sps''' : list subparser),
      pr = meas g av sp
      -> suffix_stack_wf g sp.(stack)
      -> spClosure g av sp a' = inr sps'''
      -> In sp''' sps'''
      -> exists av''',
          closure_multistep g av sp av''' sp'''.
  Proof.
    intros g pr a.
    induction a as [pr hlt IH]; intros av sp sp''' a' sps''' heq hw hs hi; subst.
    apply spClosure_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [av' [hs [crs [heq ha]]]]]]; subst.
    - apply in_singleton_eq in hi; subst.
      apply spClosureStepDone_stable_config in hdone; auto.
      destruct sp as [pred ([o suf], frs)].
      inv hdone; eauto.
    - eapply aggrClosureResults_dmap_backwards in ha; eauto.
      destruct ha as [sp' [hi' [sps'' [hi'' [hs' hi''']]]]].
      eapply IH in hs'; eauto.
      + destruct hs' as [av''' hs'].
        exists av'''.
        eapply CMS_trans with (sp' := sp'); eauto.
        eapply spClosureStep_sound; eauto.
      + eapply spClosureStep_meas_lt; eauto.
      + eapply spClosureStep_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma spClosure_sound_wrt_closure_multistep :
    forall (g  : grammar)
           (av : NtSet.t)
           (sp sp' : subparser)
           (a : Acc lex_nat_pair (meas g av sp))
           (sps' : list subparser),
      suffix_stack_wf g sp.(stack)
      -> spClosure g av sp a = inr sps'
      -> In sp' sps'
      -> exists av',
          closure_multistep g av sp av' sp'.
  Proof.
    intros; eapply spClosure_sound_wrt_closure_multistep'; eauto.
  Qed.
  
  Lemma closure_func_refines_closure_multistep :
    forall g av'' sp sp'' sps sps'',
      In sp sps
      -> closure_multistep g (allNts g) sp av'' sp''
      -> closure g sps = inr sps''
      -> In sp'' sps''.
  Proof.
    intros g av'' sp sp'' sps sps'' hi hc hc'.
    unfold closure in hc'.
    eapply aggrClosureResults_map_succ_elt_succ in hc'; eauto.
    destruct hc' as [sps' [heq hall]].
    apply hall.
    eapply spClosure_refines_closure_multistep; eauto.
  Qed.

    Lemma exists_cm_target_preserving_unprocStackSyms_recognize' :
    forall (w  : list token)
           (pr : nat * nat)
           (a  : Acc lex_nat_pair pr)
           (g  : grammar)
           (av : NtSet.t)
           (sp : subparser)
           (a' : Acc lex_nat_pair (meas g av sp)),
      pr = meas g av sp
      -> no_left_recursion g
      -> suffix_stack_wf g sp.(stack)
      -> unavailable_nts_invar g av sp
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> exists av' sp',
          closure_multistep g av sp av' sp'
          /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w.
    Proof.
      intros w pr a.
      induction a as [m hlt IH]; intros g av sp a' heq hn hw hu hg; subst.
      destruct sp as [pred ([o [| [a|x] suf]], frs)]; eauto.
      - destruct frs as [| fr' frs]; eauto.
        + inv hw; eauto.
        + simpl in hw; pose proof hw as hw'.
          destruct fr' as [o' [| [? | x] suf']]; inv hw'.
          specialize IH with (sp := Sp pred (SF o' suf', frs)).
          edestruct IH as [av' [sp' [hcm hg']]]; eauto.
          * eapply meas_lt_after_return; eauto. 
          * apply lex_nat_pair_wf.
          * eapply return_preserves_suffix_frames_wf_invar; eauto.
          * eapply return_preserves_unavailable_nts_invar; eauto.
    - simpl in hg; apply gamma_recognize_nonterminal_head in hg. 
      destruct hg as [rhs [wpre [wsuf [heq [hi [hg hg']]]]]]; subst.
      assert (hi' : NtSet.In x av).
      { (* lemma *)
        destruct (In_dec x av) as [hi' | hn']; auto.
        apply hu in hn'.
        - destruct hn' as (? & ? & ? & ? & ? & heq & heq' & hnp); subst.
          eapply frnp_grammar_nullable_path in hnp; eauto.
          firstorder.
        - apply NtSet.mem_spec; eapply lhs_mem_allNts_true; eauto. }
      specialize IH with 
          (sp := Sp pred (SF (Some x) rhs, (SF o (NT x :: suf) :: frs))).
      edestruct IH as [av' [sp' [hcm hg'']]]; eauto.
      + eapply meas_lt_after_push; eauto.
      + apply lex_nat_pair_wf.
      + eapply push_preserves_suffix_frames_wf_invar; eauto. 
      + eapply push_preserves_unavailable_nts_invar; eauto.
      + simpl; apply gamma_recognize_app; auto.
      + exists av'; exists sp'; split; auto.
        econstructor; eauto.
        constructor; auto.
    Qed.

  Lemma exists_cm_target_preserving_unprocStackSyms_recognize :
    forall g av sp w,
      no_left_recursion g
      -> suffix_stack_wf g sp.(stack)
      -> unavailable_nts_invar g av sp
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> exists av' sp',
          closure_multistep g av sp av' sp'
          /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w.
  Proof.
    intros; eapply exists_cm_target_preserving_unprocStackSyms_recognize'; eauto;
      apply lex_nat_pair_wf.
  Qed.

  Lemma closure_multistep_preserves_suffix_stack_wf_invar :
    forall g av av' sp sp',
      closure_multistep g av sp av' sp'
      -> suffix_stack_wf g sp.(stack)
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g av av' sp sp' hc; induction hc; intros hw; auto.
    eapply IHhc.
    eapply closure_step_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma stable_config_after_closure_multistep :
    forall g av av' sp sp',
      closure_multistep g av sp av' sp'
      -> stable_config sp'.(stack).
  Proof.
    intros g av av' sp sp' hc.
    induction hc; try constructor; auto.
  Qed.

  Lemma startState_closure_multistep_from_orig_sp' :
    forall g cr ce o x suf rhs frs sps w,
      cr = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> In (x, rhs) g
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w
      -> startState g x (cr, frs) = inr sps
      -> exists av sp,
          closure_multistep g (allNts g) (Sp rhs (ce, cr :: frs)) av sp
          /\ gamma_recognize g (unprocStackSyms sp.(stack)) w.
  Proof.
    intros g cr ce o x suf rhs frs sps w ? ? hn hw hi hg hs; subst; sis.
    eapply exists_cm_target_preserving_unprocStackSyms_recognize; eauto.
    - apply push_preserves_suffix_frames_wf_invar; auto.
    - apply unavailable_nts_allNts.
  Qed.

  Lemma startState_closure_multistep_from_orig_sp :
    forall g cr ce o x suf rhs frs sps w,
      cr = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> In (x, rhs) g
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w
      -> startState g x (cr, frs) = inr sps
      -> exists av sp,
          closure_multistep g (allNts g) (Sp rhs (ce, cr :: frs))
                              av sp
          /\ gamma_recognize g (unprocStackSyms sp.(stack)) w
          /\ In sp sps.
  Proof.
    intros g cr ce o x suf rhs frs sps w ? ? hn hw hi hg hs; subst; sis. 
    pose proof hs as hs'.
    eapply startState_closure_multistep_from_orig_sp' in hs'; eauto.
    destruct hs' as [av [sp [hc hg']]].
    repeat eexists; eauto.
    eapply closure_func_refines_closure_multistep; eauto.
    eapply initSps_result_incl_all_rhss; eauto.
  Qed.

  Inductive move_closure_multistep (g : grammar) :
    subparser -> list token -> subparser -> list token -> Prop :=
  | MC_empty :
      forall pred,
        move_closure_multistep g (Sp pred (SF None [], [])) []
                                 (Sp pred (SF None [], [])) []
  | MC_terminal :
      forall pred suf frs o a l ts,
        move_closure_multistep g (Sp pred (SF o (T a :: suf), frs)) ((a,l) :: ts)
                                 (Sp pred (SF o (T a :: suf), frs)) ((a,l) :: ts)
  | MC_trans :
      forall av'' sp sp' sp'' sp''' ts ts'' ts''',
        move_step sp ts sp' ts''
        -> closure_multistep g (allNts g) sp' av'' sp''
        -> move_closure_multistep g sp'' ts'' sp''' ts'''
        -> move_closure_multistep g sp ts sp''' ts'''.

  Hint Constructors move_closure_multistep : core.

  Ltac induct_mcms hm :=
    induction hm as [ ?
                    | ? ? ? ? ? ? ? 
                    | ? ? ? ? ? ? ? ? hm hc hms IH].

  Ltac inv_mcms hm :=
    inversion hm as [ ? 
                    | ? ? ? ? ? ? ? 
                    | ? ? ? ? ? ? ? ? hm' hc hms IH]; subst; clear hm.

  Lemma mcms_preserves_label :
    forall g sp sp' w w',
      move_closure_multistep g sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g sp sp' w w' hm.
    induct_mcms hm; auto.
    apply move_step_preserves_label in hm.
    apply closure_multistep_preserves_label in hc; tc. 
  Qed.

  Lemma mcms_succ_final_config :
    forall g sp sp' wpre wsuf,
      move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
      -> wsuf = []
      -> finalConfig sp' = true.
  Proof.
    intros g sp sp' wpre wsuf hm.
    induction hm; intros heq; auto.
    inv heq.
  Qed.

  Lemma mcms_word_length_le :
    forall g sp sp' ts ts',
      move_closure_multistep g sp ts sp' ts'
      -> length ts' <= length ts. 
  Proof.
    intros g sp sp' ts ts' hm.
    induct_mcms hm; auto.
    inv hm; sis; auto.
  Qed.

  Lemma mcms_backtrack_three_groups' :
    forall g sp sp'' w wsuf,
      move_closure_multistep g sp w sp'' wsuf
      -> forall wpre wmid,
        wpre ++ wmid ++ wsuf = w
        -> exists sp',
          move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
          /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros g sp sp'' w wsuf hm.
    induct_mcms hm; intros wpre wmid heq; subst.
    - rewrite app_nil_r in *; apply app_eq_nil in heq; destruct heq; subst; eauto.
    - apply app_double_left_identity_nil in heq; destruct heq; subst; sis; eauto.
    - destruct wpre as [| t wpre]; sis.
      + destruct wmid as [| t wmid]; sis.
        * apply move_step_word_length_lt in hm; apply mcms_word_length_le in hms.
          omega.
        * inv hm; eauto.
      + inv hm; destruct (IH wpre wmid) as [sp' [hms' hms'']]; eauto.
  Qed.

  Lemma mcms_backtrack_three_groups :
    forall g sp sp'' wpre wmid wsuf,
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf
      -> exists sp',
        move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
        /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms_backtrack_three_groups'; eauto.
  Qed.

  Lemma mcms_backtrack_two_groups :
    forall g sp sp'' wpre wsuf,
      move_closure_multistep g sp (wpre ++ wsuf) sp'' []
      -> exists sp',
        move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
        /\ move_closure_multistep g sp' wsuf sp'' [].
  Proof.
    intros g sp sp'' wpre wsuf hm.
    assert (happ : wpre ++ wsuf = (wpre ++ wsuf ++ [])) by apps.
    rewrite happ in hm.
    eapply mcms_backtrack_three_groups in hm; rew_anr; eauto.
  Qed.

  Lemma mcms_backtrack_terminal :
    forall g sp sp'' t wpre wsuf,
      move_closure_multistep g sp (wpre ++ t :: wsuf) sp'' wsuf
      -> exists sp',
        move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf)
        /\ move_closure_multistep g sp' (t :: wsuf) sp'' wsuf.
  Proof.
    intros; rewrite cons_app_singleton in *.
    eapply mcms_backtrack_three_groups; eauto.
  Qed.

  Lemma mcms_words_eq__subparsers_eq' :
    forall g sp sp' ts ts',
      move_closure_multistep g sp ts sp' ts'
      -> ts = ts'
      -> sp = sp'.
  Proof.
    intros g sp sp' ts ts' hm heq; inv_mcms hm; auto.
    apply move_step_word_length_lt in hm'; apply mcms_word_length_le in hms; omega.
  Qed.

  Lemma mcms_words_eq__subparsers_eq :
    forall g sp sp' ts,
      move_closure_multistep g sp ts sp' ts
      -> sp = sp'.
  Proof.
    intros; eapply mcms_words_eq__subparsers_eq'; eauto. 
  Qed.

  Lemma mcms_inv_nonempty_word :
    forall g sp sp'' t wsuf,
      move_closure_multistep g sp (t :: wsuf) sp'' wsuf
      -> exists av' av'' sp',
        move_step sp (t :: wsuf) sp' wsuf
        /\ closure_multistep g av' sp' av'' sp''.
  Proof.
    intros g sp sp'' t wsuf hm; inv_mcms hm; auto.
    - exfalso; eapply cons_neq_tail; eauto.
    - inv hm'; apply mcms_words_eq__subparsers_eq in hms;
        destruct hms; subst; eauto. 
  Qed.

  Lemma mcms_consume_exists_intermediate_subparser :
    forall g sp sp'' t wsuf,
      move_closure_multistep g sp (t :: wsuf) sp'' wsuf
      -> exists av'' sp',
        move_step sp (t :: wsuf) sp' wsuf
        /\ closure_multistep g (allNts g) sp' av'' sp''.
  Proof.
    intros g sp sp'' t wsuf hm; inv_mcms hm.
    - exfalso; eapply cons_neq_tail; eauto.
    - inv hm'.
      eapply mcms_words_eq__subparsers_eq in hms;
        destruct hms; subst; eauto.
  Qed.

  Lemma mcms_recognize_nil_empty :
    forall g sp,
      stable_config sp.(stack)
      -> gamma_recognize g (unprocStackSyms sp.(stack)) []
      -> move_closure_multistep g sp [] sp [].
  Proof.
    intros g [pred stk] hs hg; simpl in hs.
    inversion hs as [| a suf frs]; subst; clear hs; sis; auto.
    apply gamma_recognize_terminal_head in hg.
    destruct hg as [? [? [heq ?]]]; inv heq.
  Qed.

  Lemma mcms_subparser_consumes_remaining_input :
    forall g w sp,
      no_left_recursion g
      -> stable_config sp.(stack)
      -> suffix_stack_wf g sp.(stack)
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> exists sp'', 
          move_closure_multistep g sp w sp'' [].
  Proof.
    intros g w; induction w as [| t w' IH]; intros sp hn hs hw hg.
    - eapply mcms_recognize_nil_empty in hg; eauto.
    - assert (hm : exists sp', move_step sp (t :: w') sp' w'). 
      { apply move_step_recognize_cons in hg; auto. }
      destruct hm as [sp' hm].
      assert (hc : exists av'' sp'', 
                 closure_multistep g (allNts g) sp' av'' sp''
                 /\ gamma_recognize g (unprocStackSyms sp''.(stack)) w').
      { eapply exists_cm_target_preserving_unprocStackSyms_recognize; eauto.
        - eapply move_step_preserves_suffix_stack_wf_invar; eauto.
        - destruct sp'; apply unavailable_nts_allNts. 
        - eapply move_step_preserves_unprocStackSyms_recognize; eauto. }
      destruct hc as [av'' [sp'' [hc hg'']]].
      eapply IH in hg''; eauto.
      + destruct hg'' as [sp''' hmcms]; eauto.
      + eapply stable_config_after_closure_multistep; eauto.
      + eapply closure_multistep_preserves_suffix_stack_wf_invar; eauto.
        eapply move_step_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Lemma mcms_transitive :
    forall g w w' sp sp',
      move_closure_multistep g sp w sp' w'
      -> forall sp'' w'',
        move_closure_multistep g sp' w' sp'' w''
        -> move_closure_multistep g sp w sp'' w''.
  Proof.
    intros g w w' sp sp' hm.
    induction hm; intros sp'''' w'' hm'; inv hm'; eauto.
  Qed.

  Lemma mcms_transitive_three_groups :
    forall g wpre wmid wsuf sp sp' sp'',
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      -> move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf
      -> move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms_transitive; eauto.
  Qed.

  (* Next definitions and lemmas relate to this invariant *)
  Definition subparsers_complete_wrt_originals g sps wpre sps' wsuf : Prop :=
    forall sp sp',
      In sp sps
      -> move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
      -> In sp' sps'.

  Lemma move_closure_op_preserves_subparsers_complete_invar :
    forall g a l wpre wsuf sps sps' sps'' sps''',
      subparsers_complete_wrt_originals g sps wpre sps' ((a,l) :: wsuf)
      -> move a sps' = inr sps''
      -> closure g sps'' = inr sps'''
      -> subparsers_complete_wrt_originals g sps (wpre ++ [(a,l)]) sps''' wsuf.
  Proof.
    intros g a l wpre wsuf sps sps' sps'' sps''' hinvar hm hc. 
    unfold subparsers_complete_wrt_originals. 
    rewrite <- app_assoc; simpl; intros sp sp''' hi hms.
    eapply mcms_backtrack_terminal in hms.
    destruct hms as [sp' [hms hms']].
    apply hinvar in hms; auto.
    eapply mcms_consume_exists_intermediate_subparser in hms'.
    destruct hms' as [av'' [sp'' [hm' hc']]].
    eapply move_func_refines_move_step in hm'; eauto.
    eapply closure_func_refines_closure_multistep; eauto.
  Qed.

  Lemma llPredict'_succ_labels_eq_after_prefix :
    forall g orig_sps wsuf wpre curr_sps rhs,
      subparsers_complete_wrt_originals g orig_sps wpre curr_sps wsuf
      -> llPredict' g curr_sps wsuf = PredSucc rhs
      -> exists wpre' wsuf',
          wpre ++ wsuf = wpre' ++ wsuf'
          /\ forall sp sp',
            In sp orig_sps
            -> move_closure_multistep g sp (wpre' ++ wsuf') sp' wsuf'
            -> sp.(prediction) = rhs.
  Proof.
    intros g orig_sps wsuf.
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps rhs hi hl; 
      destruct curr_sps as [| curr_sp curr_sps]; sis; tc.
    - dmeq hall.
      + inv hl.
        exists wpre; exists []; split; auto.
        intros orig_sp curr_sp' hin hm.
        apply eq_trans with (y := curr_sp'.(prediction)).
        * eapply mcms_preserves_label; eauto.
        * apply hi in hm; auto.
          eapply allPredictionsEqual_in; eauto.
      + unfold handleFinalSubparsers in hl.
        destruct (filter _ _) as [| sp'' sps''] eqn:hf; tc.
        destruct (allPredictionsEqual sp'' sps'') eqn:ha'; tc.
        inv hl.
        exists wpre; exists []; split; auto.
        intros orig_sp curr_sp' hin hm.
        apply eq_trans with (y := curr_sp'.(prediction)).
        * eapply mcms_preserves_label; eauto.
        * pose proof hm as hm'.
          apply hi in hm; auto.
          apply mcms_succ_final_config in hm'; auto.
          eapply filter_In' in hm; eauto.
          rewrite hf in hm.
          eapply allPredictionsEqual_in; eauto.
    - destruct (allPredictionsEqual curr_sp curr_sps) eqn:ha.
      + inv hl.
        exists wpre; exists ((a,l) :: wsuf'); split; auto.
        intros orig_sp curr_sp' hin hm.
        apply eq_trans with (y := curr_sp'.(prediction)).
        * eapply mcms_preserves_label; eauto.
        * eapply hi in hm; eauto.
          eapply allPredictionsEqual_in; eauto.
      + dmeq hm; tc; dmeq hc; tc.
        eapply IH with (wpre := wpre ++ [(a,l)]) in hl; eauto.
        * destruct hl as [wpre' [wsuf'' [heq hall]]].
          exists wpre'; exists wsuf''; split; auto.
          rewrite <- heq; apps.
        * eapply move_closure_op_preserves_subparsers_complete_invar; eauto.
  Qed.

  Lemma subparsers_complete_invar_starts_true :
    forall g sps w,
      subparsers_complete_wrt_originals g sps [] sps w.
  Proof.
    intros g sps w sp sp' hi hm; sis.
    eapply mcms_words_eq__subparsers_eq in hm; subst; auto.
  Qed.

  (* One of the main lemmas in this file; if llPredict return a right-hand side
   and finds no ambiguity, then only that right-hand side will result in a 
   successful derivation *)
  (* This probably belongs in a different file, since it's involved in more than
   just proving completeness *)
  (* Also, I think there's a primed version of this lemma--this one may be deprecated *)
    Lemma llPredict_succ_at_most_one_rhs_applies :
    forall g cr ce o x suf frs w rhs rhs',
      cr = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> In (x, rhs) g
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w
      -> llPredict g x (cr, frs) w = PredSucc rhs'
      -> rhs' = rhs.
  Proof.
    intros g cr ce o x suf frs w rhs rhs' ? ? hn hw hi hg hl; subst; sis.
    unfold llPredict in hl.
    destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
    eapply startState_closure_multistep_from_orig_sp in hs; eauto.
    destruct hs as [av [sp [hc [hg' hi']]]].
    eapply llPredict'_succ_labels_eq_after_prefix
      with (wpre := []) (orig_sps := sps) in hl;
      [ .. | eapply subparsers_complete_invar_starts_true; eauto].
    destruct hl as [wpre' [wsuf' [? hall]]]; sis; subst.
    eapply mcms_subparser_consumes_remaining_input in hg'; eauto.
    - destruct hg' as [sp'' hm].
      eapply mcms_backtrack_two_groups in hm.
      destruct hm as [sp' [hm hm']].
      apply hall in hm; subst; auto.
      apply closure_multistep_preserves_label in hc; auto.
    - eapply stable_config_after_closure_multistep; eauto.
    - eapply closure_multistep_preserves_suffix_stack_wf_invar; eauto; sis.
      apply push_preserves_suffix_frames_wf_invar; auto.
  Qed.

  (* Moving on to the case where llPredict returns Ambig... *)

  Inductive move_closure_multistep' (g : grammar) :
    subparser -> list token -> subparser -> list token -> Prop :=
  | MC_empty' :
      forall pred ts,
        move_closure_multistep' g (Sp pred (SF None [], []))
                                ts
                                (Sp pred (SF None [], []))
                                ts
  | MC_terminal' :
      forall pred suf frs o a ts,
        move_closure_multistep' g (Sp pred (SF o (T a :: suf), frs))
                                ts
                                (Sp pred (SF o (T a :: suf), frs))
                                ts
  | MC_trans' :
      forall av'' sp sp' sp'' sp''' ts ts'' ts''',
        move_step sp ts sp' ts''
        -> closure_multistep g (allNts g) sp' av'' sp''
        -> move_closure_multistep' g sp'' ts'' sp''' ts'''
        -> move_closure_multistep' g sp ts sp''' ts'''.

  Hint Constructors move_closure_multistep' : core.

  Definition subparsers_sound_wrt_originals g sps wpre sps' wsuf :=
    forall sp',
      In sp' sps'
      -> exists sp,
        In sp sps
        /\ move_closure_multistep' g sp (wpre ++ wsuf) sp' wsuf.

  Lemma move_func_refines_move_step_backward :
    forall a l w sps sps' sp',
      move a sps = inr sps'
      -> In sp' sps'
      -> exists sp,
          In sp sps
          /\ move_step sp ((a,l) :: w) sp' w.
  Proof.
    intros a l s sps sps' sp' hm hi.
    unfold move in hm.
    eapply aggrMoveResults_map_backwards in hm; eauto.
    destruct hm as [sp [hi' hm]].
    exists sp; split; auto.
    apply move_step_moveSp; auto.
  Qed.

  Lemma closure_func_refines_closure_multistep_backward :
    forall g sps sps'' sp'',
      all_suffix_stacks_wf g sps
      -> closure g sps = inr sps''
      -> In sp'' sps''
      -> exists av'' sp,
          In sp sps
          /\ closure_multistep g (allNts g) sp av'' sp''.
  Proof.
    intros g sps sps'' sp'' ha hc hi.
    unfold closure in hc.
    eapply aggrClosureResults_map_backwards in hc; eauto.
    destruct hc as [sp [sps' [hi' [heq hi'']]]].
    eapply spClosure_sound_wrt_closure_multistep in heq; destruct heq; eauto.
  Qed.

  Lemma mcms'_transitive :
    forall g w w' sp sp',
      move_closure_multistep' g sp w sp' w'
      -> forall sp'' w'',
        move_closure_multistep' g sp' w' sp'' w''
        -> move_closure_multistep' g sp w sp'' w''.
  Proof.
    intros g w w' sp sp' hm.
    induction hm; intros sp'''' w'' hm'; inv hm'; eauto.
  Qed.

  Lemma mcms'_transitive_three_groups :
    forall g wpre wmid wsuf sp sp' sp'',
      move_closure_multistep' g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      -> move_closure_multistep' g sp' (wmid ++ wsuf) sp'' wsuf
      -> move_closure_multistep' g sp (wpre ++ wmid ++ wsuf) sp'' wsuf.
  Proof.
    intros; eapply mcms'_transitive; eauto.
  Qed.

  Lemma mcms'_preserves_label :
    forall g sp sp' w w',
      move_closure_multistep' g sp w sp' w'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g sp sp' w w' hm.
    induction hm; auto.
    apply move_step_preserves_label in H.
    apply closure_multistep_preserves_label in H0; tc.
  Qed.

  Lemma move_closure_op_preserves_subparsers_sound_invar :
    forall g a l wpre wsuf sps sps' sps'' sps''',
      all_suffix_stacks_wf g sps'
      -> subparsers_sound_wrt_originals g sps wpre sps' ((a,l) :: wsuf)
      -> move a sps' = inr sps''
      -> closure g sps'' = inr sps'''
      -> subparsers_sound_wrt_originals g sps (wpre ++ [(a,l)]) sps''' wsuf.
  Proof.
    intros g a l wpre wsuf sps sps' sps'' sps''' ha hi hm hc. 
    unfold subparsers_sound_wrt_originals in *.
    rewrite <- app_assoc; simpl; intros sp''' hi'''.
    assert (ha'' : all_suffix_stacks_wf g sps'').
    { eapply move_preserves_suffix_stack_wf_invar; eauto. }
    assert (ha''' : all_suffix_stacks_wf g sps''').
    { eapply closure_preserves_suffix_stack_wf_invar; eauto. }
    eapply closure_func_refines_closure_multistep_backward in hc; eauto.
    destruct hc as [av'' [sp'' [hi'' hc]]].
    eapply move_func_refines_move_step_backward
      with (w := wsuf) in hm; eauto.
    destruct hm as [sp' [hi' hm]].
    apply hi in hi'; clear hi.
    destruct hi' as [sp [hi hmcms]].
    exists sp; split; auto.
    rewrite cons_app_singleton in *.
    eapply mcms'_transitive_three_groups; eauto.
    econstructor; eauto.
    apply stable_config_after_closure_multistep in hc.
    destruct sp''' as [pred ([suf], frs)]; inv hc; auto.
  Qed.

  Lemma llPredict'_ambig_rhs_leads_to_successful_parse :
    forall g orig_sps wsuf wpre curr_sps rhs,
      all_suffix_stacks_wf g curr_sps
      -> subparsers_sound_wrt_originals g orig_sps wpre curr_sps wsuf
      -> llPredict' g curr_sps wsuf = PredAmbig rhs
      -> exists orig_sp final_sp,
          In orig_sp orig_sps
          /\ orig_sp.(prediction) = rhs
          /\ move_closure_multistep' g orig_sp (wpre ++ wsuf) final_sp []
          /\ finalConfig final_sp = true.
  Proof.
    intros g orig_sps wsuf.
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps rhs ha hi hl; destruct curr_sps as [| csp csps]; sis; tc.
    - destruct (allPredictionsEqual csp csps) eqn:ha'; tc.
      unfold handleFinalSubparsers in hl.
      destruct (filter _ _) as [| csp' csps'] eqn:hf; tc.
      destruct (allPredictionsEqual csp' csps') eqn:ha''; tc.
      inv hl.
      unfold subparsers_sound_wrt_originals in hi.
      pose proof hf as hf'.
      eapply filter_cons_in in hf.
      apply hi in hf.
      destruct hf as [orig_sp [hi' hm]].
      exists orig_sp; exists csp'; repeat split; auto.
      + (* easy *)
        eapply mcms'_preserves_label; eauto.
      + assert (hi'' : In csp' (filter finalConfig (csp :: csps))).
        { rewrite hf'; apply in_eq. }
        eapply filter_In in hi''; destruct hi''; auto.
    - destruct (allPredictionsEqual _ _); tc.
      destruct (move _ _ ) as [e | sps'] eqn:hm; tc.
      destruct (closure _ _) as [e | sps''] eqn:hc; tc.
      eapply IH with (wpre := wpre ++ [(a,l)]) in hl.
      + destruct hl as [osp [fsp [hi' [heq [hm' hf]]]]].
        exists osp; exists fsp; repeat split; auto.
        rewrite <- app_assoc in hm'; auto.
      + eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
        apply closure_preserves_suffix_stack_wf_invar in hc; auto.
      + eapply move_closure_op_preserves_subparsers_sound_invar; eauto.
  Qed.

  Lemma closure_step_ussr_backward :
    forall g av av' sp sp' w,
      closure_step g av sp av' sp'
      -> gamma_recognize g (unprocStackSyms sp'.(stack)) w
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w.
  Proof.
    intros g av av' sp sp' w hc hg.
    inv hc; sis; auto.
    apply gamma_recognize_split in hg.
    destruct hg as [wpre [wsuf [? [hg hg']]]]; subst; repeat (econstructor; eauto).
  Qed.

  Lemma closure_multistep_ussr_backward :
    forall g av av' sp sp' w,
      closure_multistep g av sp av' sp'
      -> gamma_recognize g (unprocStackSyms sp'.(stack)) w
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w.
  Proof.
    intros g av av' sp sp' w hc hg; induction hc; sis; auto.
    apply IHhc in hg.
    eapply closure_step_ussr_backward; eauto.
  Qed.

  Lemma mcms'_final_config :
    forall g w sp sp',
      move_closure_multistep' g sp w sp' []
      -> finalConfig sp' = true
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w.
  Proof.
    intros g w; induction w as [| t w IH]; intros sp sp' hm hf.
    - inv hm; sis.
      + constructor.
      + dm; tc. 
      + inv H.
    - inv hm.
      inv H; sis.
      apply Cons_rec with (wpre := [(a,l)]).
      + constructor.
      + apply IH in H1; auto.
        eapply closure_multistep_ussr_backward in H1; eauto.
        sis; auto.
  Qed.

  Lemma closure_ussr_backwards :
    forall g sps sps' sp' w,
      all_suffix_stacks_wf g sps
      -> closure g sps = inr sps'
      -> In sp' sps'
      -> gamma_recognize g (unprocStackSyms sp'.(stack)) w
      -> exists sp av',
          In sp sps
          /\ closure_multistep g (allNts g) sp av' sp'
          /\ gamma_recognize g (unprocStackSyms sp.(stack)) w.
  Proof.
    intros g sps sps' sp' w ha hc hi hg.
    eapply closure_func_refines_closure_multistep_backward in hc; eauto.
    destruct hc as [av'' [sp [hi' hc]]].
    repeat eexists; eauto.
    eapply closure_multistep_ussr_backward; eauto.
  Qed.

    Lemma llPredict_ambig_rhs_unproc_stack_syms :
    forall g cr ce o x suf frs w rhs,
      cr = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> llPredict g x (cr, frs) w = PredAmbig rhs
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g cr ce o x suf frs w rhs ? ? hn hw hl; subst; sis.
    pose proof hl as hl'; apply llPredict_ambig_in_grammar in hl'.
    unfold llPredict in hl.
    destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
    eapply llPredict'_ambig_rhs_leads_to_successful_parse
      with (orig_sps := sps) (wpre := []) in hl; sis.
    - destruct hl as [sp [sp' [hi [heq [hm hf]]]]]; subst.
      eapply mcms'_final_config in hm; auto.
      unfold startState in hs.
      eapply closure_ussr_backwards in hs; eauto.
      + destruct hs as [init_sp [av' [hi' [hc hg]]]].
        (* lemma? *)
        unfold initSps in hi'.
        apply in_map_iff in hi'.
        destruct hi' as [rhs [heq hi']]; subst; sis.
        apply closure_multistep_preserves_label in hc; sis; subst; auto.
      + (* lemma *)
        intros init_sp hi'.
        eapply initSps_preserves_suffix_stack_wf_invar; eauto.
    - eapply stacks_wf_in_startState_result; eauto.
    - red. intros sp' hi; sis.
      exists sp'; split; auto.
      eapply closure_func_refines_closure_multistep_backward in hi; eauto.
      + destruct hi as [av'' [sp0 [hi hc]]].
        assert (hst : stable_config sp'.(stack)).
        { eapply stable_config_after_closure_multistep; eauto. }
        destruct sp' as [pred ([suf'], frs')]; sis.
        inv hst; auto.
      + intros sp hi'.
        eapply initSps_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  (* Now some facts about how prediction doesn't return Reject when the initial
   stack's unprocessed symbols recognize the input *)

  Definition exists_successful_sp g sps w :=
    exists sp, In sp sps /\ gamma_recognize g (unprocStackSyms sp.(stack)) w.

  Lemma stable_config_recognize_nil__final_config :
    forall g sp,
      gamma_recognize g (unprocStackSyms sp.(stack)) []
      -> stable_config sp.(stack)
      -> finalConfig sp = true.
  Proof.
    intros g [pred ([o [| [a | x] suf]], frs)] hg hs; inv hs; sis; auto.
    apply gamma_recognize_terminal_head in hg.
    destruct hg as [l [w' [heq hg]]]; inv heq.
  Qed.

  Lemma stable_config_gamma_recognize_terminal_inv :
    forall g sp t w',
      stable_config sp.(stack)
      -> gamma_recognize g (unprocStackSyms sp.(stack)) (t :: w')
      -> exists o a suf frs,
          sp.(stack) = (SF o (T a :: suf), frs).
  Proof.
    intros g [pred ([o [| [a|x] suf]], frs)] t w' hs hg; sis.
    - destruct frs; sis.
      + inv hg.
      + inv hs.
    - repeat eexists; eauto. 
    - inv hs.
  Qed.
  
  Lemma moveSp_preserves_successful_sp_invar :
    forall g sp a l w',
      stable_config sp.(stack)
      -> gamma_recognize g (unprocStackSyms sp.(stack)) ((a,l) :: w')
      -> exists sp',
          moveSp a sp = MoveSucc sp'
          /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w'.
  Proof.
    intros g sp a l w' hs hg.
    pose proof hg as hg'.
    apply stable_config_gamma_recognize_terminal_inv in hg; auto.
    destruct hg as [o [a' [suf [frs heq]]]].
    unfold moveSp.
    destruct sp as [pred stk]; subst; sis.
    rewrite heq; rewrite heq in hg'; sis.
    inversion hg' as [| ? ? ? ? hs' hg'' heq' heq'']; subst; clear hg'.
    inv hs'; inv heq''.
    dms; tc; eauto.
  Qed.

  (* refactor *)
  Lemma aggrMoveResults_map_preserves_successful_sp_invar :
    forall g sp sps sps' a l w',
      all_stacks_stable sps
      -> In sp sps
      -> gamma_recognize g (unprocStackSyms sp.(stack)) ((a,l) :: w')
      -> aggrMoveResults (map (moveSp a) sps) = inr sps'
      -> exists sp',
          moveSp a sp = MoveSucc sp'
          /\ In sp' sps'
          /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w'.
  Proof.
    intros g sp sps.
    induction sps as [| hd tl IH]; intros sps' a l w' ha hi hg hm.
    - inv hi.
    - destruct hi as [hh | ht]; subst.
      + simpl in hm.
        apply moveSp_preserves_successful_sp_invar in hg.
        * destruct hg as [sp' [hmsp hg]].
          rewrite hmsp in hm.
          dm; tc.
          inv hm.
          eexists; repeat split; eauto.
          apply in_eq.
        * firstorder. 
      + simpl in hm.
        dm; tc.
        * dmeq hag; tc.
          inv hm.
          eapply IH in hag; eauto; firstorder.
        * dmeq hag; tc.
          inv hm.
          eapply IH in hag; eauto; firstorder.
  Qed.

  Lemma move_preserves_successful_sp_invar :
    forall g sps sps' a l w',
      all_stacks_stable sps
      -> exists_successful_sp g sps ((a,l) :: w')
      -> move a sps = inr sps'
      -> exists_successful_sp g sps' w'.
  Proof.
    intros g sps sps' a l w' ha he hm.
    destruct he as [sp [hi hg]].
    red.
    eapply aggrMoveResults_map_preserves_successful_sp_invar in hm; eauto.
    firstorder.
  Qed.

  Lemma spClosureStep_preserves_successful_sp_invar :
    forall g av av' sp sps' w,
      gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> spClosureStep g av sp = CstepK av' sps'
      -> exists_successful_sp g sps' w.
  Proof.
    intros g av av' sp sps' w hg hs.
    unfold spClosureStep in hs; dmeqs h; tc; sis; inv hs.
    - eexists; split; [apply in_eq | auto].
    - apply gamma_recognize_nonterminal_head in hg. 
      destruct hg as [rhs [wpre [wsuf [? [hi [hg hg']]]]]]; subst. 
      eexists; split.
      + apply in_map_iff.
        eexists; split; eauto.
        apply rhssForNt_in_iff; eauto.
      + sis; apply gamma_recognize_app; auto.
    - exfalso.
      apply gamma_recognize_nonterminal_head in hg. 
      destruct hg as [rhs [wpre [wsuf [? [hi [hg hg']]]]]]; subst.
      apply lhs_mem_allNts_true in hi; tc.
  Qed.

  Lemma spClosure_preserves_successful_sp_invar' :
    forall g pr (a : Acc lex_nat_pair pr) av sp (a' : Acc lex_nat_pair (meas g av sp)) sps' w,
      pr = meas g av sp
      -> spClosure g av sp a' = inr sps'
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> exists_successful_sp g sps' w.
  Proof.
    intros g pr a'.
    induction a' as [pr hlt IH]; intros av sp a sps'' w ? hs hg; subst.
    apply spClosure_success_cases in hs.
    destruct hs as [[hdone heq] | [sps' [av' [hs [crs [heq ha]]]]]]; subst.
    - firstorder.
    - pose proof hs as hs'. 
      eapply spClosureStep_preserves_successful_sp_invar in hs'; eauto.
      destruct hs' as [sp' [hi hg']].
      eapply aggrClosureResults_dmap_succ_elt_succ in ha; eauto.
      destruct ha as [? [? [hs' ha]]].
      eapply IH in hs'; eauto.
      + firstorder.
      + eapply spClosureStep_meas_lt; eauto.
  Qed.

  Lemma spClosure_preserves_successful_sp_invar :
    forall g av sp (a : Acc lex_nat_pair (meas g av sp)) sps' w,
      spClosure g av sp a = inr sps'
      -> gamma_recognize g (unprocStackSyms sp.(stack)) w
      -> exists_successful_sp g sps' w.
  Proof.
    intros; eapply spClosure_preserves_successful_sp_invar'; eauto.
  Qed.

  Lemma closure_preserves_successful_sp_invar :
    forall g sps sps' w,
      exists_successful_sp g sps w
      -> closure g sps = inr sps'
      -> exists_successful_sp g sps' w.
  Proof.
    intros g sps sps'' w he hc; destruct he as [sp [hi hg]]; red.
    unfold closure in hc.
    eapply aggrClosureResults_map_succ_elt_succ in hc; eauto.
    destruct hc as [sps' [hs ha]].
    eapply spClosure_preserves_successful_sp_invar in hs; eauto; firstorder.
  Qed.
  
  Lemma move_closure_preserves_successful_sp_invar :
    forall g sps sps' sps'' a l w',
      all_stacks_stable sps
      -> exists_successful_sp g sps ((a,l) :: w')
      -> move a sps = inr sps'
      -> closure g sps' = inr sps''
      -> exists_successful_sp g sps'' w'.
  Proof.
    intros g sps sps' sps'' a l w' ha he hm hc.
    eapply move_preserves_successful_sp_invar in hm; eauto.
    eapply closure_preserves_successful_sp_invar; eauto.
  Qed.
  
  Lemma exists_successful_sp_llPredict'_neq_reject :
    forall g w sps,
      all_suffix_stacks_wf g sps
      -> all_stacks_stable sps
      -> exists_successful_sp g sps w
      -> llPredict' g sps w <> PredReject.
  Proof.
    intros g w; induction w as [| (a,l) w' IH]; intros sps ha ha' hex; unfold not; intros hl; unfold exists_successful_sp in hex; sis.
    - destruct hex as [sp [hi hg]]. 
      destruct sps as [| sp' sps'].
      + inv hi.
      + dm; tc.
        (* lemma *)
        unfold handleFinalSubparsers in hl.
        destruct (filter _ _) as [| sp'' sps''] eqn:hf; dms; tc.
        apply stable_config_recognize_nil__final_config in hg; auto.
        eapply filter_In' in hg; eauto.
        rewrite hf in hg; inv hg.
    - destruct hex as [sp [hi hg]]. 
      destruct sps as [| sp' sps'].
      + inv hi.
      + dm; tc.
        destruct (move _ _) as [e | sps''] eqn:hm; tc.
        destruct (closure _ _) as [e | sps'''] eqn:hc; tc.
        eapply IH in hl; eauto.
        * red. 
          intros sp''' hi'.
          eapply move_preserves_suffix_stack_wf_invar in hm; eauto.
          eapply closure_preserves_suffix_stack_wf_invar in hc; auto.
        * red.
          intros sp''' hi'.
          eapply closure_func_refines_closure_multistep_backward in hc; eauto.
          -- destruct hc as [av'' [sp'' [hi'' hc]]].
             eapply stable_config_after_closure_multistep; eauto.
          -- red; intros sp'''' hi''.
             eapply move_preserves_suffix_stack_wf_invar in hm; auto.
        * eapply move_closure_preserves_successful_sp_invar; eauto.
          exists sp; split; eauto.
  Qed.

  Lemma initSps_preserves_exists_successful_sp_invar :
    forall g fr o x suf frs w,
      fr = SF o (NT x :: suf)
      -> gamma_recognize g (unprocStackSyms (fr, frs)) w
      -> exists_successful_sp g (initSps g x (fr, frs)) w.
  Proof.
    intros g fr o x suf frs w ? hg; subst; sis.
    apply gamma_recognize_nonterminal_head in hg.
    destruct hg as [rhs [wpre [wsuf [? [hi [hg hg']]]]]]; subst.
    eexists; split.
    - apply in_map_iff; eexists; split; eauto.
      apply rhssForNt_in_iff; eauto.
    - sis; apply gamma_recognize_app; auto.
  Qed.

  Lemma ussr_llPredict_neq_reject :
    forall g fr o x suf frs w,
      fr = SF o (NT x :: suf)
      -> suffix_stack_wf g (fr, frs)
      -> gamma_recognize g (unprocStackSyms (fr, frs)) w
      -> llPredict g x (fr, frs) w <> PredReject.
  Proof.
    intros g fr o x suf frs w ? hw hg; unfold not; intros hl; subst.
    unfold llPredict in hl.
    destruct (startState _ _ _) as [e | sps] eqn:hs; tc.
    eapply exists_successful_sp_llPredict'_neq_reject; eauto.
    - (* lemma *)
      eapply closure_preserves_suffix_stack_wf_invar; eauto.
      red; intros.
      eapply initSps_preserves_suffix_stack_wf_invar; eauto.
    - (* lemma *)
      red; intros.
      eapply closure_func_refines_closure_multistep_backward in hs; eauto.
      + firstorder.
        eapply stable_config_after_closure_multistep; eauto.
      + red; intros.
        eapply initSps_preserves_suffix_stack_wf_invar; eauto.
    - eapply closure_preserves_successful_sp_invar; eauto.
      eapply initSps_preserves_exists_successful_sp_invar; eauto.
  Qed.

End PredictionCompleteFn.
