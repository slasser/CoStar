Require Import Bool List Omega.
Require Import GallStar.Defs. 
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Fixpoint unprocTailSyms (frs : list location) : list symbol :=
  match frs with 
  | []                            => []
  | Loc _ _ [] :: _               => [] (* impossible for a well-formed stack *)
  | Loc _ _ (T _ :: _) :: _       => [] (* impossible for a well-formed stack *)
  | Loc _ _ (NT x :: suf) :: frs' => suf ++ unprocTailSyms frs'
  end.

Definition unprocStackSyms stk : list symbol :=
  match stk with
  | (Loc o pre suf, frs) => suf ++ unprocTailSyms frs
  end.

Inductive move_step (g : grammar) :
  subparser -> list token -> subparser -> list token -> Prop :=
| MV_consume :
    forall av pred o pre suf a l ts frs,
      move_step g
                (Sp av
                    pred
                    (Loc o pre (T a :: suf), frs))
                ((a, l) :: ts)
                (Sp (allNts g)
                    pred
                    (Loc o (pre ++ [T a]) suf, frs))
                ts.

Hint Constructors move_step.

Lemma move_step_preserves_label :
  forall g sp sp' w w',
    move_step g sp w sp' w'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' w w' hm; inv hm; auto.
Qed.

Lemma move_step_word_length_lt :
  forall g sp sp' ts ts',
    move_step g sp ts sp' ts'
    -> length ts' < length ts.
Proof.
  intros g sp sp' ts ts' hm; inv hm; auto.
Qed.

Lemma move_func_refines_move_step :
  forall g t ts sp sp' sps sps',
    In sp sps
    -> move_step g sp (t :: ts) sp' ts
    -> move g t sps = inr sps'
    -> In sp' sps'.
Proof.
  intros g t ts sp sp' sps sps' hi hr hf.
  inv hr.
  eapply move_succ_all_sps_step; eauto.
Qed.

Lemma moveSp_move_step :
  forall g t w' sp sp',
    move_step g sp (t :: w') sp' w'
    -> moveSp g t sp = SpMoveSucc sp'.
Proof.
  intros g t w' sp sp' hm.
  inv hm; unfold moveSp; dms; tc.
Qed.

Lemma move_step_preserves_lstack_wf_invar :
  forall g sp sp' t w,
    move_step g sp (t :: w) sp' w
    -> lstack_wf g sp.(stack)
    -> lstack_wf g sp'.(stack).
Proof.
  intros g sp sp' t w' hm hw.
  eapply moveSp_preserves_lstack_wf_invar; eauto.
  eapply moveSp_move_step; eauto.
Qed.

Lemma unavailable_nts_invar_holds_after_move_step :
  forall g sp sp' t w',
    move_step g sp (t :: w') sp' w'
    -> unavailable_nts_invar g sp'.
Proof.
  intros g sp sp' t w' hm.
  eapply unavailable_nts_invar_holds_after_moveSp.
  eapply moveSp_move_step; eauto.
Qed.

Lemma move_step_preserves_unprocStackSyms_recognize :
  forall g sp sp' t w',
    move_step g sp (t :: w') sp' w'
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
        move_step g sp (t :: w') sp' w'.
Proof.
  intros g [av pred stk] t w' hs hg; sis.
  inversion hs as [o pre | o pre a suf frs]; subst; clear hs; auto; sis.
  - inv hg. 
  - apply gamma_recognize_terminal_head in hg.
    destruct hg as [l' [w'' [heq hg]]]; inv heq; eauto.
Qed.

Inductive closure_step (g : grammar) : subparser -> subparser -> Prop :=
| CS_ret :
    forall av pred x o' pre pre' suf' frs,
      closure_step g
                   (Sp av
                       pred
                       (Loc (Some x) pre [], Loc o' pre' (NT x :: suf') :: frs))
                   (Sp (NtSet.add x av)
                       pred
                       (Loc o' (pre' ++ [NT x]) suf', frs))
| CS_push :
    forall av pred o pre x suf frs rhs,
      NtSet.In x av
      -> In (x, rhs) g
      -> closure_step g
                      (Sp av
                          pred
                          (Loc o pre (NT x :: suf), frs))
                      (Sp (NtSet.remove x av)
                          pred
                          (Loc (Some x) [] rhs,
                           Loc o pre (NT x :: suf) :: frs)).

Hint Constructors closure_step.

Lemma closure_step_preserves_label :
  forall g sp sp',
    closure_step g sp sp'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' hc; inv hc; auto.
Qed.

Lemma closure_step_preserves_lstack_wf_invar :
  forall g sp sp',
    closure_step g sp sp'
    -> lstack_wf g sp.(stack)
    -> lstack_wf g sp'.(stack).
Proof.
  intros g sp sp' hc hw; inv hc; sis; auto.
  eapply return_preserves_locations_wf_invar; eauto.
Qed.

Inductive closure_multistep (g : grammar) : subparser -> subparser -> Prop :=
| CMS_empty :
    forall av pred o pre,
      closure_multistep g (Sp av pred (Loc o pre [], []))
                          (Sp av pred (Loc o pre [], []))
| CMS_terminal :
    forall av pred o pre a suf frs,
      closure_multistep g (Sp av pred (Loc o pre (T a :: suf), frs))
                          (Sp av pred (Loc o pre (T a :: suf), frs))
| CMS_trans :
    forall sp sp' sp'',
      closure_step g sp sp'
      -> closure_multistep g sp' sp''
      -> closure_multistep g sp sp''.

Hint Constructors closure_multistep.

Lemma closure_multistep_preserves_label :
  forall g sp sp',
    closure_multistep g sp sp'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' hc.
  induction hc as [ ? ? ? ?
                  | ? ? ? ? ? ? ?
                  | ? ? ? hs hms]; auto.
  apply closure_step_preserves_label in hs; tc.
Qed.

Lemma closure_multistep_done_eq :
  forall g sp sp',
    closure_multistep g sp sp'
    -> spClosureStep g sp = SpClosureStepDone
    -> sp = sp'.
Proof.
  intros g sp sp' hc hs; unfold spClosureStep in hs; dms; tc;
  inversion hc as [? ? ? ? | ? ? ? ? ? ? ? | ? ? ? hs' ?]; subst; auto; inv hs'.
Qed.

Lemma closure_multistep_not_done_middle_sp_in_continuation :
  forall g sp sp'' sps',
    closure_multistep g sp sp''
    -> spClosureStep g sp = SpClosureStepK sps'
    -> exists sp',
        closure_step g sp sp'
        /\ closure_multistep g sp' sp''
        /\ In sp' sps'.
Proof.
  intros g sp sp'' sps' hc hs; unfold spClosureStep in hs; dmeqs h; tc; inv hs; eauto.
  - inv hc. inv H. eexists; repeat split; auto.
    apply in_eq.
  - inv hc. inv H.
    eexists; split.
    + constructor; eauto.
    + split.
      * auto.
      * apply in_map_iff.
        eexists; split; eauto.
        apply rhssForNt_in_iff; auto.
  - exfalso.
    inv hc. inv H.
    apply lhs_mem_allNts_true in H10; tc.
Qed.

Lemma spClosure_refines_closure_multistep' :
  forall (g  : grammar)
         (pr : nat * nat)
         (a  : Acc lex_nat_pair pr)
         (sp sp'' : subparser)
         (a' : Acc lex_nat_pair (meas g sp))
         (sps'' : list subparser),
    pr = meas g sp
    -> closure_multistep g sp sp''
    -> spClosure g sp a'  = inr sps''
    -> In sp'' sps''.
Proof.
  intros g pr a.
  induction a as [pr hlt IH]; intros sp sp'' a' sps'' heq hc hs; subst.
  unfold spClosure in hs.
  apply spClosure_success_cases in hs.
  destruct hs as [[hdone heq] | [sps' [hs [crs [heq ha]]]]]; subst.
  - (* sp must be in a "done" configuration, so sp = sp' *)
    apply closure_multistep_done_eq in hc; subst; auto.
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
  forall (g  : grammar) (sp sp'' : subparser) (a : Acc lex_nat_pair (meas g sp)) (sps'' : list subparser),
    closure_multistep g sp sp''
    -> spClosure g sp a  = inr sps''
    -> In sp'' sps''.
Proof.
  intros; eapply spClosure_refines_closure_multistep'; eauto.
Qed.

Lemma closure_func_refines_closure_multistep :
  forall g sp sp'' sps sps'',
    In sp sps
    -> closure_multistep g sp sp''
    -> closure g sps = inr sps''
    -> In sp'' sps''.
Proof.
  intros g sp sp'' sps sps'' hi hc hc'.
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
         (sp : subparser)
         (a' : Acc lex_nat_pair (meas g sp)),
    pr = meas g sp
    -> no_left_recursion g
    -> lstack_wf g sp.(stack)
    -> unavailable_nts_invar g sp
    -> gamma_recognize g (unprocStackSyms sp.(stack)) w
    -> exists sp',
      closure_multistep g sp sp'
      /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w.
Proof.
  intros w pr a.
  induction a as [m hlt IH]; intros g sp a' heq hn hw hu hg; subst.
  destruct sp as [av pred ([o pre [| [a | x] suf]], frs)]; eauto.
  - destruct frs as [| fr' frs]; eauto.
    simpl in hw; pose proof hw as hw'.
    destruct fr' as [o' pre' [| [? | x] suf']]; inv hw'.
    specialize IH with (sp := Sp (NtSet.add x av) pred (Loc o' (pre' ++ [NT x]) suf', frs)).
    edestruct IH as [sp' [hcm hg']]; eauto.
    + eapply meas_lt_after_return; eauto. 
    + apply lex_nat_pair_wf.
    + eapply return_preserves_locations_wf_invar; eauto.
    + eapply return_preserves_unavailable_nts_invar; eauto.
  - simpl in hg; apply gamma_recognize_nonterminal_head in hg. 
    destruct hg as [rhs [wpre [wsuf [heq [hi [hg hg']]]]]]; subst.
    assert (hi' : NtSet.In x av).
    { eapply invars_imply_head_nt_available; eauto.
      apply NtSet.mem_spec; eapply lhs_mem_allNts_true; eauto. }
    specialize IH with 
        (sp := Sp (NtSet.remove x av) pred (Loc (Some x) [] rhs, 
                                           (Loc o pre (NT x :: suf) :: frs))).
    edestruct IH as [sp' [hcm hg'']]; eauto.
    + eapply meas_lt_after_push; eauto.
      apply rhssForNt_in_iff; auto.
    + apply lex_nat_pair_wf.
    + eapply push_preserves_locations_wf_invar; eauto. 
      apply rhssForNt_in_iff; auto. 
    + eapply push_preserves_unavailable_nts_invar; eauto.
    + simpl; apply gamma_recognize_app; auto.
    + exists sp'; split; auto.
      econstructor; eauto.
      constructor; auto.
Qed.

Lemma exists_cm_target_preserving_unprocStackSyms_recognize :
  forall g sp w,
    no_left_recursion g
    -> lstack_wf g sp.(stack)
    -> unavailable_nts_invar g sp
    -> gamma_recognize g (unprocStackSyms sp.(stack)) w
    -> exists sp',
        closure_multistep g sp sp'
        /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w.
Proof.
  intros; eapply exists_cm_target_preserving_unprocStackSyms_recognize'; eauto;
  apply lex_nat_pair_wf.
Qed.

Lemma closure_multistep_preserves_lstack_wf_invar :
  forall g sp sp',
    closure_multistep g sp sp'
    -> lstack_wf g sp.(stack)
    -> lstack_wf g sp'.(stack).
Proof.
  intros g sp sp' hc; induction hc; intros hw; auto.
  eapply IHhc.
  eapply closure_step_preserves_lstack_wf_invar; eauto.
Qed.

Lemma stable_config_after_closure_multistep :
  forall g sp sp',
    closure_multistep g sp sp'
    -> stable_config sp'.(stack).
Proof.
  intros g sp sp' hc.
  induction hc; try constructor; auto.
Qed.

Inductive move_closure_multistep (g : grammar) :
  subparser -> list token -> subparser -> list token -> Prop :=
| MC_empty :
    forall av pred o pre,
      move_closure_multistep g (Sp av pred (Loc o pre [], []))
                               []
                               (Sp av pred (Loc o pre [], []))
                               []
| MC_terminal :
    forall av pred o pre suf frs a l ts,
      move_closure_multistep g (Sp av pred (Loc o pre (T a :: suf), frs))
                               ((a,l) :: ts)
                               (Sp av pred (Loc o pre (T a :: suf), frs))
                               ((a,l) :: ts)
| MC_trans :
    forall sp sp' sp'' sp''' ts ts'' ts''',
      move_step g sp ts sp' ts''
      -> closure_multistep g sp' sp''
      -> move_closure_multistep g sp'' ts'' sp''' ts'''
      -> move_closure_multistep g sp ts sp''' ts'''.

Hint Constructors move_closure_multistep.

Ltac induct_mcms hm :=
  induction hm as [ ? ? ? ?
                  | ? ? ? ? ? ? ? ? ?
                  | ? ? ? ? ? ? ? hm hc hms IH].

Ltac inv_mcms hm :=
  inversion hm as [ ? ? ? ?
                  | ? ? ? ? ? ? ? ? ?
                  | ? ? ? ? ? ? ? hm' hc hms IH]; subst; clear hm.

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

Lemma move_closure_multistep_backtrack' :
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

Lemma move_closure_multistep_backtrack :
  forall g sp sp'' wpre wmid wsuf,
    move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf
    -> exists sp',
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
Proof.
  intros; eapply move_closure_multistep_backtrack'; eauto.
Qed.

Lemma move_closure_multistep_backtrack_once :
  forall g sp sp'' t wpre wsuf,
    move_closure_multistep g sp (wpre ++ t :: wsuf) sp'' wsuf
    -> exists sp',
      move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf)
      /\ move_closure_multistep g sp' (t :: wsuf) sp'' wsuf.
Proof.
  intros; rewrite cons_app_singleton in *.
  eapply move_closure_multistep_backtrack; eauto.
Qed.

Lemma mcms_words_eq_subparsers_eq' :
  forall g sp sp' ts ts',
    move_closure_multistep g sp ts sp' ts'
    -> ts = ts'
    -> sp = sp'.
Proof.
  intros g sp sp' ts ts' hm heq; inv_mcms hm; auto.
  apply move_step_word_length_lt in hm'; apply mcms_word_length_le in hms. 
  omega.
Qed.

Lemma mcms_words_eq_subparsers_eq :
  forall g sp sp' ts,
    move_closure_multistep g sp ts sp' ts
    -> sp = sp'.
Proof.
  intros; eapply mcms_words_eq_subparsers_eq'; eauto.
Qed.

Lemma mcms_inv_nonempty_word :
  forall g sp sp'' t wsuf,
    move_closure_multistep g sp (t :: wsuf) sp'' wsuf
    -> exists sp',
      move_step g sp (t :: wsuf) sp' wsuf
      /\ closure_multistep g sp' sp''.
Proof.
  intros g sp sp'' t wsuf hm; inv_mcms hm; auto.
  - exfalso; eapply cons_neq_tail; eauto.
  - inv hm'; apply mcms_words_eq_subparsers_eq in hms; subst; eauto.
Qed.

Lemma mcms_consume_exists_intermediate_subparser :
  forall g sp sp'' t wsuf,
    move_closure_multistep g sp (t :: wsuf) sp'' wsuf
    -> exists sp',
      move_step g sp (t :: wsuf) sp' wsuf
      /\ closure_multistep g sp' sp''.
Proof.
  intros g sp sp'' t wsuf hm.
  inv_mcms hm.
  - exfalso; eapply cons_neq_tail; eauto.
  - inv hm'.
    eapply mcms_words_eq_subparsers_eq in hms; subst; eauto.
Qed.

Lemma mcms_recognize_nil_empty :
  forall g sp,
    stable_config sp.(stack)
    -> gamma_recognize g (unprocStackSyms sp.(stack)) []
    -> move_closure_multistep g sp [] sp [].
Proof.
  intros g [av pred stk] hs hg; simpl in hs.
  inversion hs as [o pre | o pre a suf frs]; subst; clear hs; sis; auto.
  apply gamma_recognize_terminal_head in hg.
  destruct hg as [? [? [heq ?]]]; inv heq.
Qed.

Lemma mcms_subparser_consumes_remaining_input :
  forall g w sp,
    no_left_recursion g
    -> stable_config sp.(stack)
    -> lstack_wf g sp.(stack)
    -> gamma_recognize g (unprocStackSyms sp.(stack)) w
    -> exists sp'', 
      move_closure_multistep g sp w sp'' [].
Proof.
  intros g w; induction w as [| t w' IH]; intros sp hn hs hw hg.
  - apply mcms_recognize_nil_empty in hg; eauto.
  - assert (hm : exists sp', move_step g sp (t :: w') sp' w'). 
    { apply move_step_recognize_cons in hg; auto. }
    destruct hm as [sp' hm].
    assert (hc : exists sp'', 
               closure_multistep g sp' sp''
               /\ gamma_recognize g (unprocStackSyms sp''.(stack)) w').
    { eapply exists_cm_target_preserving_unprocStackSyms_recognize; eauto.
      - eapply move_step_preserves_lstack_wf_invar; eauto.
      - eapply unavailable_nts_invar_holds_after_move_step; eauto.
      - eapply move_step_preserves_unprocStackSyms_recognize; eauto. }
    destruct hc as [sp'' [hc hg'']].
    apply IH in hg''; auto.
    + destruct hg'' as [sp''' hmcms].
      exists sp'''; econstructor; eauto.
    + eapply stable_config_after_closure_multistep; eauto.
    + eapply closure_multistep_preserves_lstack_wf_invar; eauto.
      eapply move_step_preserves_lstack_wf_invar; eauto.
Qed.


(* Next definitions and lemmas relate to this invariant *)
Definition subparsers_complete_wrt_originals g sps wpre sps' wsuf : Prop :=
  forall sp sp',
    In sp sps
    -> move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
    -> In sp' sps'.

Lemma move_closure_op_preserves_subparsers_complete_invar :
  forall g t wpre wsuf sps sps' sps'' sps''',
    subparsers_complete_wrt_originals g sps wpre sps' (t :: wsuf)
    -> move g t sps' = inr sps''
    -> closure g sps'' = inr sps'''
    -> subparsers_complete_wrt_originals g sps (wpre ++ [t]) sps''' wsuf.
Proof.
  intros g t wpre wsuf sps sps' sps'' sps''' hinvar hm hc. 
  unfold subparsers_complete_wrt_originals. 
  rewrite <- app_assoc; simpl; intros sp sp''' hi hms.
  eapply move_closure_multistep_backtrack_once in hms.
  destruct hms as [sp' [hms hms']].
  apply hinvar in hms; auto.
  eapply mcms_consume_exists_intermediate_subparser in hms'.
  destruct hms' as [sp'' [hm' hc']].
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
  induction wsuf as [| t wsuf' IH]; intros wpre curr_sps rhs hi hl; 
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
      exists wpre; exists (t :: wsuf'); split; auto.
      intros orig_sp curr_sp' hin hm.
      apply eq_trans with (y := curr_sp'.(prediction)).
      * eapply mcms_preserves_label; eauto.
      * eapply hi in hm; eauto.
        eapply allPredictionsEqual_in; eauto.
    + dmeq hm; tc; dmeq hc; tc.
      eapply IH with (wpre := wpre ++ [t]) in hl; eauto.
      * destruct hl as [wpre' [wsuf'' [heq hall]]].
        exists wpre'; exists wsuf''; split; auto.
        rewrite <- heq; apps.
      * eapply move_closure_op_preserves_subparsers_complete_invar; eauto.
Qed.
    
Lemma subparsers_complete_invar_starts_true :
  forall g sp sp' sps w,
    In sp sps
    -> move_closure_multistep g sp w sp' w
    -> In sp' sps.
Proof.
  intros g sp sp' sps w hi hm.
  apply mcms_words_eq_subparsers_eq in hm; subst; auto.
Qed.



(* move this stuff *)


Lemma start_state_init_all_rhss :
  forall g fr o pre x suf frs rhs,
    In (x, rhs) g
    -> fr = Loc o pre (NT x :: suf)
    -> In (Sp (allNts g) rhs (Loc (Some x) [] rhs, fr :: frs))
          (map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, fr :: frs))
               (rhssForNt g x)).
Proof.
  intros g fr o pre x suf frs rhs hi heq; subst.
  apply in_map_iff.
  exists rhs; split; auto.
  apply rhssForNt_in_iff; auto.
Qed.


  
(* refactor *)
Lemma llPredict_succ_rhs_derives_at_most_one_prefix :
  forall g fr o pre x suf frs w rhs rhs',
    no_left_recursion g
    -> lstack_wf g (fr, frs)
    -> fr = Loc o pre (NT x :: suf)
    -> In (x, rhs) g
    -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms frs) w
    -> llPredict g x (fr, frs) w = PredSucc rhs'
    -> rhs' = rhs.
Proof.
  intros g fr o pre x suf frs w rhs rhs' hn hw heq hin hg hl; subst.
  unfold llPredict in hl.
  destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
  eapply llPredict'_succ_labels_eq_after_prefix
    with (wpre := []) (orig_sps := sps) 
    in hl; eauto.
  - destruct hl as [wpre [wsuf [heq hall]]]; sis.
    assert (hi : In (Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) 
                    (map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) 
                         (rhssForNt g x))).
    { apply in_map_iff. 
      eexists; split; eauto.
      apply rhssForNt_in_iff; auto. }
    assert (hex : exists sp',
               closure_multistep g (Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) sp'
               /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w).
    { eapply exists_cm_target_preserving_unprocStackSyms_recognize; eauto.
      - sis. apply push_preserves_locations_wf_invar; auto.
        apply rhssForNt_in_iff; auto.
      - (* lemma *)
        unfold unavailable_nts_invar. unfold unavailable_nts_are_open_calls.
        intros.
        ND.fsetdec. }
    destruct hex as [sp' [hcm hg']].
    assert (h_viable_cand : In sp' sps).
    { eapply aggrClosureResults_map_succ_elt_succ in hs; eauto.
      destruct hs as [sps' [hspc hall']].
      apply hall'.
      eapply spClosure_refines_closure_multistep; eauto. }
    eapply mcms_subparser_consumes_remaining_input in hg'; eauto.
    + destruct hg' as [sp'' hmcms].
      pose proof move_closure_multistep_backtrack as hb.
      assert (hpred : sp''.(prediction) = rhs).
      { eapply closure_multistep_preserves_label in hcm; sis; subst.
        eapply mcms_preserves_label in hmcms; auto. }
      rewrite heq in hmcms.
      assert (wpre ++ wsuf = wpre ++ wsuf ++ []) by apps.
      rewrite H in hmcms.
      eapply hb in hmcms.
      destruct hmcms as [sp''' [hmcms hmcms']].
      rewrite app_nil_r in hmcms.
      apply hall in hmcms; auto; subst.
      eapply closure_multistep_preserves_label in hcm; sis; auto.
    + eapply stable_config_after_closure_multistep; eauto.
    + eapply closure_multistep_preserves_lstack_wf_invar; eauto.
      sis.
      constructor; auto.
  - intros sp sp' hi hm.
    apply mcms_words_eq_subparsers_eq in hm; subst; auto.
Qed.





(* May not be necessary *)

Lemma aggrClosureResults_in_input_in_output :
  forall g sp sp' sps sps' sps'',
    In sp sps
    -> spClosure g sp (lex_nat_pair_wf _) = inr sps'
    -> In sp' sps'
    -> aggrClosureResults (map (fun sp => spClosure g sp (lex_nat_pair_wf _)) sps) = inr sps''
    -> In sp' sps''.
Proof.
  intros g sp sp' sps; induction sps as [| hd tl IH]; intros sps' sps'' hi hs hi' ha.
  - inv hi.
  - inv hi.
    + clear IH.
      sis.
      dms; tc.
      inv hs; inv ha.
      apply in_or_app; auto.
    + sis. 
      dm; tc.
      dmeq hagg; tc.
      inv ha.
      apply in_or_app; eauto.
Qed.    

Lemma heads_eq_tails_eq_eq :
  forall A (x y : A) (xs ys : list A),
    x = y -> xs = ys -> x :: xs = y :: ys.
Proof.
  intros; subst; auto.
Qed.

Lemma dmap_proof_irrel :
  forall B (sps : list subparser) (f f' : forall sp, In sp sps -> B),
    (forall sp, f sp = f' sp)
    -> dmap sps f = dmap sps f'.
Proof.
  intros B sps; induction sps as [| sp sps IH]; intros f f' hall; auto.
  apply heads_eq_tails_eq_eq; auto.
  - rewrite hall; auto.
  - apply IH.
    intros.
    auto.
    unfold eq_rect_r.
    simpl.
    rewrite hall. auto.
Qed.

Lemma dmap_proof_irrel' :
  forall B (sps : list subparser) (f f' : forall sp, In sp sps -> B),
    (forall sp (hi : In sp sps), f sp hi = f' sp hi)
    -> dmap sps f = dmap sps f'.
Proof.
  intros B sps; induction sps as [| sp sps IH]; intros f f' hall; auto.
  simpl; apply heads_eq_tails_eq_eq; auto.
  unfold eq_rect_r; simpl.
  apply IH; auto.
Qed.

Lemma aggrClosureResults_crs_eq :
  forall crs crs',
    crs = crs'
    -> aggrClosureResults crs = aggrClosureResults crs'.
Proof.
  intros; subst; auto.
Qed.

Lemma dmap_map : forall g sps,
    dmap sps (fun sp hi => spClosure g sp (lex_nat_pair_wf (meas g sp))) = map (fun sp => spClosure g sp (lex_nat_pair_wf (meas g sp))) sps.
Proof.
  intros g sps; induction sps as [| sp sps IH]; sis; auto.
  apply heads_eq_tails_eq_eq; auto.
Qed.

Lemma inr_intro :
  forall A B (b b' : B),
    (inr b : sum A B) = (inr b' : sum A B) -> b = b'.
Proof.
  intros A B b b' heq; inv heq; auto.
Qed.

(* clean up *) (* get hi out of the exists clause *)
Lemma aggrClosureResults_dmap :
  forall sp (sps : list subparser) (f : forall sp, In sp sps -> closure_result) sps'',
    In sp sps
    -> aggrClosureResults (dmap sps f) = inr sps''
    -> exists hi sps',
        f sp hi = inr sps'.
Proof.
  intros sp sps; induction sps as [| hd tl IH]; intros f sps'' hi ha.
  - inv hi.
  - destruct hi as [heq | hi]; subst.
    + simpl in ha.
      dmeq hf; tc. dm; tc. inv ha.
      unfold eq_ind_r in hf. simpl in hf.
      repeat eexists; eauto.
    + simpl in ha.
      dm; tc; dmeq hagg; tc.
      inv ha.
      unfold eq_rect_r in hagg. sis.
      apply IH in hagg; auto.
      destruct hagg as [hi' [sps' heq]].
      repeat eexists; eauto.
Qed.

Lemma aggrClosureResults_succ_eq :
  forall (sps : list subparser) (f f' : forall sp, In sp sps -> closure_result) sps' sps'',
    aggrClosureResults (dmap sps f) = inr sps'
    -> aggrClosureResults (dmap sps f') = inr sps''
    -> (forall sp (hi : In sp sps) sps' sps'' , f sp hi = inr sps' -> f' sp hi = inr sps'' -> sps' = sps'')
    -> sps' = sps''.
Proof.
  intros sps; induction sps as [| sp sps IH]; intros f f' sps' sps'' ha ha' hall.
  - sis.
    inv ha; inv ha'; auto.
  - simpl in ha; simpl in ha'.
    dmeq hh; tc.
    dmeq ht; tc.
    dmeq hh'; tc.
    dmeq ht'; tc.
    inv ha; inv ha'.
    unfold eq_ind_r in *; sis.
    unfold eq_rect_r in *; sis.
    assert (l1 = l).
    { eapply hall; eauto. }
    subst.
    assert (l2 = l0).
    { eapply IH in ht; eauto.
      intros sp' hi sps' sps'' heq heq'.
      sis.
      eapply hall; eauto. }
    subst. auto.
Qed.
      
Lemma spClosure_proof_irrel' :
  forall g (pr : nat * nat) (a : Acc lex_nat_pair pr) pr' (a' : Acc lex_nat_pair pr') sp sps sps' (a : Acc lex_nat_pair (meas g sp)) (a' : Acc lex_nat_pair (meas g sp)),
    pr = meas g sp
    -> pr' = meas g sp
    -> spClosure g sp a = inr sps
    -> spClosure g sp a' = inr sps'
    -> sps = sps'.
Proof.
  intros g pr a.
  induction a as [pr hlt IH]; intros pr' ha' sp sps sps' a'' a''' ? ? hs hs'; subst.
  rename a'' into a; rename a''' into a'.
  apply spClosure_success_cases in hs.
  apply spClosure_success_cases in hs'.
  destruct hs; destruct hs'; tc.
  - destruct H as [? heq]; destruct H0 as [? heq']; subst; auto.
  - destruct H as [? heq]; subst.
    destruct H0 as [sps'' [hs [crs [heq ha]]]]; subst; tc.
  - destruct H0 as [? heq]; subst.
    destruct H as [sps'' [hs [crs [heq ha]]]]; subst; tc.
  - destruct H as [sps'' [hs [crs [heq ha]]]];
    destruct H0 as [sps''' [hs' [crs' [heq' ha'']]]]; subst.
    assert (heq : sps'' = sps''').
    { clear ha''; rewrite hs in hs'; inv hs'; auto. }
    subst.
    eapply aggrClosureResults_succ_eq; eauto.
    intros s h xs ys heq heq'; sis.
    specialize IH with (y := meas g s)
                       (pr' := meas g s)
                       (sp := s)
                       (sps := xs)
                       (sps' := ys).
    eapply IH; eauto.
    + eapply spClosureStep_meas_lt; eauto.
    + apply lex_nat_pair_wf.
Qed.

Lemma spClosure_proof_irrel :
  forall g sp (a a' : Acc lex_nat_pair (meas g sp))
         (sps sps' : list subparser),
    spClosure g sp a = inr sps
    -> spClosure g sp a' = inr sps'
    -> sps = sps'.
Proof.
  intros; eapply spClosure_proof_irrel'; eauto.
Qed.

Lemma aggrClosureResults_dmap' :
  forall g sp sp' sps' sps''' (hs : spClosureStep g sp = SpClosureStepK sps'),
    In sp' sps'
    -> aggrClosureResults
         (dmap sps'
               (fun sp' hi =>
                  spClosure g sp'
                            (acc_after_step g sp sp' hs hi
                                            (lex_nat_pair_wf (meas g sp))))) = inr sps'''
    -> exists sps'' a,
        spClosure g sp' a = inr sps''
        /\ forall sp'', In sp'' sps'' -> In sp'' sps'''.
Proof.
  intros g sp sp' sps' sps''' hs hi ha.
  eapply aggrClosureResults_dmap_succ_elt_succ in ha; eauto.
  destruct ha as [hi' [sps'' [heq hall]]]; eauto.
Qed.