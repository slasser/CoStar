Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser_sound.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Require Import GallStar.LLPrediction_error_free.
Import ListNotations.

Module ParserErrorFreeFn (Import D : Defs.T).

  Module Export PS := ParserSoundFn D.

  (* The following three groups of lemmas correspond to the three
   types of parser errors: errors indicating an invalid parser
   state, errors that indicate a left-recursive grammar, and 
   errors that arise during prediction *)

  (* The parser never reaches an invalid state;
   i.e., impossible states really are impossible *)

  Lemma stacks_wf__step_neq_invalid_state :
    forall (g     : grammar)
           (cm    : closure_map)
           (ps    : prefix_stack)
           (ss    : suffix_stack)
           (ts    : list token)
           (av    : NtSet.t)
           (un    : bool)
           (ca    : cache),
      stacks_wf g ps ss
      -> step g cm ps ss ts av un ca <> StepError InvalidState.
  Proof.
    intros g cm ps ss ts av un ca hw; unfold not; intros hs. 
    unfold step in hs; dms; tc; try inv hw.
  Qed.

  Lemma multistep_never_reaches_error_state :
    forall (g    : grammar)
           (cm   : closure_map)
           (tri  : nat * nat * nat)
           (ha   : Acc lex_nat_triple tri)
           (ps   : prefix_stack)
           (ss   : suffix_stack)
           (ts   : list token)
           (av   : NtSet.t)
           (un   : bool)
           (ca   : cache)
           (hc   : cache_stores_target_results g cm ca)
           (ha'  : Acc lex_nat_triple (meas g ss ts av)),
      tri = meas g ss ts av
      -> stacks_wf g ps ss
      -> multistep g cm ps ss ts av un ca hc ha' <> Error InvalidState.
  Proof.
    intros g cm tri ha'.
    induction ha' as [tri hlt IH].
    intros ps ss ts av un ca hc ha? hw hm; subst. 
    apply multistep_invalid_state_cases in hm.
    destruct hm as [hs | hm].
    - eapply stacks_wf__step_neq_invalid_state; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & un' & ca' & hc' & ha' & hs & hm).
      eapply IH in hm; eauto.
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto.
  Qed.

  Lemma parse_never_reaches_invalid_state :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token),
      parse g x ts <> Error InvalidState.
  Proof.
    intros g x ts hp; unfold parse in hp.
    eapply multistep_never_reaches_error_state in hp; eauto.
    - apply lex_nat_triple_wf.
    - constructor.
  Qed.

  (* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)
  Lemma unavailable_nts_invar_starts_true :
    forall g x,
      unavailable_nts_are_open_calls g (allNts g) (SF None [x], []). 
  Proof.
    intros g x; intros x' hi hni; ND.fsetdec.
  Qed.

  (* to do : There is some redundancy here with proofs about
   unavailable_nts_invar in Prediction. Those proofs should
   be defined in terms of unavailable_nts_are_open_calls *)

  Lemma return_preserves_unavailable_nts_invar :
    forall g s_ce s_cr s_cr' s_frs o o' x suf av,
      s_ce     = SF o' []
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> unavailable_nts_are_open_calls g av (s_ce, s_cr :: s_frs)
      -> unavailable_nts_are_open_calls g (NtSet.add x av) (s_cr', s_frs).
  Proof.
    intros; subst.
    pose proof return_preserves_unavailable_nts_invar as hr; sis.
    eapply hr; eauto.
  Qed.

  Lemma push_preserves_unavailable_nts_invar :
    forall g s_cr s_ce s_frs av o x suf rhs,
      s_cr = SF o (NT x :: suf)
      -> s_ce = SF (Some x) rhs
      -> In (x, rhs) g
      -> unavailable_nts_are_open_calls g av (s_cr, s_frs)
      -> unavailable_nts_are_open_calls g (NtSet.remove x av) (s_ce, s_cr :: s_frs).
  Proof.
    intros; subst.
    pose proof push_preserves_unavailable_nts_invar as hp; sis.
    eapply hp; eauto.
  Qed.  

  Lemma step_preserves_unavailable_nts_invar :
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca',
      cache_stores_target_results g cm ca
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> unavailable_nts_are_open_calls g av  ss
      -> unavailable_nts_are_open_calls g av' ss'.
  Proof.
    intros g cm ps ps' ss ss' ts ts' av av' un un' ca ca' hc hs hu.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_unavailable_nts_invar; eauto. 
    - intros x hi hn; ND.fsetdec. 
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_succ_in_grammar; eauto.
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_ambig_in_grammar; eauto.
  Qed.

  Lemma step_left_recursion_detection_sound :
    forall g cm ps ss ts av un ca x,
      unavailable_nts_are_open_calls g av ss
      -> step g cm ps ss ts av un ca = StepError (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g cm ps ss ts av un ca x hu hs.
    apply step_LeftRecursion_facts in hs.
    destruct hs as (hni & hi & o & suf & frs & ?); subst.
    apply hu in hni; auto.
    destruct hni as (frs_pre & cr & frs_suf & o' & suf' & ? & ? & hf); subst.
    eapply frnp_grammar_nullable_path; eauto.
  Qed.

  Lemma multistep_left_recursion_detection_sound :
    forall (g      : grammar)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (ha     : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (ha'    : Acc lex_nat_triple (meas g ss ts av))
           (x      : nonterminal),
      tri = meas g ss ts av
      -> unavailable_nts_are_open_calls g av ss
      -> multistep g cm ps ss ts av un ca hc ha' = Error (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g cm tri ha'; induction ha' as [tri hlt IH].
    intros ps ss ts av un ca hc ha x ? hu hm; subst.
    apply multistep_left_recursion_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_left_recursion_detection_sound; eauto. 
    - destruct hm as (ps' & ss' & ts' & av' & un' & ca' & hc' & ha' & hs & hm).
      eapply IH with (y := meas g ss' ts' av'); eauto.
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_unavailable_nts_invar with (ca := ca); eauto.
  Qed.

  Lemma parse_left_recursion_detection_sound :
    forall g x y ts,
      parse g x ts = Error (LeftRecursion y)
      -> left_recursive g (NT y).
  Proof.
    intros g x y ts hp; unfold parse in hp.
    eapply multistep_left_recursion_detection_sound in hp; eauto.
    - apply lex_nat_triple_wf.
    - intros x' hi hn; ND.fsetdec.
  Qed.
  
  Lemma parse_doesn't_find_left_recursion_in_non_left_recursive_grammar :
    forall (g   : grammar)
           (x y : nonterminal)
           (ts  : list token),
      no_left_recursion g
      -> parse g x ts <> Error (LeftRecursion y).
  Proof.
    intros g x y ts hn hp.
    apply parse_left_recursion_detection_sound in hp; firstorder.
  Qed.

  (* Errors never arise during prediction, given a non-left-recursive grammar *)

  Lemma step_never_returns_prediction_error :
    forall g cm ps ss ts av un ca e,
      no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> stacks_wf g ps ss
      -> step g cm ps ss ts av un ca <> StepError (PredictionError e).
  Proof.
    intros g cm ps ss ts av un ca e hn hm hc hw hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply adaptivePredict_neq_error; eauto.
    eapply frames_wf__suffix_frames_wf; eauto.
  Qed.

  (*
  Lemma step_never_returns_SpInvalidState :
    forall g cm ps ss ts av un ca,
      stacks_wf g ps ss
      -> step g cm ps ss ts av un ca <> StepError (PredictionError SpInvalidState).
  Proof.
    intros g cm ps ss ts av un ca hw hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply adaptivePredict_neq_error; eauto.
    - 
    eapply llPredict_never_returns_SpInvalidState; eauto.
    eapply frames_wf__suffix_frames_wf; eauto.
  Qed.

  Lemma step_never_returns_SpLeftRecursion :
    forall g p_stk s_stk ts av u x,
      no_left_recursion g
      -> stacks_wf g p_stk s_stk
      -> step g p_stk s_stk ts av u <> StepError (PredictionError (SpLeftRecursion x)).
  Proof.
    intros g ps ss ts av un x hn hw; unfold not; intros hs. 
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply llPredict_never_returns_SpLeftRecursion; eauto.
  Qed.
   *)
  
  Lemma multistep_never_returns_prediction_error :
    forall (g      : grammar)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a'     : Acc lex_nat_triple (meas g ss ts av))
           (e      : prediction_error),
      no_left_recursion g
      -> closure_map_correct g cm 
      -> tri = meas g ss ts av
      -> stacks_wf g ps ss
      -> multistep g cm ps ss ts av un ca hc a' <> Error (PredictionError e).
  Proof.
    intros g cm tri a.
    induction a as [tri hlt IH].
    intros ps ss ts av un ca hc a' e hn hcm ? hw hm; subst.
    apply multistep_prediction_error_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_never_returns_prediction_error in hs; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & un' & ca' & hc' & a'' & hs & hm). 
      eapply IH in hm; eauto.
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto.
  Qed.

  Lemma parse_never_returns_prediction_error :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (e  : prediction_error),
      no_left_recursion g
      -> parse g x ts <> Error (PredictionError e).
  Proof.
    intros g x ts e hn hp; unfold parse in hp.
    eapply multistep_never_returns_prediction_error in hp; eauto.
    - apply lex_nat_triple_wf.
    - apply mkClosureMap_result_correct.
    - constructor.
  Qed.

  Theorem parse_terminates_without_error :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (e  : parse_error),
      no_left_recursion g
      -> parse g x ts <> Error e.
  Proof.
    intros g x ts e hn hp; destruct e.
    - (* invalid state case *)
      eapply parse_never_reaches_invalid_state; eauto.
    - (* left recursion case *)
      eapply parse_doesn't_find_left_recursion_in_non_left_recursive_grammar; eauto.
    - (* prediction error case *)
      eapply parse_never_returns_prediction_error; eauto.
  Qed.

End ParserErrorFreeFn.
