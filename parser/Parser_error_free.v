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
           (pm    : production_map)
           (cm    : closure_map)
           (ps    : prefix_stack)
           (ss    : suffix_stack)
           (ts    : list token)
           (vi    : NtSet.t)
           (un    : bool)
           (ca    : cache)
           (hc    : cache_stores_target_results pm cm ca)
           (hk    : stack_pushes_from_keyset pm ss),
      stacks_wf g ps ss
      -> step pm cm ps ss ts vi un ca hc hk <> StepError InvalidState.
  Proof.
    intros g pm cm ps ss ts vi un ca hc hk hw; unfold not; intros hs. 
    unfold step in hs; dms; tc; try inv hw.
  Qed.

  Lemma multistep_never_reaches_error_state :
    forall (g    : grammar)
           (pm   : production_map)
           (cm   : closure_map)
           (tri  : nat * nat * nat)
           (ha   : Acc lex_nat_triple tri)
           (ps   : prefix_stack)
           (ss   : suffix_stack)
           (ts   : list token)
           (vi   : NtSet.t)
           (un   : bool)
           (ca   : cache)
           (hc   : cache_stores_target_results pm cm ca)
           (hk   : stack_pushes_from_keyset pm ss)
           (ha'  : Acc lex_nat_triple (meas pm ss ts vi)),
      tri = meas pm ss ts vi
      -> production_map_correct pm g
      -> stacks_wf g ps ss
      -> multistep pm cm ps ss ts vi un ca hc hk ha' <> Error InvalidState.
  Proof.
    intros g pm cm tri ha'.
    induction ha' as [tri hlt IH].
    intros ps ss ts vi un ca hc hk ha ? hp hw hm; subst. 
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply stacks_wf__step_neq_invalid_state; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & un' & ca' & hc' & hk' & ha' & hs & hm).
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
    - eapply mkProductionMap_correct.
    - constructor.
  Qed.

  (* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)
  Lemma unavailable_nts_invar_starts_true :
    forall g x,
      unavailable_nts_are_open_calls g NtSet.empty (SF None [x], []). 
  Proof.
    intros g x; intros x' hi hni; ND.fsetdec.
  Qed.

  (* to do : There is some redundancy here with proofs about
   unavailable_nts_invar in Prediction. Those proofs should
   be defined in terms of unavailable_nts_are_open_calls *)

  Lemma return_preserves_unavailable_nts_invar :
    forall g s_ce s_cr s_cr' s_frs o o' x suf vi,
      s_ce     = SF o' []
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> unavailable_nts_are_open_calls g vi (s_ce, s_cr :: s_frs)
      -> unavailable_nts_are_open_calls g (NtSet.remove x vi) (s_cr', s_frs).
  Proof.
    intros; subst.
    pose proof return_preserves_unavailable_nts_invar as hr; sis.
    eapply hr; eauto.
  Qed.

  Lemma push_preserves_unavailable_nts_invar :
    forall g s_cr s_ce s_frs vi o x suf rhs,
      s_cr = SF o (NT x :: suf)
      -> s_ce = SF (Some x) rhs
      -> In (x, rhs) g
      -> unavailable_nts_are_open_calls g vi (s_cr, s_frs)
      -> unavailable_nts_are_open_calls g (NtSet.add x vi) (s_ce, s_cr :: s_frs).
  Proof.
    intros; subst.
    pose proof push_preserves_unavailable_nts_invar as hp; sis.
    eapply hp; eauto.
  Qed.  

  Lemma step_preserves_unavailable_nts_invar :
    forall g pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk,
      production_map_correct pm g
      -> step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> unavailable_nts_are_open_calls g vi  ss
      -> unavailable_nts_are_open_calls g vi' ss'.
  Proof.
    intros g pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk hp hs hu.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_unavailable_nts_invar; eauto. 
    - intros x hi hn; ND.fsetdec. 
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_succ_in_grammar; eauto.
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_ambig_in_grammar; eauto.
  Qed.

  Lemma step_left_recursion_detection_sound :
    forall g pm cm ps ss ts vi un ca hc hk x,
      production_map_correct pm g
      -> unavailable_nts_are_open_calls g vi ss
      -> step pm cm ps ss ts vi un ca hc hk = StepError (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g pm cm ps ss ts vi un ca hc hk x hp hu hs.
    apply step_LeftRecursion_facts in hs.
    destruct hs as [hi [[yss hf] [o [suf [frs heq]]]]]; subst.
    apply hu in hi; auto.
    - destruct hi as (frs_pre & cr & frs_suf & o' & suf' & ? & ? & hf'); subst.
      eapply frnp_grammar_nullable_path; eauto.
    - eapply find_allNts; eauto.
  Qed.

  Lemma multistep_left_recursion_detection_sound :
    forall (g      : grammar)
           (pm     : production_map)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (ha     : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results pm cm ca)
           (hk     : stack_pushes_from_keyset pm ss)
           (ha'    : Acc lex_nat_triple (meas pm ss ts vi))
           (x      : nonterminal),
      tri = meas pm ss ts vi
      -> production_map_correct pm g
      -> unavailable_nts_are_open_calls g vi ss
      -> multistep pm cm ps ss ts vi un ca hc hk ha' = Error (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g pm cm tri ha'; induction ha' as [tri hlt IH].
    intros ps ss ts vi un ca hc hk ha x ? hp hu hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_left_recursion_detection_sound; eauto. 
    - destruct hm as (ps' & ss' & ts' & vi' & un' & ca' & hc' & hk' & ha' & hs & hm).
      eapply IH with (y := meas pm ss' ts' vi'); eauto.
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
    - apply mkProductionMap_correct.
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
    forall g pm cm ps ss ts vi un ca hc hk e,
      no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> step pm cm ps ss ts vi un ca hc hk <> StepError (PredictionError e).
  Proof.
    intros g pm cm ps ss ts vi un ca hc hk e hn hp hm hw hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply adaptivePredict_neq_error; eauto.
    eapply frames_wf__suffix_frames_wf; eauto.
  Qed.
  
  Lemma multistep_never_returns_prediction_error :
    forall (g      : grammar)
           (pm     : production_map)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results pm cm ca)
           (hk     : stack_pushes_from_keyset pm ss)
           (a'     : Acc lex_nat_triple (meas pm ss ts vi))
           (e      : prediction_error),
      no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm 
      -> tri = meas pm ss ts vi
      -> stacks_wf g ps ss
      -> multistep pm cm ps ss ts vi un ca hc hk a' <> Error (PredictionError e).
  Proof.
    intros g pm cm tri a.
    induction a as [tri hlt IH].
    intros ps ss ts vi un ca hc hk a' e hn hp hcm ? hw hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_never_returns_prediction_error in hs; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & un' & ca' & hc' & hk' & a'' & hs & hm). 
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
    - apply mkProductionMap_correct.
    - apply mkClosureMap_result_correct.
    - constructor.
  Qed.

End ParserErrorFreeFn.
