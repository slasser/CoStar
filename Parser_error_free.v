Require Import List.
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.Parser_sound.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Require Import CoStar.LLPrediction_error_free.
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
    forall (gr    : grammar)
           (hw    : grammar_wf gr)
           (rm    : rhs_map)
           (cm    : closure_map)
           (sk    : parser_stack)
           (ts    : list token)
           (vi    : NtSet.t)
           (un    : bool)
           (ca    : cache)
           (hc    : cache_stores_target_results rm cm ca)
           (hk    : stack_pushes_from_keyset rm sk),
      stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk <> StepError InvalidState.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk hw'; unfold not; intros hs. 
    unfold step in hs; dmeqs H; tc; rew_anr; inv hw'; rew_anr.
    eapply fpaa_none_contra; eauto.
  Qed.

  Lemma multistep_never_reaches_error_state :
    forall (gr   : grammar)
           (hw   : grammar_wf gr) 
           (rm   : rhs_map)
           (hr   : rhs_map_correct rm gr)
           (cm   : closure_map)
           (x    : nonterminal)
           (tri  : nat * nat * nat)
           (ha   : Acc lex_nat_triple tri)
           (sk   : parser_stack)
           (ts   : list token)
           (vi   : NtSet.t)
           (un   : bool)
           (ca   : cache)
           (hc   : cache_stores_target_results rm cm ca)
           (hk   : stack_pushes_from_keyset rm sk)
           (hb   : bottom_stack_sym_eq_start_sym sk x)
           (ha'  : Acc lex_nat_triple (parser_meas rm sk ts vi)),
      tri = parser_meas rm sk ts vi
      -> stack_wf gr sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha' <> Error _ InvalidState.
  Proof.
    intros gr hw rm hr cm x tri ha'.
    induction ha' as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha ? hw' hm; subst. 
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply stacks_wf__step_neq_invalid_state; eauto.
    - destruct hm as (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & ha' & hs & hm).
      eapply IH in hm; eauto.
      + eapply step_parser_meas_lt; eauto.  
      + eapply step_preserves_stack_wf_invar; eauto.
  Qed.

  Lemma parse_never_reaches_invalid_state :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ts  : list token),
      parse gr hw x ts <> Error _ InvalidState.
  Proof.
    intros g hw x ts hp; unfold parse in hp.
    eapply multistep_never_reaches_error_state in hp; eauto.
    - apply lex_nat_triple_wf.
    - constructor.
  Qed.

  (* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)
  Lemma unavailable_nts_invar_starts_true :
    forall g x,
      unavailable_nts_are_open_calls g NtSet.empty (Fr [] tt [NT x], []). 
  Proof.
    intros g x; intros x' hi hni; ND.fsetdec.
  Qed.

  Lemma step_preserves_unavailable_nts_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> unavailable_nts_are_open_calls gr vi  sk
      -> unavailable_nts_are_open_calls gr vi' sk'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hr hs hu.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_unavailable_nts_invar; eauto. 
    - intros x hi hn; ND.fsetdec. 
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_succ_in_grammar; eauto.
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply adaptivePredict_ambig_in_grammar; eauto.
      Unshelve.
      all : auto.
  Qed.

  Lemma step_left_recursion_detection_sound :
    forall gr hw rm cm sk ts vi un ca hc hk x,
      rhs_map_correct rm gr
      -> unavailable_nts_are_open_calls gr vi sk
      -> step gr hw rm cm sk ts vi un ca hc hk = StepError (LeftRecursion x)
      -> left_recursive gr (NT x).
  Proof.
    intros g hw rm cm sk ts vi un ca hc hk x hp hu hs.
    apply step_LeftRecursion_facts in hs.
    destruct hs as [hi [[yss hf] [pre [vs [suf [frs heq]]]]]]; subst.
    apply hu in hi; auto.
    - destruct hi as (frs_pre & cr & frs_suf & pre' & vs' & suf' & ? & ? & hf'); subst.
      eapply frnp_grammar_nullable_path; eauto.
    - eapply find_allNts; eauto.
  Qed.

  Lemma multistep_left_recursion_detection_sound :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (ha     : Acc lex_nat_triple tri)
           (sk     : parser_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (ha'    : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (y      : nonterminal),
      tri = parser_meas rm sk ts vi
      -> unavailable_nts_are_open_calls gr vi sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha' = Error _ (LeftRecursion y)
      -> left_recursive gr (NT y).
  Proof.
    intros gr hw rm hr cm x tri ha'; induction ha' as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha y ? hu hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_left_recursion_detection_sound; eauto. 
    - destruct hm as (sk' & ts' & vi' & un' & ca' & hc' & hk' & hb' & ha' & hs & hm).
      eapply IH with (y := parser_meas rm sk' ts' vi'); eauto.
      + eapply step_parser_meas_lt; eauto. 
      + eapply step_preserves_unavailable_nts_invar; eauto. 
  Qed.

  Lemma parse_left_recursion_detection_sound :
    forall gr hw x y ts,
      parse gr hw x ts = Error _ (LeftRecursion y)
      -> left_recursive gr (NT y).
  Proof.
    intros g hw x y ts hp; unfold parse in hp.
    eapply multistep_left_recursion_detection_sound in hp; eauto.
    - apply lex_nat_triple_wf.
    - intros x' hi hn; ND.fsetdec.
  Qed.
  
  Lemma parse_doesn't_find_left_recursion_in_non_left_recursive_grammar :
    forall (g   : grammar)
           (hw  : grammar_wf g)
           (x y : nonterminal)
           (ts  : list token),
      no_left_recursion g
      -> parse g hw x ts <> Error _ (LeftRecursion y).
  Proof.
    intros g hw x y ts hn hp.
    apply parse_left_recursion_detection_sound in hp; firstorder.
  Qed.

  (* Errors never arise during prediction, given a non-left-recursive grammar *)

  Lemma step_never_returns_prediction_error :
    forall gr hw rm cm sk ts vi un ca hc hk e,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> step gr hw rm cm sk ts vi un ca hc hk <> StepError (PredictionError e).
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk e hn hp hm hw' hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
    eapply adaptivePredict_neq_error; eauto.
  Qed.
  
  Lemma multistep_never_returns_prediction_error :
    forall (gr     : grammar)
           (hw     : grammar_wf gr)
           (rm     : rhs_map)
           (hr     : rhs_map_correct rm gr)
           (cm     : closure_map)
           (x      : nonterminal)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (sk     : parser_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results rm cm ca)
           (hk     : stack_pushes_from_keyset rm sk)
           (hb     : bottom_stack_sym_eq_start_sym sk x)
           (a'     : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (e      : prediction_error),
      no_left_recursion gr
      -> closure_map_correct gr cm 
      -> tri = parser_meas rm sk ts vi
      -> stack_wf gr sk
      -> multistep gr hw rm hr cm x sk ts vi un ca hc hk hb a' <> Error _ (PredictionError e).
  Proof.
    intros gr hw rm hr cm x tri ha.
    induction ha as [tri hlt IH].
    intros sk ts vi un ca hc hk hb ha' e hn hcm ? hw' hm; subst.
    apply multistep_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_never_returns_prediction_error in hs; eauto.
    - destruct hm as (sk' & ts' & av' & un' & ca' & hc' & hk' & hb' & a'' & hs & hm). 
      eapply IH in hm; eauto.
      + eapply step_parser_meas_lt; eauto. 
      + eapply step_preserves_stack_wf_invar; eauto. 
  Qed.

  Lemma parse_never_returns_prediction_error :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ts  : list token)
           (e   : prediction_error),
      no_left_recursion gr
      -> parse gr hw x ts <> Error _ (PredictionError e).
  Proof.
    intros g hw x ts e hn hp; unfold parse in hp.
    eapply multistep_never_returns_prediction_error in hp; eauto.
    - apply lex_nat_triple_wf.
    - apply mkClosureMap_correct.
    - constructor.
  Qed.

End ParserErrorFreeFn.
