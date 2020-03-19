Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Parser.
Require Import GallStar.Parser_sound.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Require Import GallStar.Prediction_error_free.
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
           (p_stk : prefix_stack)
           (s_stk : suffix_stack)
           (ts    : list token)
           (av    : NtSet.t)
           (u     : bool),
      stacks_wf g p_stk s_stk
      -> step g p_stk s_stk ts av u <> StepError InvalidState.
  Proof.
    intros g pstk sstk ts av u hw; unfold not; intros hs. 
    unfold step in hs; dms; tc; try inv hw.
  Qed.

  Lemma multistep_never_reaches_error_state :
    forall (g      : grammar)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (u      : bool)
           (a'     : Acc lex_nat_triple (meas g s_stk ts av)),
      tri = meas g s_stk ts av
      -> stacks_wf g p_stk s_stk
      -> multistep g p_stk s_stk ts av u a' <> Error InvalidState.
  Proof.
    intros g tri a.
    induction a as [tri hlt IH].
    intros pstk sstk ts av u a' ? hw; unfold not in *; intros hm; subst.
    apply multistep_invalid_state_cases in hm.
    destruct hm as [hs | hm].
    - eapply stacks_wf__step_neq_invalid_state; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & u' & a'' & hs & hm).
      eapply IH in hm; eauto.
      + eapply step_meas_lt; eauto.
      + eapply step_preserves_stacks_wf_invar; eauto.
  Qed.

  Lemma parser_never_reaches_invalid_state :
    forall (g  : grammar)
           (ss : list symbol)
           (ts : list token),
      parse g ss ts <> Error InvalidState.
  Proof.
    intros g ss ts; unfold not; intros hp.
    unfold parse in hp.
    eapply multistep_never_reaches_error_state in hp; eauto.
    - apply lex_nat_triple_wf.
    - constructor.
  Qed.

  (* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)
  Lemma unavailable_nts_invar_starts_true :
    forall g ys,
      unavailable_nts_are_open_calls g (allNts g) (SF None ys, []). 
  Proof.
    intros g ys; intros x hi hni; ND.fsetdec.
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
    forall g p_stk p_stk' s_stk s_stk' ts ts' av av' u u',
      step g p_stk s_stk ts av u = StepK p_stk' s_stk' ts' av' u'
      -> unavailable_nts_are_open_calls g av s_stk
      -> unavailable_nts_are_open_calls g av' s_stk'.
  Proof.
    intros g ps ps' ss ss' ts ts' av av' u u' hs hu.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_unavailable_nts_invar; eauto. 
    - intros x hi hn; ND.fsetdec. 
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply llPredict_succ_in_grammar; eauto.
    - eapply push_preserves_unavailable_nts_invar; eauto.
      eapply llPredict_ambig_in_grammar; eauto.
  Qed.

  Lemma step_left_recursion_detection_sound :
    forall g p_stk s_stk ts av u x,
      unavailable_nts_are_open_calls g av s_stk
      -> step g p_stk s_stk ts av u = StepError (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g p_stk s_stk ts av u x hu hs.
    apply step_LeftRecursion_facts in hs.
    destruct hs as (hni & hi & o & suf & frs & ?); subst.
    apply hu in hni; auto.
    destruct hni as (frs_pre & cr & frs_suf & o' & suf' & ? & ? & hf); subst.
    eapply frnp_grammar_nullable_path; eauto.
  Qed.

  Lemma multistep_left_recursion_detection_sound :
    forall (g      : grammar)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (u      : bool)
           (a'     : Acc lex_nat_triple (meas g s_stk ts av))
           (x      : nonterminal),
      tri = meas g s_stk ts av
      -> unavailable_nts_are_open_calls g av s_stk
      -> multistep g p_stk s_stk ts av u a' = Error (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g tri a.
    induction a as [tri hlt IH].
    intros pstk sstk ts av u a' x ? hu hm; subst.
    apply multistep_left_recursion_cases in hm.
    destruct hm as [hs | hm].
    - eapply step_left_recursion_detection_sound; eauto. 
    - destruct hm as (ps' & ss' & ts' & av' & u' & a'' & hs & hm).
      eapply IH with (y := meas g ss' ts' av'); eauto.
      + eapply step_meas_lt; eauto.
      + eapply step_preserves_unavailable_nts_invar; eauto.
  Qed.

  Lemma parse_left_recursion_detection_sound :
    forall g ss ts x,
      parse g ss ts = Error (LeftRecursion x)
      -> left_recursive g (NT x).
  Proof.
    intros g ss ts x hp; unfold parse in hp.
    eapply multistep_left_recursion_detection_sound in hp; eauto.
    - apply lex_nat_triple_wf.
    - intros x' hi hn; ND.fsetdec.
  Qed.
  
  Lemma parser_doesn't_find_left_recursion_in_non_left_recursive_grammar :
    forall (g  : grammar)
           (ss : list symbol)
           (ts : list token)
           (x  : nonterminal),
      no_left_recursion g
      -> parse g ss ts <> Error (LeftRecursion x).
  Proof.
    intros g ss ts x hn; unfold not; intros hp.
    apply parse_left_recursion_detection_sound in hp; firstorder.
  Qed.

  (* Errors never arise during prediction, given a non-left-recursive grammar *)

  Lemma step_never_returns_SpInvalidState :
    forall g p_stk s_stk ts av u,
      stacks_wf g p_stk s_stk
      -> step g p_stk s_stk ts av u <> StepError (PredictionError SpInvalidState).
  Proof.
    intros g ps ss ts av un hw; unfold not; intros hs. 
    unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
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

  Lemma multistep_never_returns_prediction_error :
    forall (g      : grammar)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (u      : bool)
           (a'     : Acc lex_nat_triple (meas g s_stk ts av))
           (e      : prediction_error),
      no_left_recursion g
      -> tri = meas g s_stk ts av
      -> stacks_wf g p_stk s_stk
      -> multistep g p_stk s_stk ts av u a' <> Error (PredictionError e).
  Proof.
    intros g tri a.
    induction a as [tri hlt IH].
    intros ps ss ts av un a' e hn ? hw; unfold not; intros hm; subst. 
    apply multistep_prediction_error_cases in hm.
    destruct hm as [hs | hm].
    - destruct e as [ | x].
      + (* InvalidState case *)
        eapply step_never_returns_SpInvalidState in hs; eauto.
      + (* LeftRecursion case *)
        eapply step_never_returns_SpLeftRecursion in hs; eauto.
    - destruct hm as (ps' & ss' & ts' & av' & un' & a'' & hs & hm). 
      eapply IH in hm; eauto.
      + eapply step_meas_lt; eauto.
      + eapply step_preserves_stacks_wf_invar; eauto.
  Qed.

  Lemma parse_never_returns_prediction_error :
    forall (g : grammar)
           (ys : list symbol)
           (ts : list token)
           (e  : prediction_error),
      no_left_recursion g
      -> parse g ys ts <> Error (PredictionError e).
  Proof.
    intros g ys ts e hn; unfold not; intros hp.
    unfold parse in hp.
    eapply multistep_never_returns_prediction_error in hp; eauto.
    - apply lex_nat_triple_wf.
    - constructor.
  Qed.

  Theorem parser_terminates_without_error :
    forall (g  : grammar)
           (ys : list symbol)
           (ts : list token)
           (e  : parse_error),
      no_left_recursion g
      -> parse g ys ts <> Error e.
  Proof.
    intros g ys ts e; unfold not; intros hp; destruct e.
    - (* invalid state case *)
      eapply parser_never_reaches_invalid_state; eauto.
    - (* left recursion case *)
      apply parser_doesn't_find_left_recursion_in_non_left_recursive_grammar; auto.
    - (* prediction error case *)
      apply parse_never_returns_prediction_error; auto.
  Qed.

End ParserErrorFreeFn.
