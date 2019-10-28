Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Require Import GallStar.Prediction_error_free_termination.
Import ListNotations.

(* The parser never reaches an invalid state;
   i.e., impossible states really are impossible *)

Lemma stack_wf_no_invalid_state :
  forall (g : grammar)
         (av : NtSet.t)
         (stk : parser_stack)
         (ts : list token),
    stack_wf g stk
    -> ~ step g (Pst av stk ts) = StepError InvalidState.
Proof.
  intros g av stk ts hwf; unfold not; intros hs.
  unfold step in hs.
  dms; tc; try inv hwf.
Qed.

Lemma multistep_never_reaches_error_state :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (ts     : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk ts))),
    tri = meas g (Pst av stk ts)
    -> stack_wf g stk
    -> ~ multistep g (Pst av stk ts) a' = Error InvalidState.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros ts av stk a' heq hwf; unfold not; intros hm; subst.
  apply multistep_invalid_state_cases in hm.
  destruct hm as [hs | hm].
  - eapply stack_wf_no_invalid_state; eauto. 
  - destruct hm as [[av' stk' ts'] [a'' [hs hm]]].
    eapply IH in hm; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
Qed.

Lemma parser_never_reaches_invalid_state :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token),
    ~ parse g ss ts = Error InvalidState.
Proof.
  intros g ss ts; unfold not; intros hp.
  unfold parse in hp.
  apply multistep_never_reaches_error_state
    with (tri := Parser.meas g (mkInitState g ss ts)) in hp; auto.
  - apply lex_nat_triple_wf.
  - constructor.
Qed.

(* CLEAN UP *)
Lemma multistep_left_recursion_detection_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (st     : parser_state)
         (a'     : Acc lex_nat_triple (meas g st))
         (x      : nonterminal),
    tri = meas g st
    -> stack_wf g st.(stack)
    -> unavailable_nts_invar g st
    -> multistep g st a' = Error (LeftRecursion x)
    -> left_recursive g (NT x).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros st a' x heq hw hu hm; subst.
  apply multistep_left_recursion_cases in hm.
  destruct hm as [hs | [st' [a'' [hs hm]]]].
  - clear IH.
    destruct st as [av (fr, frs) ts].
    apply step_LeftRecursion_facts in hs.
    destruct hs as [hnin [hin [suf heq]]]; subst.
    unfold unavailable_nts_invar in hu.
    apply hu in hnin; auto.
    destruct hnin as [hng [frs_pre [fr_cr [frs_suf [suf_cr [heq' [hp heq'']]]]]]]; subst.
    simpl in hw. unfold frames_wf in hw; simpl in hw.
    rewrite heq' in hw.
    assert (happ : loc fr :: frs_pre ++ fr_cr :: frs_suf =
                   (loc fr :: frs_pre ++ [fr_cr]) ++ frs_suf).
    (* lemma *)
    { simpl. rewrite <- app_assoc. simpl. auto. }
    rewrite happ in hw; clear happ.
    apply Prediction.locations_wf_app_l in hw.
    eapply Prediction_error_free_termination.stack_configuration_repr_nullable_path in hw; eauto.
  - eapply IH with (y := meas g st'); eauto.
    + eapply step_meas_lt; eauto.
    + (* redefine invariants to get rid of these destructs *)
      destruct st; destruct st'.
      eapply step_preserves_stack_wf_invar; eauto.
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
  - (* lemma? *)
    constructor.
  - (* lemma *)
    unfold mkInitState.
    unfold unavailable_nts_invar; simpl.
    intros; ND.fsetdec.
Qed.
  
Lemma parser_doesn't_find_left_recursion_in_non_left_recursive_grammar :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token)
         (x  : nonterminal),
    no_left_recursion g
    -> ~ parse g ss ts = Error (LeftRecursion x).
Proof.
  intros g ss ts x hn; unfold not; intros hp.
  apply parse_left_recursion_detection_sound in hp; firstorder.
Qed.

Lemma parse_never_returns_prediction_error :
  forall (g : grammar)
         (ss : list symbol)
         (ts : list token)
         (e  : prediction_error),
    no_left_recursion g
    -> ~ parse g ss ts = Error (PredictionError e).
Proof.
  intros g ss ts e hn; unfold not; intros hp.
  unfold parse in hp.
  apply multistep_never_returns_prediction_error
    with (tri := Parser.meas g (mkInitState g ss ts)) in hp; auto.
  - apply lex_nat_triple_wf.
  - constructor.
Qed.

Theorem parser_terminates_without_error :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token)
         (e  : parse_error),
    no_left_recursion g
    -> ~ parse g ss ts = Error e.
Proof.
  intros g ss ts e; unfold not; intros hp.
  destruct e.
  - (* invalid state case *)
    eapply parser_never_reaches_invalid_state; eauto.
  - (* left recursion case *)
    apply parser_doesn't_find_left_recursion_in_non_left_recursive_grammar; auto.
  - (* prediction error case *)
    apply parse_never_returns_prediction_error; auto.
Qed.