Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Require Import GallStar.Prediction_error_free.
Import ListNotations.

(* The following three groups of lemmas correspond to the three
   types of parser errors: errors indicating an invalid parser
   state, errors that indicate a left-recursive grammar, and 
   errors that arise during prediction *)

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
    parse g ss ts <> Error InvalidState.
Proof.
  intros g ss ts; unfold not; intros hp.
  unfold parse in hp.
  apply multistep_never_reaches_error_state
    with (tri := Parser.meas g (mkInitState g ss ts)) in hp; auto.
  - apply lex_nat_triple_wf.
  - constructor.
Qed.

(* The parser doesn't return a "left recursion detected" error
   when given a non-left-recursive grammar *)

Lemma step_left_recursion_detection_sound :
  forall g st x,
    stack_wf g st.(stack)
    -> unavailable_nts_invar g st
    -> step g st = StepError (LeftRecursion x)
    -> left_recursive g (NT x).
Proof.
  intros g [av (fr, frs) ts] x hw hu hs.
  apply step_LeftRecursion_facts in hs.
  destruct hs as [hnin [hin [suf heq]]]; subst.
  apply hu in hnin; auto.
  destruct hnin as [hng [frs_pre [cr [frs_suf [suf_cr [heq' [hp heq'']]]]]]]; subst.
  unfold stack_wf in hw; unfold frames_wf in hw; simpl in hw.
  rewrite heq' in hw.
  assert (happ :  fr.(loc) :: frs_pre ++ cr :: frs_suf =
                 (fr.(loc) :: frs_pre ++ [cr]) ++ frs_suf)
    by (simpl; apps).
  rewrite happ in hw.
  apply locations_wf_app_l in hw.
  eapply stack_configuration_repr_nullable_path; eauto.
Qed.

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
  - eapply step_left_recursion_detection_sound; eauto. 
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
    -> parse g ss ts <> Error (LeftRecursion x).
Proof.
  intros g ss ts x hn; unfold not; intros hp.
  apply parse_left_recursion_detection_sound in hp; firstorder.
Qed.

(* Errors never arise during prediction, given a non-left-recursive grammar *)

Lemma step_never_returns_SpInvalidState :
  forall g (st : parser_state),
    stack_wf g st.(stack)
    -> step g st <> StepError (PredictionError SpInvalidState).
Proof.
  intros g st hw; unfold not; intros hs.
  unfold step in hs; repeat dmeq h; tc; inv hs; sis; subst.
  eapply llPredict_never_returns_SpInvalidState; eauto.
  simpl; eauto.
Qed.

Lemma step_never_returns_SpLeftRecursion :
  forall g (st : parser_state) x,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> step g st <> StepError (PredictionError (SpLeftRecursion x)).
Proof.
  intros g st x hn hw; unfold not; intros hs.
  unfold step in hs; repeat dmeq h; tc; inv hs; sis.
  eapply llPredict_never_returns_SpLeftRecursion; eauto.
  simpl; eauto.
Qed.

Lemma multistep_never_returns_prediction_error :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (ts     : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (a'     : Acc lex_nat_triple (Parser.meas g (Pst av stk ts)))
         (e      : prediction_error),
    no_left_recursion g
    -> tri = Parser.meas g (Pst av stk ts)
    -> stack_wf g stk
    -> multistep g (Pst av stk ts) a' <> Error (PredictionError e).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros ts av (fr, frs) a' e hn heq hw; unfold not; intros hm; subst.
  apply multistep_prediction_error_cases in hm.
  destruct hm as [hs | hm].
  - destruct e as [ | x].
    + (* InvalidState case *)
      eapply step_never_returns_SpInvalidState in hs; eauto.
    + (* LeftRecursion case *)
      eapply step_never_returns_SpLeftRecursion in hs; eauto.
  - destruct hm as [[av' stk' ts'] [a'' [hs hm]]].
    eapply IH in hm; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
Qed.

Lemma parse_never_returns_prediction_error :
  forall (g : grammar)
         (ss : list symbol)
         (ts : list token)
         (e  : prediction_error),
    no_left_recursion g
    -> parse g ss ts <> Error (PredictionError e).
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
    -> parse g ss ts <> Error e.
Proof.
  intros g ss ts e; unfold not; intros hp; destruct e.
  - (* invalid state case *)
    eapply parser_never_reaches_invalid_state; eauto.
  - (* left recursion case *)
    apply parser_doesn't_find_left_recursion_in_non_left_recursive_grammar; auto.
  - (* prediction error case *)
    apply parse_never_returns_prediction_error; auto.
Qed.