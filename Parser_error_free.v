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
    unavailable_nts_are_open_calls g (allNts g) (SF ys, []). 
Proof.
  intros g ys; intros x hi hni; ND.fsetdec.
Qed.

(* to do : There is some redundancy here with proofs about
   unavailable_nts_invar in Prediction. Those proofs should
   be defined in terms of unavailable_nts_are_open_calls *)

Lemma return_preserves_unavailable_nts_invar :
  forall g s_ce s_cr s_cr' s_frs x suf av,
    s_ce     = SF []
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> unavailable_nts_are_open_calls g av (s_ce, s_cr :: s_frs)
    -> unavailable_nts_are_open_calls g (NtSet.add x av) (s_cr', s_frs).
Proof.
  intros; subst.
  pose proof return_preserves_unavailable_nts_invar as hr; sis.
  eapply hr; eauto.
Qed.

Lemma push_preserves_unavailable_nts_invar :
  forall g av fr ce o o' pre suf suf' x v v' frs,
    fr    = Fr (Loc o pre (NT x :: suf)) v
    -> ce = Fr (Loc o' [] suf') v'
    -> unavailable_nts_are_open_calls g av (lstackOf (fr, frs))
    -> unavailable_nts_are_open_calls g (NtSet.remove x av) (lstackOf (ce, fr :: frs)).
Proof.
  intros g av fr ce o o' pre suf suf' x v v' frs ? ? hu; subst; sis.
  intros x' hi hn; split; auto.
  destruct (NF.eq_dec x' x); subst.
  - exists []; repeat eexists; eauto.
  - assert (hn' : ~ NtSet.In x' av) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as [? [frs_pre [? [? [? [heq [? ?]]]]]]]; subst; rewrite heq.
    exists (Loc o pre (NT x :: suf) :: frs_pre); repeat eexists; eauto.
Qed.
    
Lemma step_preserves_unavailable_nts_invar :
  forall g st st',
    step g st = StepK st'
    -> stack_wf g st.(stack)
    -> unavailable_nts_invar g st
    -> unavailable_nts_invar g st'.
Proof.
  intros g [av stk ts] [av' stk' ts'] hs hw hu.
  unfold unavailable_nts_invar in *.
  unfold step in hs; dmeqs h; tc; inv hs.
  - eapply return_preserves_unavailable_nts_invar; eauto. 
  - intros x hi hn; ND.fsetdec.
  - eapply push_preserves_unavailable_nts_invar; eauto.
  - eapply push_preserves_unavailable_nts_invar; eauto.
Qed.

step g pstk sstk ts av u = StepK ps' ss' ts' av' u'


Lemma step_left_recursion_detection_sound :
  forall g p_stk s_stk ts av u x,
    unavailable_nts_are_open_calls g av s_stk
    -> step g p_stk s_stk ts av u = StepError (LeftRecursion x)
    -> left_recursive g (NT x).
Proof.
  intros g p_stk s_stk ts av u x hu hs.
  apply step_LeftRecursion_facts in hs.
  destruct hs as (hni & hi & suf & frs & ?); subst.
  apply hu in hni; auto.
  destruct hni as (frs_pre & cr & frs_suf & suf' & ? & ? & hf); subst.
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
    + admit.
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
         (u      : bool)
         (a'     : Acc lex_nat_triple (Parser.meas g (Pst av stk ts u)))
         (e      : prediction_error),
    no_left_recursion g
    -> tri = Parser.meas g (Pst av stk ts u)
    -> stack_wf g stk
    -> multistep g (Pst av stk ts u) a' <> Error (PredictionError e).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros ts av (fr, frs) u a' e hn heq hw; unfold not; intros hm; subst.
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
    with (tri := meas g (mkInitState g ss ts)) in hp; auto.
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