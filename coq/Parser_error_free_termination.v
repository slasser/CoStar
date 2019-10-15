Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
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

Inductive nullable_frames_path (g : grammar) : nonterminal -> nonterminal -> list frame -> Prop :=
| NFP : 
    forall top_fr mid_frs bot_fr x y suf suf',
      bot_fr.(loc).(rsuf) = NT x :: suf
      -> List.Forall (fun mf => nullable_gamma g mf.(loc).(rpre)) mid_frs
      -> nullable_gamma g top_fr.(loc).(rpre)
      -> top_fr.(loc).(rsuf) = NT y :: suf'
      -> nullable_frames_path g x y (top_fr :: mid_frs ++ [bot_fr]).

Lemma nullable_path_two_head_frames :
  forall g l l' v v' frs y suf,
    frames_wf g (Fr l v :: Fr l' v' :: frs)
    -> nullable_gamma g l.(rpre)
    -> l.(rsuf) = NT y :: suf
    -> exists x suf',
        l'.(rsuf) = NT x :: suf'
        /\ nullable_path g (NT x) (NT y).
Proof.
  intros g l l' v v' frs y suf hw hn heq.
  inv hw; sis; subst; eauto.
Qed.
(*
Lemma nullable_path_two_head_frames :
  forall g fr fr' frs y suf,
    frames_wf g (fr :: fr' :: frs)
    -> nullable_gamma g fr.(loc).(rpre)
    -> fr.(loc).(rsuf) = NT y :: suf
    -> exists x suf',
        fr'.(loc).(rsuf) = NT x :: suf'
        /\ nullable_path g (NT x) (NT y).
Proof.
  intros g fr fr' frs y suf hw hn heq.
  unfold frames_wf in hw.
  sis.
  inv hw; sis; subst.
  assert (suf' = NT y :: suf).
  { rewrite <- H in heq; sis; auto. }
  subst.
  exists x; exists suf0; split; eauto.
  eapply DirectPath; eauto.
  rewrite <- H in heq.
  simpl in heq; subst.
  eauto.
  destruct fr as rewrit
  destruct fr.
  exists x; exists suf0; split; auto.
  econstructor; eauto.
Qed.

Lemma nullable_path_two_head_frames :
  forall g fr fr' frs y suf,
    frames_wf g (fr :: fr' :: frs)
    -> nullable_gamma g fr.(loc).(rpre)
    -> fr.(loc).(rsuf) = NT y :: suf
    -> exists x suf',
        fr'.(loc).(rsuf) = NT x :: suf'
        /\ nullable_path g (NT x) (NT y).
Proof.
  intros g fr fr' frs y suf hw hn heq.
  unfold frames_wf in *; sis.
  inv hw; sis; subst; eauto 20.  
Qed.

*)

(* CLEAN THIS UP *)
Lemma stack_configuration_repr_nullable_path :
  forall g frs l l_cr v v_cr x y suf suf',
    frames_wf g (Fr l v :: frs ++ [Fr l_cr v_cr])
    -> nullable_gamma g l.(rpre)
    -> l.(rsuf) = NT y :: suf
    -> processed_symbols_all_nullable g frs
    -> l_cr.(rsuf) = NT x :: suf'
    -> nullable_path g (NT x) (NT y).
Proof.
  intros g frs.
  induction frs as [| (l', v') frs IH]; intros l l_cr v v_cr x y suf suf' hw hn heq hp heq'; sis. 
  - inv hw; sis.
    inv heq'.
    eapply DirectPath; eauto.
  - rename y into z.
    pose proof hw as hw'.
    eapply nullable_path_two_head_frames in hw'; eauto.
    destruct hw' as [y [suf'' [heq'' hnp]]].
    apply nullable_path_trans with (y := (NT y)); auto.
    apply frames_wf_tl in hw.
    inv hp; sis.
    eapply IH in hw; eauto.
Qed.

(*
Lemma stack_configuration_repr_nullable_path :
  forall g frs fr fr_cr x y suf suf',
    frames_wf g (fr :: frs ++ [fr_cr])
    -> nullable_gamma g fr.(loc).(rpre)
    -> fr.(loc).(rsuf) = NT y :: suf
    -> processed_symbols_all_nullable g frs
    -> fr_cr.(loc).(rsuf) = NT x :: suf'
    -> nullable_path g (NT x) (NT y).
Proof.
  intros g frs.
  induction frs as [| fr' frs IH]; intros fr fr_cr x y suf suf' hw hn heq hp heq'; sis.
  - inv hw; sis.
    inv heq'.
    eapply DirectPath; eauto.
  - rename y into z.
    pose proof hw as hw'.
    eapply nullable_path_two_head_frames in hw'; eauto.
    destruct hw' as [y [suf'' [heq'' hnp]]].
    apply nullable_path_trans with (y := (NT y)); auto.
    assert (hw' : frames_wf g (fr' :: frs ++ [fr_cr])).
    { inv hw; auto. }
    inv hp.
    eapply IH in hw'; eauto.
Qed.
 *)

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
    -> unavailable_nts_are_open_calls_invar g st
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
    unfold unavailable_nts_are_open_calls_invar in hu.
    unfold nt_unavailable in hu.
    assert (hand : In x (lhss g) /\ ~ NtSet.In x av).
    { split; auto.
      apply in_lhss_iff_in_allNts; auto. }
    apply hu in hand; clear hu.
    destruct hand as [hng [frs_pre [fr_cr [frs_suf [suf_cr [heq' [hp heq'']]]]]]]; subst.
    simpl in hw.
    assert (happ : fr :: frs_pre ++ fr_cr :: frs_suf =
                   (fr :: frs_pre ++ [fr_cr]) ++ frs_suf).
    (* lemma *)
    { simpl. rewrite <- app_assoc. simpl. auto. }
    rewrite happ in hw; clear happ.
    apply frames_wf_app_l in hw.
    destruct fr as (l, v); destruct fr_cr as (l', v').
    eapply stack_configuration_repr_nullable_path in hw; eauto.
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
    unfold unavailable_nts_are_open_calls_invar; simpl.
    intros x' hu.
    exfalso.
    eapply all_nts_available_no_nt_unavailable; eauto.
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

Require Import GallStar.Prediction.
Require Import GallStar.Prediction_error_free_termination.

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