Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

(* BREAKING THIS INTO TWO GROUPS OF LEMMAS
   FOR THE TWO TYPES OF PREDICTION ERRORS *)

(* SP INVALID STATE CASE *)

Definition all_sp_stacks_wf (g : grammar) (sps : list subparser) : Prop :=
  forall sp, In sp sps -> lstack_wf g sp.(stack).

Definition sp_ready_for_move (sp : subparser) : Prop :=
  match sp with
  | Sp _ _ (loc, locs) =>
    (loc.(rsuf) = [] /\ locs = [])
    \/ exists a suf, loc.(rsuf) = T a :: suf
  end.

Definition all_sps_ready_for_move (sps : list subparser) : Prop :=
  forall sp, In sp sps -> sp_ready_for_move sp.

Lemma spClosureStep_never_returns_SpInvalidState :
  forall g sp,
    lstack_wf g sp.(stack)
    -> spClosureStep g sp <> SpClosureStepError SpInvalidState.
Proof.
  intros g sp hw; unfold not; intros hs.
  unfold spClosureStep in hs; dms; tc; inv hw.
Qed.

Lemma spClosure_never_returns_SpInvalidState :
  forall (g    : grammar)
         (pair : nat * nat)
         (a    : Acc lex_nat_pair pair)
         (sp   : subparser)
         (a'   : Acc lex_nat_pair (spMeas g sp)),
    pair = spMeas g sp
    -> lstack_wf g sp.(stack)
    -> spClosure g sp a' <> inl SpInvalidState.
Proof.
  intros g pair a'.
  induction a' as [pair hlt IH].
  intros sp a heq hw; unfold not; intros hs; subst.
  apply spClosure_error_cases in hs.
  destruct hs as [hs | [sps [hs [crs [heq heq']]]]]; subst.
  - eapply spClosureStep_never_returns_SpInvalidState; eauto.
  - apply error_in_aggrClosureResults_result_in_input in heq'.
    eapply in_dmap in heq'; eauto.
    destruct heq' as [sp' [hi [hi' heq]]].
    eapply IH with (sp := sp'); eauto.
    + eapply spClosureStep_meas_lt; eauto.
    + eapply spClosureStep_preserves_lstack_wf_invar; eauto.
Qed.
    
Lemma closure_never_returns_SpInvalidState :
  forall g sps,
    all_sp_stacks_wf g sps
    -> closure g sps <> inl SpInvalidState.
Proof.
  intros g sps hw; unfold not; intros hc.
  unfold closure in hc.
  apply error_in_aggrClosureResults_result_in_input in hc.
  apply in_map_iff in hc; destruct hc as [sp [hs hi]].
  eapply spClosure_never_returns_SpInvalidState; eauto.
  apply lex_nat_pair_wf.
Qed.

Lemma startState_never_returns_SpInvalidState :
  forall g loc locs x suf,
    lstack_wf g (loc, locs)
    -> loc.(rsuf) = NT x :: suf
    -> startState g x (loc, locs) <> inl SpInvalidState.
Proof.
  intros g loc locs x suf hw heq; unfold not; intros hss.
  eapply closure_never_returns_SpInvalidState; eauto.
  intros sp hi.
  apply in_map_iff in hi.
  destruct hi as [rhs [heq' hi]]; subst; simpl.
  (* LEMMA *)
  clear hss.
  inv hw; sis; subst.
  - constructor; auto.
    apply in_rhssForNt_production_in_grammar; auto.
  - constructor; auto.
    apply in_rhssForNt_production_in_grammar; auto.
Qed.

Lemma handleFinalSubparsers_never_returns_error :
  forall sps e,
    handleFinalSubparsers sps <> PredError e.
Proof.
  intros sps e; unfold not; intro hh.
  unfold handleFinalSubparsers in hh; dms; tc.
Qed.

Lemma moveSp_never_returns_SpInvalidState_for_ready_sp :
  forall t sp,
    sp_ready_for_move sp
    -> moveSp t sp <> SpMoveError SpInvalidState.
Proof.
  intros t sp hr; unfold not; intros hm.
  unfold moveSp in hm.
  dms; tc; sis.
  - unfold sp_ready_for_move in hr; sis.
    destruct hr as [[_ heq] | [a [suf heq]]]; inv heq.
  - destruct hr as [[heq _] | [a [suf heq]]]; inv heq.
Qed.

Lemma move_never_returns_SpInvalidState_for_ready_sps :
  forall t sps,
    all_sps_ready_for_move sps
    -> move t sps <> inl SpInvalidState.
Proof.
  intros t sps ha; unfold not; intros hm.
  unfold move in hm.
  apply aggrMoveResults_error_in_input in hm.
  apply in_map_iff in hm.
  destruct hm as [sp [hm hi]].
  eapply moveSp_never_returns_SpInvalidState_for_ready_sp; eauto.
Qed.

Lemma moveSp_preserves_lstack_wf_invar :
  forall g t sp sp',
    lstack_wf g sp.(stack)
    -> moveSp t sp = SpMoveSucc sp'
    -> lstack_wf g sp'.(stack).
Proof.
  intros g t sp sp' hw hm.
  unfold moveSp in hm; dms; tc; inv hm; sis.
  inv hw; auto.
  constructor; auto.
  rewrite <- app_assoc; auto.
Qed.

Lemma move_preserves_lstack_wf_invar :
  forall g t sps sps',
    all_sp_stacks_wf g sps
    -> move t sps = inr sps'
    -> all_sp_stacks_wf g sps'.
Proof.
  intros g t sps sps' ha hm.
  unfold all_sp_stacks_wf.
  intros sp' hi.
  unfold move in hm.
  eapply in_aggrMoveResults_result_in_input in hm; eauto.
  apply in_map_iff in hm.
  destruct hm as [sp [hm hi']].
  eapply moveSp_preserves_lstack_wf_invar; eauto.
Qed.

Lemma spClosure_preserves_lstack_wf_invar :
  forall g pr (a : Acc lex_nat_pair pr) sp sp' a' sps',
    pr = spMeas g sp
    -> lstack_wf g sp.(stack)
    -> spClosure g sp a' = inr sps'
    -> In sp' sps'
    -> lstack_wf g sp'.(stack).
Proof.
  intros g pr a'.
  induction a' as [pr hlt IH]; intros sp sp' a sps' heq hw hs hi; subst.
  apply spClosure_success_cases in hs.
  destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
  - apply in_singleton_eq in hi; subst; auto.
  - eapply sp_in_aggrClosureResults_result_in_input in heq'; eauto.
    destruct heq' as [sps''' [hi' hi'']].
    eapply in_dmap in hi'; eauto.
    destruct hi' as [sp'' [hi' [hi''' heq]]].
    eapply IH in heq; eauto.
    + eapply spClosureStep_meas_lt; eauto.
    + eapply spClosureStep_preserves_lstack_wf_invar; eauto.
Qed.
  
Lemma closure_preserves_lstack_wf_invar :
  forall g sps sps',
    all_sp_stacks_wf g sps
    -> closure g sps = inr sps'
    -> all_sp_stacks_wf g sps'.
Proof.
  intros g sps sps' ha hc.
  unfold closure in hc.
  unfold all_sp_stacks_wf.
  intros sp' hi.
  eapply sp_in_aggrClosureResults_result_in_input in hc; eauto.
  destruct hc as [sps'' [hi' hi'']].
  apply in_map_iff in hi'.
  destruct hi' as [sp [hs hi']]; subst.
  eapply spClosure_preserves_lstack_wf_invar; eauto.
  apply lex_nat_pair_wf.
Qed.

Lemma spClosureStepDone_ready_for_move :
  forall g sp,
    spClosureStep g sp = SpClosureStepDone
    -> sp_ready_for_move sp.
Proof.
  intros g sp hs.
  unfold spClosureStep in hs; dms; tc; sis; eauto.
Qed.

Lemma sp_in_spClosure_result_ready_for_move :
  forall g pr (a : Acc lex_nat_pair pr) sp sp' a' sps',
    pr = spMeas g sp
    -> spClosure g sp a' = inr sps'
    -> In sp' sps'
    -> sp_ready_for_move sp'.
Proof.
  intros g pr a'.
  induction a' as [pr hlt IH]; intros sp sp' a sps' heq hs hi; subst.
  apply spClosure_success_cases in hs.
  destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
  - apply in_singleton_eq in hi; subst; auto.
    eapply spClosureStepDone_ready_for_move; eauto.
  - eapply sp_in_aggrClosureResults_result_in_input in heq'; eauto.
    destruct heq' as [sps''' [hi' hi'']].
    eapply in_dmap in hi'; eauto.
    destruct hi' as [sp'' [hi' [hi''' heq]]].
    eapply IH in heq; eauto.
    eapply spClosureStep_meas_lt; eauto.
Qed.

Lemma sps_ready_for_move_after_closure :
  forall g sps sps',
    closure g sps = inr sps'
    -> all_sps_ready_for_move sps'.
Proof.
  intros g sps sps' hc.
  unfold closure in hc.
  unfold all_sps_ready_for_move.
  intros sp' hi.
  eapply sp_in_aggrClosureResults_result_in_input in hc; eauto.
  destruct hc as [sps'' [hi' hi'']].
  apply in_map_iff in hi'.
  destruct hi' as [sp [hs hi']].
  eapply sp_in_spClosure_result_ready_for_move; eauto.
  apply lex_nat_pair_wf.
Qed.
    
Lemma llPredict'_never_returns_SpInvalidState :
  forall g ts sps,
    all_sp_stacks_wf g sps
    -> all_sps_ready_for_move sps
    -> llPredict' g ts sps <> PredError SpInvalidState.
Proof.
  intros g ts; induction ts as [| t ts IH]; intros sps ha ha'; unfold not; intros hl; sis.
  - eapply handleFinalSubparsers_never_returns_error; eauto.
  - destruct sps as [| sp sps']; tc.
    dm; tc.
    dmeq hm; tc.
    + inv hl.
      eapply move_never_returns_SpInvalidState_for_ready_sps; eauto.
    + dmeq hc; tc.
      * inv hl.
        eapply move_preserves_lstack_wf_invar in hm; eauto.
        eapply closure_never_returns_SpInvalidState; eauto.
      * eapply IH in hl; eauto.
        -- eapply move_preserves_lstack_wf_invar in hm; eauto.
           eapply closure_preserves_lstack_wf_invar; eauto.
        -- eapply sps_ready_for_move_after_closure; eauto.
Qed.

Lemma stacks_wf_in_startState_result :
  forall g fr frs x suf sps,
    lstack_wf g (fr, frs)
    -> fr.(rsuf) = NT x :: suf
    -> startState g x (fr, frs) = inr sps
    -> all_sp_stacks_wf g sps.
Proof.
  intros g fr frs x suf sps hw heq hs.
  unfold startState in hs.
  eapply closure_preserves_lstack_wf_invar; eauto.
  unfold all_sp_stacks_wf.
  intros sp hi.
  apply in_map_iff in hi.
  destruct hi as [rhs [heq' hi]]; subst; sis.
  apply in_rhssForNt_production_in_grammar in hi.
  inv hw; sis; subst; auto.
Qed.

Lemma llPredict_never_returns_SpInvalidState :
  forall g fr frs x suf ts,
    lstack_wf g (fr, frs)
    -> fr.(rsuf) = NT x :: suf
    -> llPredict g x (fr, frs) ts <> PredError SpInvalidState.
Proof.
  intros g fr frs x suf ts hw heq; unfold not; intros hl.
  unfold llPredict in hl.
  dmeq hss.
  - inv hl.
    eapply startState_never_returns_SpInvalidState; eauto.
  - eapply llPredict'_never_returns_SpInvalidState; eauto.
    + eapply stacks_wf_in_startState_result; eauto.
    + unfold startState in hss.
      eapply sps_ready_for_move_after_closure; eauto.
Qed.

(* LEFT RECURSION CASE *)

Lemma spClosureStep_never_finds_left_recursion :
  forall g sp x,
    spClosureStep g sp <> SpClosureStepError (SpLeftRecursion x).
Proof.
  intros g sp x; unfold not; intros hs.
  unfold spClosureStep in hs; repeat dmeq h; tc; inv hs; subst.
Admitted.

Lemma spClosure_never_finds_left_recursion :
  forall g pr (a : Acc lex_nat_pair pr) sp a' x,
    pr = spMeas g sp
    -> spClosure g sp a' <> inl (SpLeftRecursion x).
Proof.
  intros g pr a'; induction a' as [pr hlt IH]; intros sp a x heq; unfold not; intros hs; subst.
  apply spClosure_error_cases in hs.
  destruct hs as [hs | [sps [hs [crs [hc ha]]]]]; subst.
  - eapply spClosureStep_never_finds_left_recursion; eauto.
  - apply error_in_aggrClosureResults_result_in_input in ha.
    eapply in_dmap in ha; eauto.
    destruct ha as [sp' [hi [hi' hs']]].
    eapply IH with (sp := sp'); eauto.
    eapply spClosureStep_meas_lt; eauto.
Qed.

Lemma closure_never_finds_left_recursion :
  forall g x sps,
    closure g sps <> inl (SpLeftRecursion x).
Proof.
  intros g x sps; unfold not; intros hc.
  unfold closure in hc.
  apply error_in_aggrClosureResults_result_in_input in hc.
  apply in_map_iff in hc.
  destruct hc as [sp [hs hi]].
  eapply spClosure_never_finds_left_recursion; eauto.
  apply lex_nat_pair_wf.
Qed.        

Lemma startState_never_finds_left_recursion :
  forall g x x' stk,
    startState g x stk <> inl (SpLeftRecursion x').
Proof.
  intros g x x' (fr, frs); unfold not; intros hs.
  unfold startState in hs.
  eapply closure_never_finds_left_recursion; eauto.
Qed.

Lemma llPredict_never_returns_SpLeftRecursion :
  forall g x x' stk ts,
    llPredict g x stk ts <> PredError (SpLeftRecursion x').
Proof.
  intros g x x' stk ts; unfold not; intros hl.
  unfold llPredict in hl.
  dmeq hss.
  - inv hl.
    eapply startState_never_finds_left_recursion; eauto.
  - admit.
Admitted.

(* PARSER STUFF *)

Require Import GallStar.Parser.

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
    step g st <> StepError (PredictionError (SpLeftRecursion x)).
Proof.
  intros g st x; unfold not; intros hs.
  unfold step in hs; repeat dmeq h; tc; inv hs; sis.
  eapply llPredict_never_returns_SpLeftRecursion; eauto.
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
    tri = Parser.meas g (Pst av stk ts)
    -> stack_wf g stk
    -> ~ multistep g (Pst av stk ts) a' = Error (PredictionError e).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros ts av stk a' e heq hw; unfold not; intros hm; subst.
  apply multistep_prediction_error_cases in hm.
  destruct hm as [hs | hm].
  - destruct e as [ | x]. 
    + (* InvalidState case -- should be easy *)
      destruct stk as (fr, frs).
      eapply step_never_returns_SpInvalidState in hs; eauto.
    + (* LeftRecursion case *)
      eapply step_never_returns_SpLeftRecursion; eauto.
  - destruct hm as [[av' stk' ts'] [a'' [hs hm]]].
    eapply IH in hm; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
Qed.