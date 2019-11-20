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
  | Loc _ _ [] :: _               => [] (* impossible *)
  | Loc _ _ (T _ :: _) :: _       => [] (* impossible *)
  | Loc _ _ (NT x :: suf) :: frs' => suf ++ unprocTailSyms frs'
  end.

Definition unprocStackSyms stk : list symbol :=
  match stk with
  | (Loc o pre suf, frs) => suf ++ unprocTailSyms frs
  end.

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
  apply rhssForNt_in_grammar_iff; auto.
Qed.

Lemma mc_multistep_succ_final_config :
  forall g sp sp' wpre wsuf,
    move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
    -> wsuf = []
    -> finalConfig sp' = true.
Proof.
  intros g sp sp' wpre wsuf hm.
  induction hm; intros heq; auto.
  inv heq.
Qed.

Lemma move_step_preserves_label :
  forall g sp sp' w w',
    move_step g sp w sp' w'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' w w' hm; inv hm; auto.
Qed.

Lemma closure_step_preserves_label :
  forall g sp sp',
    closure_step g sp sp'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' hc; inv hc; auto.
Qed.

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

Lemma mc_multistep_preserves_label :
  forall g sp sp' w w',
    move_closure_multistep g sp w sp' w'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' w w' hm.
  induction hm as [ ? ? ? ?
                  | ? ? ? ? ? ? ? ? ?
                  | ? ? ? ? ? ? ? hm hc hmc]; auto.
  apply move_step_preserves_label in hm.
  apply closure_multistep_preserves_label in hc; tc.
Qed.

Lemma allPredictionsEqual_inv_cons :
  forall sp' sp sps,
    allPredictionsEqual sp' (sp :: sps) = true
    -> sp'.(prediction) = sp.(prediction)
       /\ allPredictionsEqual sp' sps = true.
Proof.
  intros sp' sp sps ha.
  unfold allPredictionsEqual in ha; unfold allEqual in ha; sis.
  apply andb_true_iff in ha; destruct ha as [hhd htl]; split; auto.
  unfold beqGamma in *; dms; tc.
Qed.

Lemma allPredictionEqual_in_tl :
  forall sp sp' sps,
    allPredictionsEqual sp sps = true
    -> In sp' sps
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros sp sp' sps ha hi; induction sps as [| sp'' sps IH]; inv hi;
  apply allPredictionsEqual_inv_cons in ha; destruct ha as [hhd htl]; auto.
Qed.
      
Lemma allPredictionEqual_in :
  forall sp' sp sps,
    allPredictionsEqual sp sps = true
    -> In sp' (sp :: sps)
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros sp' sp sps ha hi; inv hi; auto.
  eapply allPredictionEqual_in_tl; eauto.
Qed.

Lemma moveSp_succ_step :
  forall g sp sp' av pred o pre a l suf frs,
    sp = Sp av pred (Loc o pre (T a :: suf), frs)
    -> sp' = Sp (allNts g) pred (Loc o (pre ++ [T a]) suf, frs)
    -> moveSp g (a, l) sp = SpMoveSucc sp'.
Proof.
  intros; subst; unfold moveSp; dms; tc.
Qed.

Lemma moveSp_result_in_map :
  forall g sp av pred o pre a t suf frs sps,
    sp = Sp av pred (Loc o pre (T a :: suf), frs)
    -> In sp sps
    -> In (moveSp g t sp) (map (moveSp g t) sps).
Proof.
  intros; subst; apply in_map_iff; eauto.
Qed.

Lemma map_unroll_once :
  forall (A B : Type) (f : A -> B) x xs,
    map f (x :: xs) = f x :: map f xs.
Proof.
  auto.
Qed.

Lemma aggrMoveResults_in_input_in_output :
  forall g t sp sps sp' sps',
    In sp sps
    -> moveSp g t sp = SpMoveSucc sp'
    -> aggrMoveResults (map (moveSp g t) sps) = inr sps'
    -> In sp' sps'.
Proof.
  intros g t sp sps. 
  induction sps as [| hd tl IH]; intros sp' sps' hi hm ha; inv hi; sis.
  - dms; tc. 
    inv hm; inv ha.
    apply in_eq.
  - dms; tc.
    inv ha.
    apply in_cons; auto.
Qed.

Lemma move_in_input_in_output :
  forall g t sp sp' sps sps',
    In sp sps
    -> moveSp g t sp = SpMoveSucc sp'
    -> move g t sps = inr sps'
    -> In sp' sps'.
Proof.
  intros g t sp sp' sps sps' hi hm hm'.
  eapply aggrMoveResults_in_input_in_output; eauto.
Qed.

Lemma move_succ_step :
  forall g sp sp' av pred o pre a l suf frs sps sps',
    sp = Sp av pred (Loc o pre (T a :: suf), frs)
    -> sp' = Sp (allNts g) pred (Loc o (pre ++ [T a]) suf, frs)
    -> In sp sps
    -> move g (a, l) sps = inr sps'
    -> In sp' sps'.
Proof.
  intros g sp sp' av pred o pre a l suf frs sps sps' ? ? hi hm; subst.
  eapply move_in_input_in_output; eauto.
  eapply moveSp_succ_step; eauto.
Qed.

Lemma move_func_refines_rel :
  forall g t ts sp sp' sps sps',
    In sp sps
    -> move_step g sp (t :: ts) sp' ts
    -> move g t sps = inr sps'
    -> In sp' sps'.
Proof.
  intros g t ts sp sp' sps sps' hi hr hf.
  inv hr.
  eapply move_succ_step; eauto.
Qed.

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

Lemma acr_map_inr_all_inr :
  forall sp (f : subparser -> closure_result) (sps : list subparser) sps'',
    In sp sps
    -> aggrClosureResults (map f sps) = inr sps''
    -> exists sps',
        f sp = inr sps'
        /\ forall sp', In sp' sps' -> In sp' sps''.
Proof.
  intros sp f sps; induction sps as [| hd tl IH]; intros sps'' hi ha.
  - inv hi.
  - destruct hi as [hh | ht]; subst.
    + simpl in ha.
      dmeq hsp; tc.
      dmeq hag; tc.
      inv ha.
      repeat eexists; eauto.
      intros sp' hi; apply in_or_app; auto.
    + simpl in ha.
      dmeq hsp; tc.
      dmeq hag; tc.
      inv ha.
      eapply IH with (sps'' := l0) in ht; eauto.
      destruct ht as [sps' [heq hall]].
      repeat eexists; eauto.
      intros sp' hi.
      apply in_or_app; auto.
Qed.

Lemma acr_dmap_inr_all_inr :
  forall sp (sps : list subparser) (f : forall sp, In sp sps -> closure_result) sps'',
    In sp sps
    -> aggrClosureResults (dmap sps f) = inr sps''
    -> exists hi sps',
        f sp hi = inr sps'
        /\ forall sp', In sp' sps' -> In sp' sps''.
Proof.
  intros sp sps; induction sps as [| hd tl IH]; intros f sps'' hi ha.
  - inv hi.
  - destruct hi as [hh | ht]; subst.
    + simpl in ha.
      dmeq hsp; tc.
      dmeq hag; tc.
      inv ha.
      repeat eexists; eauto.
      intros sp' hi; apply in_or_app; auto.
    + simpl in ha.
      dmeq hsp; tc.
      dmeq hag; tc.
      inv ha.
      unfold eq_rect_r in hag; simpl in hag.
      apply IH in hag; auto.
      destruct hag as [hi [sps' [heq hall]]].
      repeat eexists; eauto.
      intros sp' hi'.
      apply in_or_app; auto.
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

Lemma production_lhs_in_lhss :
  forall g x ys,
    In (x, ys) g
    -> In x (lhss g).
Proof.
  intros g x ys hi; induction g as [| (x', ys') ps IH]; sis.
  - inv hi.
  - destruct hi as [hh | ht].
    + inv hh; apply in_eq.
    + apply in_cons; auto.
Qed.

Lemma lhs_mem_allNts_true :
  forall g x ys,
    In (x, ys) g
    -> NtSet.mem x (allNts g) = true.
Proof.
  intros g x ys hi.
  apply NtSet.mem_spec.
  apply in_lhss_iff_in_allNts.
  eapply production_lhs_in_lhss; eauto.
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
        apply rhssForNt_in_grammar_iff; auto.
  - exfalso.
    inv hc. inv H.
    apply lhs_mem_allNts_true in H10; tc.
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
  eapply acr_dmap_inr_all_inr in ha; eauto.
  destruct ha as [hi' [sps'' [heq hall]]]; eauto.
Qed.

Lemma spClosure_func_refines_rel' :
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
    eapply acr_dmap_inr_all_inr in ha; eauto.
    destruct ha as [hi' [sps''' [heq hall]]].
    apply hall.
    eapply IH; eauto.
    eapply spClosureStep_meas_lt; eauto.
Qed.

Lemma spClosure_func_refines_rel :
  forall (g  : grammar) (sp sp'' : subparser) (a : Acc lex_nat_pair (meas g sp)) (sps'' : list subparser),
    closure_multistep g sp sp''
    -> spClosure g sp a  = inr sps''
    -> In sp'' sps''.
Proof.
  intros; eapply spClosure_func_refines_rel'; eauto.
Qed.

Lemma closure_func_refines_rel :
  forall g sp sp'' sps sps'',
    In sp sps
    -> closure_multistep g sp sp''
    -> closure g sps = inr sps''
    -> In sp'' sps''.
Proof.
  intros g sp sp'' sps sps'' hi hc hc'.
  unfold closure in hc'.
  eapply acr_map_inr_all_inr in hc'; eauto.
  destruct hc' as [sps' [heq hall]].
  apply hall.
  eapply spClosure_func_refines_rel; eauto.
Qed.

(* REFACTOR! *)
Lemma move_closure_multistep_midpoint' :
  forall g sp sp'' w w'',
    move_closure_multistep g sp w sp'' w''
    -> forall wpre wsuf t,
      w = wpre ++ t :: wsuf
      -> w'' = wsuf
      -> exists sp',
          move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf)
          /\ move_closure_multistep g sp' (t :: wsuf) sp'' wsuf.
Proof.
  intros g sp sp'' w w'' hm.
  induction hm; intros wpre wsuf t heq heq'; subst. 
  - apply app_cons_not_nil in heq; inv heq. 
  - assert (h : (a, l) :: ts = [] ++ (a, l) :: ts) by auto.
    rewrite h in heq.
    assert (h' : wpre ++ t :: [] ++ (a, l) :: ts = (wpre ++ [t]) ++ (a, l) :: ts) by apps.
    rewrite h' in heq.
    apply app_inv_tail in heq.
    apply app_cons_not_nil in heq; inv heq.
  - destruct wpre. 
    + sis.
      inv H.
      eexists; split.
      * apply MC_terminal.
      * eapply MC_trans; eauto.
    + sis. 
      inv H.
      specialize (IHhm wpre wsuf t).
      destruct IHhm as [sp'''' [hmc hmc']]; auto.
      eexists; split; eauto.
      eapply MC_trans; eauto. 
Qed.

Lemma move_closure_multistep_midpoint :
  forall g sp sp'' t wpre wsuf,
    move_closure_multistep g sp (wpre ++ t :: wsuf) sp'' wsuf
    -> exists sp',
      move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf)
      /\ move_closure_multistep g sp' (t :: wsuf) sp'' wsuf.
Proof.
  intros; eapply move_closure_multistep_midpoint'; eauto.
Qed.

(* This can be simplified -- all we really care about is the length inequality *)
Lemma mcms_inv :
  forall g sp sp' ts ts',
    move_closure_multistep g sp ts sp' ts'
    -> (exists av pred o pre,
           sp = Sp av pred (Loc o pre [], [])
           /\ sp'  = Sp av pred (Loc o pre [], [])
           /\ ts   = []
           /\ ts'  = []
           /\ ts = ts')
       \/ (exists av pred o pre suf frs a l ts'',
              sp = Sp av pred (Loc o pre (T a :: suf), frs)
              /\ sp' = Sp av pred (Loc o pre (T a :: suf), frs)
              /\ ts  = (a, l) :: ts''
              /\ ts' = (a, l) :: ts''
              /\ ts = ts')
       \/ (exists sp'' sp''' a l ts'',
              ts = (a, l) :: ts''
              /\ move_step g sp ts sp'' ts''
              /\ closure_multistep g sp'' sp'''
              /\ move_closure_multistep g sp''' ts'' sp' ts'
              /\ List.length ts' < List.length ts).
Proof.
  intros g sp sp' ts ts' hm.
  induction hm.
  - left; eauto 10.
  - right; left; eauto 20.
  - right; right.
    inv H.
    destruct IHhm as [? | [? | ?]].
    + firstorder. subst.
      repeat eexists; eauto.
    + firstorder; subst.
      repeat eexists; eauto.
    + firstorder.
      subst.
      repeat eexists; eauto.
      sis.
      omega.
Qed.

Lemma app_eq_self_contra :
  forall A x (xs : list A),
    (x :: xs) <> xs.
Proof.
  intros A x xs; unfold not; intros heq.
  assert (heq' : [x] ++ xs = [] ++ xs) by apps.
  apply app_inv_tail in heq'; inv heq'.
Qed.

(* REFACTOR! *)
Lemma move_closure_multistep_midpoint_trans' :
  forall g sp sp'' w w'',
    move_closure_multistep g sp w sp'' w''
    -> forall wpre wmid wsuf,
      w = wpre ++ wmid ++ wsuf
      -> w'' = wsuf
      -> exists sp',
          move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
          /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
Proof.
  intros g sp sp'' w w'' hm.
  induction hm; intros wpre wmid wsuf heq heq'; subst. 
  - rewrite app_nil_r in *. 
    symmetry in heq.
    apply app_eq_nil in heq; destruct heq; subst.
    eexists; split; eauto.
    + constructor.
    + constructor.
  - assert (h : (a, l) :: ts = [] ++ (a, l) :: ts) by auto.
    rewrite h in heq.
    assert (h' : wpre ++ wmid ++ [] ++ (a,l) :: ts = ((wpre ++ wmid) ++ ((a, l) :: ts))) by apps.
    rewrite h' in heq.
    apply app_inv_tail in heq.
    symmetry in heq; apply app_eq_nil in heq; destruct heq; subst.
    sis.
    eexists; split; eauto.
    + constructor.
    + constructor.
  - destruct wpre as [| t wpre].
    + sis.
      destruct wmid as [| t' wmid].
      * sis.
        inv H.
        eapply mcms_inv in hm.
        destruct hm.
        -- firstorder.
           tc.
        -- destruct H. 
           ++ firstorder.
              subst.
              apply app_eq_self_contra in H3; inv H3.
           ++ firstorder.
              sis. omega. 
      * inv H. 
        eexists; split.
        -- eapply MC_terminal.
        -- eapply MC_trans.
           ++ constructor.
           ++ eauto.
           ++ specialize (IHhm [] wmid wsuf).
              destruct IHhm; auto.
    + inv H.
      specialize (IHhm wpre wmid wsuf).
      destruct IHhm as [sp' [hmc hmc']]; auto.
      exists sp'; split; auto.
      eapply MC_trans; eauto.
      constructor.
Qed.

(* strange--this doesn't seem to register as a lemma *)
Lemma move_closure_multistep_backtrack :
  forall g sp sp'' wpre wmid wsuf,
    move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp'' wsuf
    -> exists sp',
      move_closure_multistep g sp (wpre ++ wmid ++ wsuf) sp' (wmid ++ wsuf)
      /\ move_closure_multistep g sp' (wmid ++ wsuf) sp'' wsuf.
Proof.
  intros; eapply move_closure_multistep_midpoint_trans'; eauto.
Qed.

Lemma mcms_words_eq_subparser_eq :
  forall g sp sp' ts ts',
    move_closure_multistep g sp ts sp' ts'
    -> ts = ts'
    -> sp = sp'.
Proof.
  intros g sp sp' ts ts' hm heq; subst.
  apply mcms_inv in hm.
  destruct hm as [? | [? | ?]].
  - firstorder. subst. auto.
  - firstorder; subst; auto.
  - firstorder.
    omega.
Qed.

Lemma mcms_inv_nonempty_word :
  forall g sp sp'' t wsuf,
    move_closure_multistep g sp (t :: wsuf) sp'' wsuf
    -> exists sp',
      move_step g sp (t :: wsuf) sp' wsuf
      /\ closure_multistep g sp' sp''.
Proof.
  intros g sp sp'' t wsuf hm.
  inv hm.
  - exfalso; eapply app_eq_self_contra; eauto.
  - inv H.
    apply mcms_words_eq_subparser_eq in H1; subst; auto.
    eexists; split; eauto.
Qed.

Lemma move_closure_code_refines_relation :
  forall g sps sps' sps_after_move sps_after_move_closure wpre wsuf t,
    (forall sp sp', In sp sps -> move_closure_multistep g sp (wpre ++ t :: wsuf) sp' (t :: wsuf) -> In sp' sps')
    -> move g t sps' = inr sps_after_move
    -> closure g sps_after_move = inr sps_after_move_closure
    -> forall sp sp' w w',
        In sp sps
        -> move_closure_multistep g sp w sp' w'
        -> w = wpre ++ t :: wsuf
        -> w' = wsuf
        -> In sp' sps_after_move_closure.
Proof.
  intros g sps sps' sps_after_move sps_after_move_closure wpre wsuf t hinv hm hc sp sp' w w' hin hrel; intros; subst.
  eapply move_closure_multistep_midpoint in hrel.
  destruct hrel as [sp'' [hmc hmc']].
  apply hinv in hmc; auto.
  inv hmc'.
  - exfalso; eapply app_eq_self_contra; eauto.
  - inv H.
    eapply move_func_refines_rel with 
        (sp' := {|
                 avail := allNts g;
                 prediction := pred;
                 stack := ({| lopt := o; rpre := pre ++ [T a]; rsuf := suf |}, frs) |})
        (ts := ts'') in hm; eauto.
    eapply closure_func_refines_rel in hc; eauto.
    apply mcms_words_eq_subparser_eq in H1; subst; auto.
Qed.

Lemma llPredict'_succ_labels_eq :
  forall g orig_sps wsuf wpre curr_sps rhs,
    llPredict' g curr_sps wsuf = PredSucc rhs
    -> (forall sp sp',
           In sp orig_sps
           -> move_closure_multistep g sp (wpre ++ wsuf) sp' wsuf
           -> In sp' curr_sps)
    -> exists wpre' wsuf',
        wpre ++ wsuf = wpre' ++ wsuf'
        /\ forall sp sp',
          In sp orig_sps
          -> move_closure_multistep g sp (wpre' ++ wsuf') sp' wsuf'
          -> sp.(prediction) = rhs.
Proof.
  intros g orig_sps wsuf.
  induction wsuf as [| t wsuf' IH]; intros wpre curr_sps rhs hl hi; sis.
  - destruct curr_sps as [| sp' sps']; tc.
    dmeq hall.
    + inv hl.
      exists wpre; exists []; split; auto.
      intros orig_sp curr_sp hin hm.
      erewrite mc_multistep_preserves_label
        with (sp := orig_sp) (sp' := curr_sp); eauto.
      eapply hi in hin; eauto.
      erewrite allPredictionEqual_in; eauto.
    + unfold handleFinalSubparsers in hl.
      destruct (filter _ _) as [| sp'' sps''] eqn:hf; tc.
      destruct (allPredictionsEqual sp'' sps'') eqn:ha'; tc.
      inv hl.
      exists wpre; exists []; split; auto.
      intros orig_sp curr_sp hin hm.
      eapply hi in hin; eauto.
      pose proof hm as hm'.
      apply mc_multistep_succ_final_config in hm'; auto.
      pose proof (filter_In) as hfi.
      assert (hand : In curr_sp (sp' :: sps') /\ finalConfig curr_sp = true) by firstorder.
      apply hfi in hand.
      rewrite hf in hand.
      erewrite mc_multistep_preserves_label with
          (sp := orig_sp) (sp' := curr_sp); eauto.
      erewrite allPredictionEqual_in; eauto.
  - destruct curr_sps as [| sp' sps']; tc.
    destruct (allPredictionsEqual sp' sps') eqn:ha.
    + inv hl.
      exists wpre; exists (t :: wsuf'); split; auto.
      intros orig_sp curr_sp hin hm.
      eapply hi in hin; eauto.
      erewrite mc_multistep_preserves_label with
          (sp := orig_sp) (sp' := curr_sp); eauto.
      erewrite allPredictionEqual_in; eauto.
    + destruct (move _ _ _) as [msg | sps_after_mv] eqn:hm; tc.
      destruct (closure _ _) as [msg | sps_after_mv_cl_step] eqn:hc; tc.
      eapply IH with (wpre := wpre ++ [t]) in hl; eauto.
      * destruct hl as [wpre' [wsuf'' [heq hall]]].
        exists wpre'; exists wsuf''; split; auto.
        rewrite <- heq; apps.
      * intros.
        eapply move_closure_code_refines_relation; eauto.
        apps.
Qed.

Lemma subparser_complete_starts_true :
  forall g sp sp' sps w,
    In sp sps
    -> move_closure_multistep g sp w sp' w
    -> In sp' sps.
Proof.
  intros g sp sp' sps w hi hm.
  apply mcms_words_eq_subparser_eq in hm; subst; auto.
Qed.

Inductive stable_config : location_stack -> Prop :=
| SC_empty :
    forall o pre,
    stable_config (Loc o pre [], [])
| SC_terminal :
    forall o pre a suf frs,
      stable_config (Loc o pre (T a :: suf), frs).

Lemma stable_config_recognize_nil_mcms :
  forall g sp,
    stable_config sp.(stack)
    -> gamma_recognize g (unprocStackSyms sp.(stack)) []
    -> move_closure_multistep g sp [] sp [].
Proof.
  intros g sp hs hg.
  destruct sp as [av pred stk].
  inv hs.
  - simpl in H.  subst. constructor.
  - simpl in H. subst.
    simpl in hg.
    inv hg.
    inv H2.
    simpl in H1.
    inv H1.
Qed.

(* refactor *)
Lemma exists_closure_multistep_target' :
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
  destruct sp as [av pred ([o pre suf], frs)].
  destruct suf as [| [a | x] suf].
  - destruct frs as [| fr' frs].
    + eexists; split.
      * constructor.
      * auto.
    + inv hw.
      specialize IH with (sp := Sp (NtSet.add x av) pred (Loc xo (pre0 ++ [NT x]) suf, frs)).
      edestruct IH as [sp' [hcm hg']]; eauto.
      * eapply spClosureStep_meas_lt; eauto.
        -- unfold spClosureStep; dms; tc; eauto.
        -- apply in_eq.
      * apply lex_nat_pair_wf.
      * simpl.
        inv H5.
        -- constructor.
        -- constructor; auto.
           apps.
      * eapply return_preserves_unavailable_nts_invar; eauto. 
        constructor; auto.
      * eexists; split. 
        -- eapply CMS_trans; eauto.
        -- auto.
  - eexists; split. 
    + eapply CMS_terminal.
    + auto.
  - inv hg.
    inv H1.
    specialize IH with (sp := Sp (NtSet.remove x av) pred (Loc (Some x) [] ys, (Loc o pre (NT x :: suf) :: frs))).
    edestruct IH as [sp' [hcm hg']]; eauto.
    + eapply spClosureStep_meas_lt; eauto.
      * unfold spClosureStep; dmeqs h; tc.
        -- exfalso. clear IH. clear hlt. clear a'.
           simpl in hu.
           apply NtSet.mem_spec in h0.
           apply hu in h0; auto.
           ++ destruct h0 as [hng [frs_pre [fr_cr [frs_suf [suf' [heq [hp heq']]]]]]]; subst.
              simpl in hw.
              assert (happ : (Loc o pre (NT x :: suf)) :: frs_pre ++ fr_cr :: frs_suf =
                             (Loc o pre (NT x :: suf) :: frs_pre ++ [fr_cr]) ++ frs_suf).
              (* lemma *)
              { simpl; apps. }
              rewrite happ in hw.
              apply locations_wf_app_l in hw.
              eapply stack_configuration_repr_nullable_path with (y := x) in hw; sis; eauto.
              eapply hn; eauto.
           ++ unfold not; intros H. apply NtSet.mem_spec in H; tc.
        -- apply lhs_mem_allNts_true in H0; tc.
      * apply in_map_iff.
        eexists; split; eauto.
        apply rhssForNt_in_grammar_iff; auto.
    + apply lex_nat_pair_wf.
    + eapply push_preserves_locations_wf_invar; eauto. 
      apply rhssForNt_in_grammar_iff; auto. 
    + eapply push_preserves_unavailable_nts_invar; eauto.
    + simpl.
      apply gamma_recognize_app; auto.
    + exists sp'; split.
      * econstructor; eauto.
        constructor; auto.
        simpl in hu.
        destruct (In_dec x av).
        -- auto.
        -- exfalso. 
           apply hu in n.
           ++ firstorder.
              subst.
              assert (happ : (Loc o pre (NT x :: suf)) :: x0  ++ x1 :: x2 =
                             (Loc o pre (NT x :: suf) :: x0 ++ [x1]) ++ x2).
              (* lemma *)
              { simpl; apps. }
              simpl in hw.
              rewrite happ in hw.
              apply locations_wf_app_l in hw.
              eapply stack_configuration_repr_nullable_path with (y := x) in hw; sis; eauto.
              eapply hn; eauto.
           ++ apply NtSet.mem_spec. 
              eapply lhs_mem_allNts_true; eauto. 
      * auto.
Qed.

Lemma exists_closure_multistep_target :
  forall (g  : grammar)
         (sp : subparser)
         (w  : list token),
    no_left_recursion g
    -> lstack_wf g sp.(stack)
    -> unavailable_nts_invar g sp
    -> gamma_recognize g (unprocStackSyms sp.(stack)) w
    -> exists sp',
        closure_multistep g sp sp'
        /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w.
Proof.
  intros; eapply exists_closure_multistep_target'; eauto; apply lex_nat_pair_wf.
Qed.
  
Lemma stable_config_recognize_cons_move :
  forall g sp t w',
    stable_config sp.(stack)
    -> gamma_recognize g (unprocStackSyms sp.(stack)) (t :: w')
    -> exists sp',
        move_step g sp (t :: w') sp' w'.
Proof.
  intros g sp t w' hs hg.
  destruct sp as [av pred stk].
  inv hs.
  - simpl in H; subst. inv hg. 
  - simpl in H; subst. inv hg.
    inv H2. simpl in H1. inv H1.
    eexists; constructor.
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
  intros g sp sp' t w' hm hg.
  inv hm.
  sis.
  inv hg.
  inv H2.
  sis.
  inv H1; auto.
Qed.

Lemma stable_config_after_closure_multistep :
  forall g sp sp',
    closure_multistep g sp sp'
    -> stable_config sp'.(stack).
Proof.
  intros g sp sp' hc.
  induction hc; try constructor; auto.
Qed.

Lemma closure_step_preserves_lstack_wf_invar :
  forall g sp sp',
    closure_step g sp sp'
    -> lstack_wf g sp.(stack)
    -> lstack_wf g sp'.(stack).
Proof.
  intros g sp sp' hc hw.
  inv hc; sis; auto.
  inv hw; sis.
  inv H8; auto.
  constructor; auto.
  apps.
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

Lemma unproc_syms_recognize_move_closure_multistep :
  forall g w sp,
    no_left_recursion g
    -> stable_config sp.(stack)
    -> lstack_wf g sp.(stack)
    -> gamma_recognize g (unprocStackSyms sp.(stack)) w
    -> exists sp'', 
      move_closure_multistep g sp w sp'' [].
Proof.
  intros g w; induction w as [| t w' IH]; intros sp hn hs hw hg.
  - apply stable_config_recognize_nil_mcms in hg; eauto.
  - assert (hm : exists sp', move_step g sp (t :: w') sp' w'). 
    { apply stable_config_recognize_cons_move in hg; auto. }
    destruct hm as [sp' hm].
    assert (hw' : lstack_wf g sp'.(stack)).
    { eapply move_step_preserves_lstack_wf_invar; eauto. }
    assert (hu : unavailable_nts_invar g sp').
    { eapply unavailable_nts_invar_holds_after_move_step; eauto. }
    assert (hc : exists sp'', closure_multistep g sp' sp''
                              /\ gamma_recognize g (unprocStackSyms sp''.(stack)) w').
    { eapply exists_closure_multistep_target; eauto.
      eapply move_step_preserves_unprocStackSyms_recognize; eauto. }
    destruct hc as [sp'' [hc hg'']].
    apply IH in hg''; auto.
    + destruct hg'' as [sp''' hmcms].
      exists sp'''; econstructor; eauto.
    + eapply stable_config_after_closure_multistep; eauto.
    + eapply closure_multistep_preserves_lstack_wf_invar; eauto.
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
  eapply llPredict'_succ_labels_eq with (wpre := []) (orig_sps := sps) in hl; eauto.
  - destruct hl as [wpre [wsuf [heq hall]]]; sis.
    assert (hi : In (Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) 
                    (map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) 
                         (rhssForNt g x))).
    { apply in_map_iff. 
      eexists; split; eauto.
      apply rhssForNt_in_grammar_iff; auto. }
    assert (hex : exists sp',
               closure_multistep g (Sp (allNts g) rhs (Loc (Some x) [] rhs, Loc o pre (NT x :: suf) :: frs)) sp'
               /\ gamma_recognize g (unprocStackSyms sp'.(stack)) w).
    { eapply exists_closure_multistep_target; eauto.
      - sis. apply push_preserves_locations_wf_invar; auto.
        apply rhssForNt_in_grammar_iff; auto.
      - (* lemma *)
        unfold unavailable_nts_invar. unfold unavailable_nts_are_open_calls.
        intros.
        ND.fsetdec. }
    destruct hex as [sp' [hcm hg']].
    assert (h_viable_cand : In sp' sps).
    { eapply acr_map_inr_all_inr in hs; eauto.
      destruct hs as [sps' [hspc hall']].
      apply hall'.
      eapply spClosure_func_refines_rel; eauto. }
    apply unproc_syms_recognize_move_closure_multistep in hg'; eauto.
    + destruct hg' as [sp'' hmcms].
      pose proof move_closure_multistep_backtrack as hb.
      assert (hpred : sp''.(prediction) = rhs).
      { eapply closure_multistep_preserves_label in hcm; sis; subst.
        eapply mc_multistep_preserves_label in hmcms; auto. }
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
    apply mcms_words_eq_subparser_eq in hm; subst; auto.
Qed.

