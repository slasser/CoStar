Require Import Arith List Omega PeanoNat Program.Wf String.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

(* Hide an alternative definition of "sum" from NtSet *)
Definition sum := Datatypes.sum.

Definition location_stack := (location * list location)%type.

Record subparser := Sp { avail      : NtSet.t
                       ; prediction : list symbol
                       ; stack      : location_stack
                       }.

(* Error values that the prediction mechanism can return *)
Inductive prediction_error :=
| SpInvalidState  : prediction_error
| SpLeftRecursion : nonterminal -> prediction_error.

(* "move" operation *)

Inductive subparser_move_result :=
| SpMoveSucc   : subparser -> subparser_move_result
| SpMoveReject : subparser_move_result
| SpMoveError  : prediction_error -> subparser_move_result.

Definition moveSp (g : grammar) (tok : token) (sp : subparser) : subparser_move_result :=
  match sp with
  | Sp _ pred stk =>
    match stk with
    | (Loc _ _ [], [])                => SpMoveReject
    | (Loc _ _ [], _ :: _)            => SpMoveError SpInvalidState
    | (Loc _ _ (NT _ :: _), _)        => SpMoveError SpInvalidState
    | (Loc xo pre (T a :: suf), locs) =>
      match tok with
      | (a', _) =>
        if t_eq_dec a' a then
          SpMoveSucc (Sp (allNts g) pred (Loc xo (pre ++ [T a]) suf, locs))
        else
          SpMoveReject
      end
    end
  end.

Definition move_result := sum prediction_error (list subparser).

Fixpoint aggrMoveResults (smrs : list subparser_move_result) : 
  move_result :=
  match smrs with
  | []           => inr []
  | smr :: smrs' =>
    match (smr, aggrMoveResults smrs') with
    | (SpMoveError e, _)       => inl e
    | (_, inl e)               => inl e
    | (SpMoveSucc sp, inr sps) => inr (sp :: sps)
    | (SpMoveReject, inr sps)  => inr sps
    end
  end.

Definition move (g : grammar) (tok : token) (sps : list subparser) : move_result :=
  aggrMoveResults (map (moveSp g tok) sps).

(* "closure" operation *)

Inductive subparser_closure_step_result :=
| SpClosureStepDone  : subparser_closure_step_result
| SpClosureStepK     : list subparser -> subparser_closure_step_result
| SpClosureStepError : prediction_error -> subparser_closure_step_result.

Definition spClosureStep (g : grammar) (sp : subparser) : 
  subparser_closure_step_result :=
  match sp with
  | Sp av pred (loc, locs) =>
    match loc with
    | Loc _ _ [] =>
      match locs with
      | []                        => SpClosureStepDone
      | (Loc _ _ []) :: _         => SpClosureStepError SpInvalidState
      | (Loc _ _ (T _ :: _)) :: _ => SpClosureStepError SpInvalidState
      | (Loc xo_cr pre_cr (NT x :: suf_cr)) :: locs_tl =>
        let stk':= (Loc xo_cr (pre_cr ++ [NT x]) suf_cr, locs_tl) 
        in  SpClosureStepK [Sp (NtSet.add x av) pred stk']
      end
    | Loc _ _ (T _ :: _)       => SpClosureStepDone
    | Loc xo pre (NT x :: suf) =>
      if NtSet.mem x av then
        let sps' := map (fun rhs => Sp (NtSet.remove x av) 
                                       pred 
                                       (Loc (Some x) [] rhs, loc :: locs))
                        (rhssForNt g x)
        in  SpClosureStepK sps'
      else if NtSet.mem x (allNts g) then
             SpClosureStepError (SpLeftRecursion x)
           else
             SpClosureStepK []
    end
  end.

Definition closure_result := sum prediction_error (list subparser).

Fixpoint aggrClosureResults (crs : list closure_result) : closure_result :=
  match crs with
  | [] => inr []
  | cr :: crs' =>
    match (cr, aggrClosureResults crs') with
    | (inl e, _)          => inl e
    | (inr _, inl e)      => inl e
    | (inr sps, inr sps') => inr (sps ++ sps')
    end
  end.

Definition meas (g : grammar) (sp : subparser) : nat * nat :=
  match sp with
  | Sp av _ stk =>
    let m := maxRhsLength g in
    let e := NtSet.cardinal av               
    in  (stackScore stk (1 + m) e, stackHeight stk)
  end.

Lemma spClosureStep_meas_lt :
  forall (g      : grammar)
         (sp sp' : subparser)
         (sps'   : list subparser),
    spClosureStep g sp = SpClosureStepK sps'
    -> In sp' sps'
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' sps' hs hi; unfold spClosureStep in hs; dmeqs h; tc; inv hs; try solve [inv hi]; unfold meas.
  - apply in_singleton_eq in hi; subst.
    pose proof stackScore_le_after_return' as hle.
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq].
    + apply pair_fst_lt; eauto.
    + rewrite heq; apply pair_snd_lt; auto.
  - apply in_map_iff in hi.
    destruct hi as [rhs [heq hi]]; subst.
    apply pair_fst_lt.
    eapply stackScore_lt_after_push; simpl; eauto.
    apply NtSet.mem_spec; auto.
Defined.

Lemma acc_after_step :
  forall g sp sp' sps',
    spClosureStep g sp = SpClosureStepK sps'
    -> In sp' sps'
    -> Acc lex_nat_pair (meas g sp)
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g so sp' sps' heq hi ha.
  eapply Acc_inv; eauto.
  eapply spClosureStep_meas_lt; eauto.
Defined.

Fixpoint spClosure (g  : grammar) 
                   (sp : subparser) 
                   (a  : Acc lex_nat_pair (meas g sp)) : closure_result :=
  match spClosureStep g sp as r return spClosureStep g sp = r -> _ with
  | SpClosureStepDone     => fun _  => inr [sp]
  | SpClosureStepError e  => fun _  => inl e
  | SpClosureStepK sps'   => 
    fun hs => 
      let crs := 
          dmap sps' (fun sp' hin => spClosure g sp' (acc_after_step _ _ _ hs hin a))
      in  aggrClosureResults crs
  end eq_refl.

Definition closure (g : grammar) (sps : list subparser) :
  sum prediction_error (list subparser) :=
  aggrClosureResults (map (fun sp => spClosure g sp (lex_nat_pair_wf _)) sps).

(* LL prediction *)

Inductive prediction_result :=
| PredSucc   : list symbol      -> prediction_result
| PredAmbig  : list symbol      -> prediction_result
| PredReject :                     prediction_result
| PredError  : prediction_error -> prediction_result.

Definition finalConfig (sp : subparser) : bool :=
  match sp with
  | Sp _ _ (Loc _ _ [], []) => true
  | _                       => false
  end.

Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : bool :=
  allEqual _ beqGamma sp.(prediction) (map prediction sps).

Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
  match filter finalConfig sps with
  | []         => PredReject
  | sp :: sps' => 
    if allPredictionsEqual sp sps' then
      PredSucc sp.(prediction)
    else
      PredAmbig sp.(prediction)
  end.

Fixpoint llPredict' (g : grammar) (ts : list token) (sps : list subparser) : prediction_result :=
  match ts with
  | []       => handleFinalSubparsers sps
  | t :: ts' =>
    match sps with 
    | []         => PredReject
    | sp :: sps' =>
      if allPredictionsEqual sp sps' then
        PredSucc sp.(prediction)
      else
        match move g t sps with
        | inl msg => PredError msg
        | inr mv  =>
          match closure g mv with
          | inl msg => PredError msg
          | inr cl  => llPredict' g ts' cl
          end
        end
    end
  end.

Definition startState (g : grammar) (x : nonterminal) (stk : location_stack) :
  sum prediction_error (list subparser) :=
  match stk with
  | (loc, locs) =>
    let init := map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, loc :: locs))
                    (rhssForNt g x)
    in  closure g init
  end.

Definition llPredict (g : grammar) (x : nonterminal) (stk : location_stack)
                     (ts : list token) : prediction_result :=
  match startState g x stk with
  | inl msg => PredError msg
  | inr sps => llPredict' g ts sps
  end.

(* LEMMAS *)

Lemma handleFinalSubparsers_success_from_subparsers :
  forall sps gamma,
    handleFinalSubparsers sps = PredSucc gamma
    -> exists sp, In sp sps /\ sp.(prediction) = gamma.
Proof.
  intros sps gamma hh; unfold handleFinalSubparsers in hh.
  dmeqs h; tc; inv hh.
  eexists; split; eauto.
  eapply filter_cons_in; eauto.
Qed.

Lemma handleFinalSubparsers_ambig_from_subparsers :
  forall sps gamma,
    handleFinalSubparsers sps = PredAmbig gamma
    -> exists sp, In sp sps /\ sp.(prediction) = gamma.
Proof.
  intros sps gamma hh.
  unfold handleFinalSubparsers in hh.
  dmeqs h; tc; inv hh.
  eexists; split; eauto.
  eapply filter_cons_in; eauto.
Qed.

Lemma move_unfold :
  forall g t sps,
    move g t sps = aggrMoveResults (map (moveSp g t) sps).
Proof. 
  auto. 
Qed.

Lemma aggrMoveResults_succ_in_input :
  forall (smrs : list subparser_move_result)
         (sp   : subparser)
         (sps  : list subparser),
    aggrMoveResults smrs = inr sps
    -> In sp sps
    -> In (SpMoveSucc sp) smrs.
Proof.
  intros smrs sp.
  induction smrs as [| smr smrs' IH]; intros sps ha hi; sis.
  - inv ha; inv hi.
  - destruct smr as [sp' | | e];
    destruct (aggrMoveResults smrs') as [e' | sps']; tc; inv ha.
    + inv hi; firstorder.
    + firstorder.
Qed.

Lemma aggrMoveResults_error_in_input :
  forall (smrs : list subparser_move_result)
         (e    : prediction_error),
    aggrMoveResults smrs = inl e
    -> In (SpMoveError e) smrs.
Proof.
  intros smrs e ha.
  induction smrs as [| smr smrs' IH]; sis; tc.
  destruct smr as [sp' | | e'];
  destruct (aggrMoveResults smrs') as [e'' | sps']; tc; inv ha; eauto.
Qed.

Lemma moveSp_preserves_prediction :
  forall g t sp sp',
    moveSp g t sp = SpMoveSucc sp'
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros g t sp sp' hm; unfold moveSp in hm.
  dms; tc; subst; inv hm; auto.
Qed.

Lemma move_preserves_prediction :
  forall g t sp' sps sps',
    move g t sps = inr sps'
    -> In sp' sps'
    -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
Proof.
  intros g t sp' sps sps' hm hi.
  unfold move in hm.
  eapply aggrMoveResults_succ_in_input in hm; eauto.
  eapply in_map_iff in hm; destruct hm as [sp [hmsp hi']].
  eexists; split; eauto.
  eapply moveSp_preserves_prediction; eauto.
Qed.

Lemma spClosure_unfold :
  forall g sp a,
    spClosure g sp a =
    match spClosureStep g sp as r return spClosureStep g sp = r -> _ with
    | SpClosureStepDone     => fun _  => inr [sp]
    | SpClosureStepError e  => fun _  => inl e
    | SpClosureStepK sps'   => 
      fun hs => 
        let crs := 
            dmap sps' (fun sp' hin => spClosure g sp' (acc_after_step _ _ _ hs hin a))
        in  aggrClosureResults crs
    end eq_refl.
Proof.
  intros g sp a; destruct a; auto.
Qed.

Lemma spClosure_cases' :
  forall (g   : grammar)
         (sp  : subparser)
         (a   : Acc lex_nat_pair (meas g sp))
         (sr  : subparser_closure_step_result)
         (cr  : closure_result)
         (heq : spClosureStep g sp = sr),
    match sr as r return spClosureStep g sp = r -> closure_result with
    | SpClosureStepDone     => fun _  => inr [sp]
    | SpClosureStepError e  => fun _  => inl e
    | SpClosureStepK sps'   => 
      fun hs => 
        let crs := 
            dmap sps' (fun sp' hin => spClosure g sp' (acc_after_step _ _ _ hs hin a))
        in  aggrClosureResults crs
    end heq = cr
    -> match cr with
       | inl e => 
         sr = SpClosureStepError e
         \/ exists (sps : list subparser)
                   (hs  : spClosureStep g sp = SpClosureStepK sps)
                   (crs : list closure_result),
             crs = dmap sps (fun sp' hi => 
                               spClosure g sp' (acc_after_step _ _ _ hs hi a))
             /\ aggrClosureResults crs = inl e
       | inr sps => 
         (sr = SpClosureStepDone
          /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (hs   : spClosureStep g sp = SpClosureStepK sps')
                   (crs  : list closure_result),
             crs = dmap sps' (fun sp' hi => 
                                spClosure g sp' (acc_after_step _ _ _ hs hi a))
             /\ aggrClosureResults crs = inr sps
       end.
Proof.
  intros g sp a sr cr heq.
  destruct sr as [ | sps | e];
  destruct cr as [e' | sps']; intros heq'; tc;
  try solve [inv heq'; auto | eauto 6].
Qed.

Lemma spClosure_cases :
  forall (g  : grammar)
         (sp : subparser)
         (a  : Acc lex_nat_pair (meas g sp))
         (cr : closure_result),
    spClosure g sp a = cr
    -> match cr with
       | inl e => 
         spClosureStep g sp = SpClosureStepError e
         \/ exists (sps : list subparser)
                   (hs  : spClosureStep g sp = SpClosureStepK sps)
                   (crs : list closure_result),
             crs = dmap sps (fun sp' hi => 
                               spClosure g sp' (acc_after_step _ _ _ hs hi a))
             /\ aggrClosureResults crs = inl e
       | inr sps => 
         (spClosureStep g sp = SpClosureStepDone
          /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (hs   : spClosureStep g sp = SpClosureStepK sps')
                   (crs  : list closure_result),
             crs = dmap sps' (fun sp' hi => 
                                spClosure g sp' (acc_after_step _ _ _ hs hi a))
             /\ aggrClosureResults crs = inr sps
       end.
Proof.
  intros g sp a cr hs; subst.
  rewrite spClosure_unfold.
  eapply spClosure_cases'; eauto.
Qed.

Lemma spClosure_success_cases :
  forall g sp a sps,
    spClosure g sp a = inr sps
    -> (spClosureStep g sp = SpClosureStepDone
        /\ sps = [sp])
       \/ exists (sps' : list subparser)
                 (hs   : spClosureStep g sp = SpClosureStepK sps')
                 (crs  : list closure_result),
        crs = dmap sps' (fun sp' hi => 
                           spClosure g sp' (acc_after_step _ _ _ hs hi a))
        /\ aggrClosureResults crs = inr sps.
Proof.
  intros g sp a sps hs; apply spClosure_cases with (cr := inr sps); auto.
Qed.

Lemma spClosure_error_cases :
  forall g sp a e,
    spClosure g sp a = inl e
    -> spClosureStep g sp = SpClosureStepError e
       \/ exists (sps : list subparser)
                 (hs  : spClosureStep g sp = SpClosureStepK sps)
                 (crs : list closure_result),
        crs = dmap sps (fun sp' hi => 
                          spClosure g sp' (acc_after_step _ _ _ hs hi a))
        /\ aggrClosureResults crs = inl e.
Proof.
  intros g sp a e hs; apply spClosure_cases with (cr := inl e); auto.
Qed.
                   
Lemma aggrClosureResults_succ_in_input:
  forall (crs : list closure_result) 
         (sp  : subparser)
         (sps : list subparser),
    aggrClosureResults crs = inr sps 
    -> In sp sps 
    -> exists sps',
        In (inr sps') crs
        /\ In sp sps'.
Proof.
  intros crs; induction crs as [| cr crs IH]; intros sp sps ha hi; simpl in ha.
  - inv ha; inv hi.
  - destruct cr as [e | sps'];
    destruct (aggrClosureResults crs) as [e' | sps'']; tc; inv ha.
    apply in_app_or in hi.
    destruct hi as [hi' | hi''].
    + eexists; split; eauto.
      apply in_eq.
    + apply IH in hi''; auto.
      destruct hi'' as [sps [hi hi']].
      eexists; split; eauto.
      apply in_cons; auto.
Qed.

Lemma aggrClosureResults_error_in_input:
  forall (crs : list closure_result) 
         (e   : prediction_error),
    aggrClosureResults crs = inl e
    -> In (inl e) crs.
Proof.
  intros crs e ha; induction crs as [| cr crs IH]; sis; tc.
  destruct cr as [e' | sps].
  - inv ha; auto.
  - destruct (aggrClosureResults crs) as [e' | sps']; tc; auto.
Qed.

Lemma spClosureStep_preserves_prediction :
  forall g sp sp' sps',
    spClosureStep g sp = SpClosureStepK sps'
    -> In sp' sps'
    -> sp.(prediction) = sp'.(prediction).
Proof.
  intros g sp sp' sps' hs hi.
  unfold spClosureStep in hs; dms; tc; inv hs.
  - apply in_singleton_eq in hi; subst; auto.
  - apply in_map_iff in hi.
    destruct hi as [rhs [heq hi]]; subst; auto.
  - inv hi.
Qed.

Lemma spClosure_preserves_prediction :
  forall g pair (a : Acc lex_nat_pair pair) sp a' sp' sps',
    pair = meas g sp
    -> spClosure g sp a' = inr sps'
    -> In sp' sps'
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros g pair a.
  induction a as [pair hlt IH].
  intros sp a' sp' sps' heq hs hi; subst.
  apply spClosure_success_cases in hs.
  destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
  - apply in_singleton_eq in hi; subst; auto.
  - eapply aggrClosureResults_succ_in_input in heq'; eauto.
    destruct heq' as [sps [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp'' [hi''' [_ heq]]].
    eapply IH in heq; subst; eauto.
    + apply spClosureStep_preserves_prediction with (sp' := sp'') in hs; auto.
      rewrite hs; auto.
    + eapply spClosureStep_meas_lt; eauto.
Qed.

Lemma closure_preserves_prediction :
  forall g sp' sps sps',
    closure g sps = inr sps'
    -> In sp' sps'
    -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
Proof.
  intros g sp' sps sps' hc hi.
  eapply aggrClosureResults_succ_in_input in hc; eauto.
  destruct hc as [sps'' [hi' hi'']].
  apply in_map_iff in hi'; destruct hi' as [sp [hspc hi''']].
  eexists; split; eauto.
  eapply spClosure_preserves_prediction; eauto.
  apply lex_nat_pair_wf.
Qed.

Lemma llPredict'_success_result_in_original_subparsers :
  forall g ts gamma sps,
    llPredict' g ts sps = PredSucc gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts_tl IH]; intros sps hl; simpl in hl.
  - eapply handleFinalSubparsers_success_from_subparsers; eauto.
  - destruct sps as [| sp_hd sps_tl] eqn:hs; tc.
    destruct (allPredictionsEqual sp_hd sps_tl) eqn:Ha.
    + inv hl; eexists; split; eauto.
      apply in_eq.
    + rewrite <- hs in *.
      destruct (move g t _) as [msg | sps'] eqn:hm; tc.
      destruct (closure g sps') as [msg | sps''] eqn:hc; tc. 
      apply IH in hl; destruct hl as [sp'' [hin'' heq]]; subst.
      eapply closure_preserves_prediction in hc; eauto.
      destruct hc as [sp' [hin' heq]]; rewrite heq.
      eapply move_preserves_prediction in hm; eauto.
      destruct hm as [? [? ?]]; eauto.
Qed.

Lemma llPredict'_ambig_result_in_original_subparsers :
  forall g ts gamma sps,
    llPredict' g ts sps = PredAmbig gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts_tl IH]; intros sps hl; simpl in hl.
  - eapply handleFinalSubparsers_ambig_from_subparsers; eauto.
  - destruct sps as [| sp_hd sps_tl] eqn:hs; tc.
    destruct (allPredictionsEqual sp_hd sps_tl) eqn:ha; tc.
    rewrite <- hs in *.
    destruct (move g t _) as [msg | sps'] eqn:hm; tc.
    destruct (closure g sps') as [msg | sps''] eqn:hc; tc. 
    apply IH in hl; destruct hl as [sp'' [hin'' heq]]; subst.
    eapply closure_preserves_prediction in hc; eauto.
    destruct hc as [sp' [hin' heq]]; rewrite heq.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [sp [Hin Heq]]; eauto.
Qed.

Lemma startState_sp_prediction_in_rhssForNt :
  forall g x stk sp' sps',
    startState g x stk = inr sps'
    -> In sp' sps'
    -> In sp'.(prediction) (rhssForNt g x).
Proof.
  intros g x (fr, frs) sp' sps' hf hi.
  unfold startState in hf.
  eapply closure_preserves_prediction in hf; eauto.
  destruct hf as [sp [hin heq]].
  apply in_map_iff in hin.
  destruct hin as [gamma [hin heq']]; subst.
  rewrite heq; auto.
Qed.

Lemma llPredict_succ_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredSucc gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma hp; unfold llPredict in hp.
  dmeq hs; tc.
  apply llPredict'_success_result_in_original_subparsers in hp.
  destruct hp as [sp [hin heq]]; subst.
  eapply startState_sp_prediction_in_rhssForNt; eauto.
Qed.

Lemma llPredict_ambig_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredAmbig gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma hf.
  unfold llPredict in hf.
  dmeq hs; tc.
  apply llPredict'_ambig_result_in_original_subparsers in hf.
  destruct hf as [sp [hin heq]]; subst.
  eapply startState_sp_prediction_in_rhssForNt; eauto.
Qed.

Lemma llPredict_succ_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredSucc ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply rhssForNt_in_grammar.
  eapply llPredict_succ_in_rhssForNt; eauto.
Qed.

Lemma llPredict_ambig_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredAmbig ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply rhssForNt_in_grammar.
  eapply llPredict_ambig_in_rhssForNt; eauto.
Qed.

(* A WELL-FORMEDNESS PREDICATE OVER A LOCATION STACK *)

(* The stack predicate is defined in terms of the following
   predicate over a list of locations *)
Inductive locations_wf (g : grammar) : list location -> Prop :=
| WF_nil :
    locations_wf g []
| WF_bottom :
    forall xo pre suf,
      locations_wf g [Loc xo pre suf]
| WF_upper :
    forall x xo pre pre' suf suf' locs,
      In (x, pre' ++ suf') g
      -> locations_wf g (Loc xo pre (NT x :: suf) :: locs)
      -> locations_wf g (Loc (Some x) pre' suf'   ::
                         Loc xo pre (NT x :: suf) :: locs).

Hint Constructors locations_wf.

(* The stack well-formedness predicate *)
Definition lstack_wf (g : grammar) (stk : location_stack) : Prop :=
  match stk with
  | (loc, locs) => locations_wf g (loc :: locs)
  end.

(* Lift the predicate to a list of subparsers *)
Definition all_sp_stacks_wf (g : grammar) (sps : list subparser) : Prop :=
  forall sp, In sp sps -> lstack_wf g sp.(stack).

(* Lemmas about the well-formedness predicate *)

Lemma locations_wf_app :
  forall g l,
    locations_wf g l
    -> forall p s,
      l = p ++ s
      -> locations_wf g p /\ locations_wf g s.
Proof.
  intros g l hw.
  induction hw; intros p s heq.
  - symmetry in heq; apply app_eq_nil in heq.
    destruct heq; subst; auto.
  - destruct p as [| fr p]; sis; subst; auto.
    apply cons_inv_eq in heq.
    destruct heq as [hh ht].
    apply app_eq_nil in ht; destruct ht; subst; auto.
  - destruct p as [| fr  p]; sis; subst; auto.
    destruct p as [| fr' p]; sis; subst; inv heq; auto.
    specialize (IHhw (Loc xo pre (NT x :: suf):: p) s).
    destruct IHhw as [hs hp]; auto.
Qed.

Lemma locations_wf_app_l :
  forall g p s,
    locations_wf g (p ++ s)
    -> locations_wf g p.
Proof.
  intros g p s hw.
  eapply locations_wf_app in hw; eauto.
  firstorder.
Qed.

Lemma locations_wf_tl :
  forall g h t,
    locations_wf g (h :: t)
    -> locations_wf g t.
Proof.
  intros g h t hw.
  rewrite cons_app_singleton in hw.
  eapply locations_wf_app in hw; eauto.
  firstorder.
Qed.

Lemma return_preserves_locations_wf_invar :
  forall g o o_cr pre pre_cr suf_cr x locs,
    locations_wf g (Loc o pre [] :: Loc o_cr pre_cr (NT x :: suf_cr) :: locs)
    -> locations_wf g (Loc o_cr (pre_cr ++ [NT x]) suf_cr :: locs).
Proof.
  intros g o o_cr pre pre_cr suf_cr x locs hw.
  inversion hw as [ | o' pre' suf' hw' | x' o' pre' pre'' suf suf' locs' hi hw']; subst; clear hw.
  inv hw'; constructor; auto.
  rewrite <- app_assoc; auto.
Qed.

Lemma push_preserves_locations_wf_invar :
  forall g o pre suf x rhs locs,
    In rhs (rhssForNt g x)
    -> locations_wf g (Loc o pre (NT x :: suf) :: locs)
    -> locations_wf g (Loc (Some x) [] rhs :: Loc o pre (NT x :: suf) :: locs).
Proof.
  intros; constructor; auto.
  apply rhssForNt_in_grammar; auto.
Qed.

Lemma consume_preserves_locations_wf_invar :
  forall g o pre suf a locs,
    locations_wf g (Loc o pre (T a :: suf) :: locs)
    -> locations_wf g (Loc o (pre ++ [T a]) suf :: locs).
Proof.
  intros g o pre suf a locs hw.
  inversion hw as [ | o' pre' suf' hw' | x o' pre' pre'' suf' suf'' locs' hi hw']; subst; clear hw; auto.
  rewrite cons_app_singleton in hi.
  rewrite app_assoc in hi; auto.
Qed.

Lemma spClosureStep_preserves_lstack_wf_invar :
  forall g sp sp' sps',
    lstack_wf g sp.(stack)
    -> spClosureStep g sp = SpClosureStepK sps'
    -> In sp' sps'
    -> lstack_wf g sp'.(stack).
Proof.
  intros g sp sp' sps' hw hs hi.
  unfold spClosureStep in hs; dms; tc; sis; inv hs.
  - apply in_singleton_eq in hi; subst; sis.
    eapply return_preserves_locations_wf_invar; eauto.
  - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
    apply push_preserves_locations_wf_invar; auto.
  - inv hi.
Qed.

(* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

(* Auxiliary definition *)
Definition processed_symbols_all_nullable (g : grammar) (frs : list location) : Prop :=
  Forall (fun fr => nullable_gamma g fr.(rpre)) frs.

Hint Unfold processed_symbols_all_nullable.
Hint Constructors Forall.

(* The invariant itself *)
Definition unavailable_nts_are_open_calls g av stk : Prop :=
  match stk with
  | (fr, frs) =>
    forall (x : nonterminal),
      NtSet.In x (allNts g)
      -> ~ NtSet.In x av
      -> nullable_gamma g fr.(rpre)
         /\ (exists frs_pre fr_cr frs_suf suf,
                frs = frs_pre ++ fr_cr :: frs_suf
                /\ processed_symbols_all_nullable g frs_pre
                /\ fr_cr.(rsuf) = NT x :: suf)
  end.

(* Lift the invariant to a subparser *)
Definition unavailable_nts_invar g sp :=
  match sp with
  | Sp av _ stk => unavailable_nts_are_open_calls g av stk
  end.

(* Lift the invariant to a list of subparsers *)
Definition sps_unavailable_nts_invar g sps : Prop :=
  forall sp, In sp sps -> unavailable_nts_invar g sp.

Lemma return_preserves_unavailable_nts_invar :
  forall g av pr o o' pre pre' suf' x fr cr cr' frs,
    fr     = Loc o pre []
    -> cr  = Loc o' pre' (NT x :: suf')
    -> cr' = Loc o' (pre' ++ [NT x]) suf'
    -> lstack_wf g (fr, cr :: frs)
    -> unavailable_nts_invar g (Sp av pr (fr, cr :: frs))
    -> unavailable_nts_invar g (Sp (NtSet.add x av) pr (cr', frs)). 
Proof.
  intros g av pr o o' pre pre' suf' x' fr cr cr' frs hfr hcr hcr' hw hu; subst.
  intros x hi hn; simpl.
  assert (hn' : ~ NtSet.In x av) by ND.fsetdec.
  apply hu in hn'; clear hu; auto.
  destruct hn' as [hng [frs_pre [fr_cr [frs_suf [suf [heq [hp heq']]]]]]].
  destruct frs_pre as [| fr' frs_pre]; sis.
  - inv heq; inv heq'; ND.fsetdec.
  - inv heq; inv hp; sis; split; eauto 8.
    apply nullable_app; auto.
    inv hw; rewrite app_nil_r in *; eauto.
Qed.

Lemma push_preserves_unavailable_nts_invar :
  forall g cr ce av pr o pre suf x rhs frs,
    cr = Loc o pre (NT x :: suf)
    -> ce = Loc (Some x) [] rhs
    -> unavailable_nts_invar g (Sp av pr (cr, frs))
    -> unavailable_nts_invar g (Sp (NtSet.remove x av) pr (ce, cr :: frs)).
Proof.
  intros g cr ce av pr o pre suf x rhs frs hcr hce hu; subst.
  intros x' hi hn; simpl; split; auto.
  unfold processed_symbols_all_nullable.
  destruct (NF.eq_dec x' x); subst.
  - exists []; repeat eexists; eauto.
  - assert (hn' : ~ NtSet.In x' av) by ND.fsetdec.
    apply hu in hn'; simpl in hn'; clear hu; auto.
    destruct hn' as
        [hng [frs_pre [fr_cr [frs_suf [suf' [heq [hp heq']]]]]]]; subst.
    exists (Loc o pre (NT x :: suf) :: frs_pre); repeat eexists; eauto.
Qed.

Lemma spClosureStep_preserves_unavailable_nts_invar :
  forall g sp sp' sps',
    lstack_wf g sp.(stack)
    -> unavailable_nts_invar g sp
    -> spClosureStep g sp = SpClosureStepK sps'
    -> In sp' sps'
    -> unavailable_nts_invar g sp'.
Proof.
  intros g sp sp' sps' hw hu hs hi.
  unfold spClosureStep in hs; dmeqs h; inv hs; tc; simpl in hw.
  - apply in_singleton_eq in hi; subst.
    eapply return_preserves_unavailable_nts_invar; eauto.
  - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
    eapply push_preserves_unavailable_nts_invar; eauto.
  - inv hi.
Qed.

(* Stuff about the unprocessed stack symbols recognize suffix invariant *)

Inductive tail_frames_recognize (g : grammar) : list location -> list token -> Prop :=
| TFR_nil :
    tail_frames_recognize g [] []
| TFR_cons :
    forall o pre x suf w w' frs,
      gamma_recognize g suf w
      -> tail_frames_recognize g frs w'
      -> tail_frames_recognize g (Loc o pre (NT x :: suf) :: frs) (w ++ w').

Hint Constructors tail_frames_recognize.

Inductive stack_recognize (g : grammar) : location_stack -> list token -> Prop :=
| SR :
    forall o pre suf w w' frs,
      gamma_recognize g suf w
      -> tail_frames_recognize g frs w'
      -> stack_recognize g (Loc o pre suf, frs) (w ++ w').

Hint Constructors stack_recognize.

Lemma stack_recognize_inv :
  forall g o pre suf frs w'',
    stack_recognize g (Loc o pre suf, frs) w''
    -> exists w w',
      w'' = w ++ w'
      /\ gamma_recognize g suf w
      /\ tail_frames_recognize g frs w'.
Proof.
  intros g o pre suf frs w'' hs; inv hs; eauto.
Qed.

Lemma gamma_recognize_nonterminal_head :
  forall g x suf w,
    gamma_recognize g (NT x :: suf) w
    -> exists rhs wpre wsuf,
      w = wpre ++ wsuf
      /\ In (x, rhs) g
      /\ gamma_recognize g rhs wpre
      /\ gamma_recognize g suf wsuf.
Proof.
  intros g x suf w hg.
  inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
  inv hs; simpl; eauto 8.
Qed.

Lemma llPredict_succ_viable_prefix :
  forall g fr o pre x suf frs w rhs,
    fr = Loc o pre (NT x :: suf)
    -> stack_recognize g (fr, frs) w
    -> llPredict g x (fr, frs) w = PredSucc rhs
    -> exists viable_prefix viable_suffix wpre wsuf,
        viable_prefix ++ viable_suffix = rhs ++ suf ++ flat_map rsuf frs
        /\ w = wpre ++ wsuf
        /\ gamma_recognize g viable_prefix wpre
        /\ gamma_recognize g viable_suffix wsuf
        /\ forall viable_prefix' viable_suffix' wpre' wsuf',
            viable_prefix ++ viable_suffix = viable_prefix' ++ viable_suffix'
            ->w = wpre' ++ wsuf'
            -> gamma_recognize g viable_prefix' wpre'
            -> gamma_recognize g viable_suffix' wsuf'
            -> viable_prefix = viable_prefix'
               /\ viable_suffix = viable_suffix'
               /\wpre = wpre' /\ wsuf = wsuf'.
Proof.
  intros g fr o pre x suf frs w rhs heq hs hl; subst.
  unfold llPredict in hl.
  destruct (startState g x _) as [| sps] eqn:hss; tc.
Admitted.

Lemma llPredict_succ_gamma_recognize :
  forall g fr o pre x suf frs rhs rhs' wpre wmid wsuf,
    fr = Loc o pre (NT x :: suf)
    -> In (x, rhs) g
    -> gamma_recognize g rhs wpre
    -> gamma_recognize g suf wmid
    -> tail_frames_recognize g frs wsuf
    -> llPredict g x (fr, frs) (wpre ++ wmid ++ wsuf) = PredSucc rhs'
    -> rhs' = rhs.
Proof.
  intros g fr o pre x suf frs rhs rhs' wpre wmid wsuf
         heq hin hg hg' ht hl; subst.
  unfold llPredict in hl.
  destruct (startState g x _) as [| sps] eqn:hss; tc.
  unfold llPredict' in hl.
Abort.  

Lemma llPredict_succ_gamma_recognize :
  forall g fr frs o pre x suf w rhs,
    fr = Loc o pre (NT x :: suf)
    -> stack_recognize g (fr, frs) w
    -> llPredict g x (fr, frs) w = PredSucc rhs
    -> True.
Proof. 
Abort.  