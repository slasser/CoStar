Require Import Arith Bool List Omega PeanoNat Program.Wf String.
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

Fixpoint llPredict' (g : grammar) (sps : list subparser) (ts : list token) : prediction_result :=
  match sps with
  | []         => PredReject
  | sp :: sps' =>
    if allPredictionsEqual sp sps' then
      PredSucc sp.(prediction)
    else
      match ts with
      | []       => handleFinalSubparsers sps
      | t :: ts' =>
        match move g t sps with
        | inl msg => PredError msg
        | inr mv  =>
          match closure g mv with
          | inl msg => PredError msg
          | inr cl  => llPredict' g cl ts'
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
  | inr sps => llPredict' g sps ts
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
    llPredict' g sps ts = PredSucc gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts IH]; intros sps hl; sis.
  - destruct sps as [| sp sps']; tc; dmeq hall.
    + inv hl; exists sp; split; auto.
      apply in_eq.
    + apply handleFinalSubparsers_success_from_subparsers; auto.
  - destruct sps as [| sp sps'] eqn:hs; tc; dmeq hall.
    + inv hl; exists sp; split; auto.
      apply in_eq.
    + destruct (move g t _) as [m | sps''] eqn:hm; tc.
      destruct (closure g sps'') as [m | sps'''] eqn:hc; tc.
      apply IH in hl; destruct hl as [? [? ?]]; subst.
      eapply closure_preserves_prediction in hc; eauto.
      destruct hc as [? [? heq]]; rewrite heq.
      eapply move_preserves_prediction in hm; eauto.
      destruct hm as [? [? ?]]; eauto.
Qed.

Lemma llPredict'_ambig_result_in_original_subparsers :
  forall g ts gamma sps,
    llPredict' g sps ts = PredAmbig gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts IH]; intros sps hl; sis.
  - destruct sps as [| sp sps']; tc; dmeq hall; inv hl.
    apply handleFinalSubparsers_ambig_from_subparsers; auto.
  - destruct sps as [| sp sps'] eqn:hs; tc; dmeq hall.
    + inv hl.
    + destruct (move g t _) as [m | sps''] eqn:hm; tc.
      destruct (closure g sps'') as [m | sps'''] eqn:hc; tc.
      apply IH in hl; destruct hl as [? [? ?]]; subst.
      eapply closure_preserves_prediction in hc; eauto.
      destruct hc as [? [? heq]]; rewrite heq.
      eapply move_preserves_prediction in hm; eauto.
      destruct hm as [? [? ?]]; eauto.
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
  apply rhssForNt_in_grammar_iff.
  eapply llPredict_succ_in_rhssForNt; eauto.
Qed.

Lemma llPredict_ambig_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredAmbig ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply rhssForNt_in_grammar_iff.
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
  apply rhssForNt_in_grammar_iff; auto.
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

Fixpoint procSyms (frs : list location) : list symbol :=
  match frs with 
  | [] => []
  | Loc o pre suf :: frs' => procSyms frs' ++ pre
  end.

Definition procStackSyms stk : list symbol :=
  match stk with
  | (fr, frs) => procSyms (fr :: frs)
  end.

Inductive processedSyms_recognize_prefix g stk wsuf w : Prop :=
| SRP :
    forall wpre,
      gamma_recognize g (procSyms stk) wpre
      -> w = wpre ++ wsuf
      -> processedSyms_recognize_prefix g stk wsuf w.

Inductive processed_syms_recognize (g : grammar) : list location -> list token -> Prop :=
| PR_nil :
    processed_syms_recognize g [] []
| PR_cons :
    forall o pre suf wpre wsuf frs,
      gamma_recognize g pre wsuf
      -> processed_syms_recognize g frs wpre
      -> processed_syms_recognize g (Loc o pre suf :: frs) (wpre ++ wsuf).

Hint Constructors processed_syms_recognize.

Definition stack_processed_syms_recognize g stk w :=
  match stk with
  | (fr, frs) => processed_syms_recognize g (fr :: frs) w
  end.

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

Lemma handleFinalSubparsers_facts :
  forall sps rhs,
    handleFinalSubparsers sps = PredSucc rhs
    -> exists sp o pre,
      In sp sps
      /\ sp.(prediction) = rhs
      /\ sp.(stack) = (Loc o pre [], []).
Proof.
  intros sps rhs hh.
  unfold handleFinalSubparsers in hh.
  destruct (filter _ _) as [| sp sps'] eqn:hf; tc.
  destruct (allPredictionsEqual _ _); tc; inv hh.
  assert (hin : In sp (filter finalConfig sps)).
  { rewrite hf; apply in_eq. }
  apply filter_In in hin.
  destruct hin as [hin ht]; subst.
  unfold finalConfig in ht.
  exists sp.
  destruct sp as [av pred ([o pre suf], frs)]; sis.
  dm; tc.
  dm; tc.
  eexists; eexists; repeat split; auto.
Qed.

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

Inductive list_closure_multistep (g : grammar) : list subparser -> list subparser -> Prop :=
| LCM :
    forall sp sp' sps sps',
      In sp sps
      -> closure_multistep g sp sp'
      -> In sp' sps'
      -> list_closure_multistep g sps sps'.

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

Inductive list_move_step (g : grammar) :
  list subparser -> list token -> list subparser -> list token -> Prop :=
| LMS :
    forall sp sp' sps sps' ts ts',
      In sp sps
      -> move_step g sp ts sp' ts'
      -> list_move_step g sps ts sps' ts'.

Inductive list_move_closure_multistep (g : grammar) :
  list subparser -> list token -> list subparser -> list token -> Prop :=
| LMC_refl :
    forall sps ts,
      list_move_closure_multistep g sps ts sps ts
| LMC_trans :
    forall sps sps' sps'' sps''' ts ts'' ts''',
      list_move_step g sps ts sps' ts''
      -> list_closure_multistep g sps' sps''
      -> list_move_closure_multistep g sps'' ts'' sps''' ts'''
      -> list_move_closure_multistep g sps ts sps''' ts'''.

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

Lemma spClosure_multistep_rel :
  forall g pair (a : Acc lex_nat_pair pair) sp a' sp' sps',
    pair = meas g sp
    -> lstack_wf g sp.(stack)
    -> spClosure g sp a' = inr sps'
    -> In sp' sps'
    -> closure_multistep g sp sp'.
Proof.
  intros g pair a.
  induction a as [pair hlt IH].
  intros sp a' sp' sps' heq hw hs hi; subst.
  apply spClosure_success_cases in hs.
  destruct hs as [[hd heq] | [sps'' [hs [crs [heq heq']]]]]; subst.
  - apply in_singleton_eq in hi; subst; auto.
    unfold spClosureStep in hd; dms; tc.
    constructor.
    constructor.
  - eapply aggrClosureResults_succ_in_input in heq'; eauto.
    destruct heq' as [sps [hi' hi'']].
    eapply dmap_in in hi'; eauto.
    destruct hi' as [sp'' [hi''' [_ heq]]].
    eapply IH in heq; subst; eauto.
    + eapply CMS_trans; eauto.
      unfold spClosureStep in hs; dmeqs h; tc; inv hs.
      * apply in_singleton_eq in hi'''; subst.
        inv hw.
        constructor.
      * apply in_map_iff in hi'''.
        destruct hi''' as [rhs [heq' hin''']]; subst.
        simpl in hw.
        econstructor; eauto.
        -- eapply NtSet.mem_spec; auto.
        -- eapply rhssForNt_in_grammar_iff; eauto.
      * inv hi'''.
    + eapply spClosureStep_meas_lt; eauto.
    + eapply spClosureStep_preserves_lstack_wf_invar; eauto.
Qed.

Lemma closure_func_rel :
  forall g sps sps' sp',
    closure g sps = inr sps'
    -> In sp' sps'
    -> exists sp,
        In sp sps
        /\ closure_multistep g sp sp'.
Proof.
  intros g sps sps' sp' hc hi.
  eapply aggrClosureResults_succ_in_input in hc; eauto.
  destruct hc as [sps'' [hin hin']].
  apply in_map_iff in hin.
  destruct hin as [sp [heq hin]].
  exists sp; split; auto.
  eapply spClosure_multistep_rel; eauto.
Abort.

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

Lemma startState_multistep :
  forall g fr o pre x suf frs sp sps av pred,
    fr = Loc o pre (NT x :: suf)
    -> startState g x (fr, frs) = inr sps
    -> In sp sps
    -> closure_multistep g (Sp av pred (fr, frs)) sp.
Proof.
  intros g fr o pre x suf frs sp sps av pred heq hs hi; subst.
  unfold startState in hs.
Abort.  

Lemma start_state_init_invar :
  forall g x rhs fr o pre suf frs wpre wsuf,
    In (x, rhs) g
    -> fr = Loc o pre (NT x :: suf)
    -> gamma_recognize g rhs wpre
    -> gamma_recognize g (suf ++ unprocTailSyms frs) wsuf
    -> exists sp,
        In sp (map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, fr :: frs))
                   (rhssForNt g x))
        /\ gamma_recognize g (unprocStackSyms sp.(stack)) (wpre ++ wsuf).
Proof.
  intros g x rhs fr o pre suf frs wpre wsuf hin heq hg hg'.
  exists (Sp (allNts g) rhs (Loc (Some x) [] rhs, fr :: frs)); subst; sis.
  split.
  - apply in_map_iff.
    exists rhs; split; auto.
    admit.
  - admit.
Admitted.

Lemma startState_invar :
  forall g x fr o pre suf frs sp sps,
    fr = Loc o pre (NT x :: suf)
    -> startState g x (fr, frs) = inr sps
    -> In sp sps
    -> False.
Proof.
  intros g x fr o pre suf frs sp sps heq hs hi; subst.
  unfold startState in hs.
  eapply aggrClosureResults_succ_in_input in hs; eauto.
  destruct hs as [orig_sps [hin hin']].
  apply in_map_iff in hin.
  destruct hin as [sp' [heq hin]].
  apply in_map_iff in hin.
  destruct hin as [rhs [heq' hin]]; subst.
Abort.

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

Lemma app_eq_self_contra :
  forall A x (xs : list A),
    (x :: xs) <> xs.
Proof.
  intros A x xs; unfold not; intros heq.
  assert (heq' : [x] ++ xs = [] ++ xs) by apps.
  apply app_inv_tail in heq'; inv heq'.
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

Lemma llPredict_succ_rhs_derives_at_most_one_prefix :
  forall g fr o pre x suf frs w rhs rhs',
    fr = Loc o pre (NT x :: suf)
    -> In (x, rhs) g
    -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms frs) w
    -> llPredict g x (fr, frs) w = PredSucc rhs'
    -> rhs' = rhs.
Proof.
  intros g fr o pre x suf frs w rhs rhs' heq hin hg hl; subst.
  unfold llPredict in hl.
  destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
  eapply llPredict'_succ_labels_eq with (wpre := []) (orig_sps := sps) in hl; eauto.
Abort.
