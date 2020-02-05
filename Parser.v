Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

(*Definition bottomFrameSyms (stk : location_stack) : list symbol :=
  let fr := bottomElt stk
  in  fr.(rpre) ++ fr.(rsuf).
 *)

(*Record parser_state    := Pst { avail  : NtSet.t
                              ; stack  : parser_stack     
                              ; tokens : list token
                              ; unique : bool
                              }.
 *)

Inductive parse_error :=
| InvalidState    : parse_error
| LeftRecursion   : nonterminal -> parse_error
| PredictionError : prediction_error -> parse_error.

Inductive step_result :=
  StepAccept : forest -> step_result
| StepReject : string -> step_result
| StepK      : prefix_stack -> suffix_stack -> list token -> NtSet.t -> bool -> step_result
| StepError  : parse_error -> step_result.

Inductive parse_result := Accept : forest -> parse_result
                        | Ambig  : forest -> parse_result
                        | Reject : string -> parse_result
                        | Error  : parse_error -> parse_result.

Definition step (g      : grammar)
                (p_stk  : prefix_stack)
                (s_stk  : suffix_stack)
                (ts     : list token)
                (av     : NtSet.t)
                (u      : bool) : step_result := 
  match p_stk, s_stk with
  | (PF pre v, p_frs), (SF suf, s_frs) =>
    match suf with
    (* no more symbols to process in current frame *)
    | [] =>
      match p_frs, s_frs with
      (* empty stacks --> terminate *)
      | [], [] => 
        match ts with
        | []     => StepAccept (rev v)
        | _ :: _ => StepReject "stack exhausted, tokens remain"
        end
      (* nonempty stacks --> return to caller frames *)
      | PF pre_cr v_cr :: p_frs', SF suf_cr :: s_frs' =>
        match suf_cr with
        | []                => StepError InvalidState
        | T _  :: _         => StepError InvalidState
        | NT x :: suf_cr'   =>
          let p_stk' := (PF (NT x :: pre_cr) (Node x (rev v) :: v_cr), p_frs') in
          let s_stk' := (SF suf_cr', s_frs')                                   in
          StepK p_stk' s_stk' ts (NtSet.add x av) u
        end
      | _, _ => StepError InvalidState
      end
    (* terminal case --> consume a token *)
    | T a :: suf' =>
      match ts with
      | []             => StepReject "input exhausted"
      | (a', l) :: ts' =>
        if t_eq_dec a' a then
          let p_stk' := (PF (T a :: pre) (Leaf a l :: v), p_frs) in
          let s_stk' := (SF suf', s_frs)                         in
          StepK p_stk' s_stk' ts' (allNts g) u
        else
          StepReject "token mismatch"
      end
    (* nonterminal case --> push a frame onto the stack *)
    | NT x :: _ => 
      if NtSet.mem x av then
        match llPredict g x s_stk ts with
        | PredSucc rhs =>
          let p_stk' := (PF [] [], PF pre v :: p_frs) in
          let s_stk' := (SF rhs, SF suf :: s_frs)     in
          StepK p_stk' s_stk' ts (NtSet.remove x av) u
        | PredAmbig rhs =>
          let p_stk' := (PF [] [], PF pre v :: p_frs) in
          let s_stk' := (SF rhs, SF suf :: s_frs)     in
          StepK p_stk' s_stk' ts (NtSet.remove x av) false
        | PredReject =>
          StepReject "prediction found no viable right-hand sides"
        | PredError e =>
          StepError (PredictionError e)
        end
      else if NtSet.mem x (allNts g) then
             StepError (LeftRecursion x)
           else
             StepReject "nonterminal not in grammar"
    end
  end.

Lemma step_StepAccept_facts :
  forall g p_stk s_stk ts av u v,
    step g p_stk s_stk ts av u = StepAccept v
    -> ts = []
       /\ s_stk = (SF [], [])
       /\ exists pre,
           p_stk = (PF pre (rev v), []).
Proof.
  intros g pstk sstk ts av u v hs.
  unfold step in hs; dms; tc.
  inv hs; rewrite rev_involutive; eauto.
Qed.

Lemma step_LeftRecursion_facts :
  forall g p_stk s_stk ts av u x,
    step g p_stk s_stk ts av u = StepError (LeftRecursion x)
    -> ~ NtSet.In x av
       /\ NtSet.In x (allNts g)
       /\ exists suf frs,
           s_stk = (SF (NT x :: suf), frs).
Proof.
  intros g pstk sstk ts av u x hs.
  unfold step in hs; repeat dmeq h; tc; inv hs; sis;
  repeat split; eauto.
  - unfold not; intros hi.
    apply NtSet.mem_spec in hi; tc.
  - apply NtSet.mem_spec; auto.
Qed.

Definition meas (g   : grammar)
                (stk : suffix_stack)
                (ts  : list token)
                (av  : NtSet.t) : nat * nat * nat := 
  let m := maxRhsLength g    in
  let e := NtSet.cardinal av in
  (List.length ts, stackScore stk (1 + m) e, stackHeight stk).

Lemma meas_lt_after_return :
  forall g ce cr cr' x suf frs ts av,
    ce  = SF []
    -> cr  = SF (NT x :: suf)
    -> cr' = SF suf
    -> lex_nat_triple (meas g (cr', frs) ts (NtSet.add x av))
                      (meas g (ce, cr :: frs) ts av).
Proof.
  intros; subst; unfold meas.
  pose proof stackScore_le_after_return as hs.
  eapply le_lt_or_eq in hs; eauto.
  destruct hs as [hlt | heq].
  - apply triple_snd_lt; eauto. 
  - rewrite heq. apply triple_thd_lt; auto. 
Defined.

Lemma meas_lt_after_push :
  forall g cr ce x suf rhs frs ts av,
    cr = SF (NT x :: suf)
    -> ce = SF rhs
    -> In (x, rhs) g 
    -> NtSet.In x av
    -> lex_nat_triple (meas g (ce, cr :: frs) ts (NtSet.remove x av))
                      (meas g (cr, frs) ts av).
Proof.
  intros; subst.
  apply triple_snd_lt.
  eapply stackScore_lt_after_push; eauto.
Defined.

Lemma step_meas_lt :
  forall g p_stk p_stk' s_stk s_stk' ts ts' av av' u u',
    step g p_stk s_stk ts av u = StepK p_stk' s_stk' ts' av' u'
    -> lex_nat_triple (meas g s_stk' ts' av') (meas g s_stk ts av).
Proof.
  intros g pstk pstk' sstk stk' ts ts' av av' u u' hs; unfold step in hs.
  destruct sstk as ([ [| [a|x] suf] ], frs).
  - dms; tc; inv hs.
    eapply meas_lt_after_return; eauto.
  - dms; tc; inv hs.
    apply triple_fst_lt; auto.
  - destruct pstk as ([pre v], p_frs).
    destruct (NtSet.mem x av) eqn:hm; [.. | dms; tc].
    apply NtSet.mem_spec in hm.
    destruct (llPredict _ _ _ _) eqn:hp; dms; tc; inv hs.
    + apply llPredict_succ_in_grammar in hp.
      eapply meas_lt_after_push; eauto.
    + apply llPredict_ambig_in_grammar in hp.
      eapply meas_lt_after_push; eauto.
Qed.

Lemma StepK_result_acc :
  forall g ps ps' ss ss' ts ts' av av' u u' (a : Acc lex_nat_triple (meas g ss ts av)),
    step g ps ss ts av u = StepK ps' ss' ts' av' u'
    -> Acc lex_nat_triple (meas g ss' ts' av').
Proof.
  intros; eapply Acc_inv; eauto.
  eapply step_meas_lt; eauto.
Defined.

Fixpoint multistep (g  : grammar)
                   (ps : prefix_stack)
                   (ss : suffix_stack)
                   (ts : list token)
                   (av : NtSet.t)
                   (u  : bool)
                   (a  : Acc lex_nat_triple (meas g ss ts av))
                   {struct a} :
                   parse_result :=
  match step g ps ss ts av u as res return step g ps ss ts av u = res -> _ with
  | StepAccept v             => fun _  => if u then Accept v else Ambig v
  | StepReject s             => fun _  => Reject s
  | StepError e              => fun _  => Error e
  | StepK ps' ss' ts' av' u' =>
    fun hs => multistep g ps' ss' ts' av' u'
                        (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ a hs)
  end eq_refl.

Lemma multistep_unfold :
  forall g ps ss ts av u a,
    multistep g ps ss ts av u a = 
    match step g ps ss ts av u
    as res return (step g ps ss ts av u = res -> parse_result)
    with
    | StepAccept sv            => fun _ => if u then Accept sv else Ambig sv
    | StepReject s             => fun _ => Reject s
    | StepK ps' ss' ts' av' u' =>
      fun hs =>
        multistep g ps' ss' ts' av' u'
                  (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ a hs)
    | StepError s              => fun _ => Error s
    end eq_refl.
Proof.
  intros; destruct a; auto.
Qed.

Lemma multistep_unfold_ex :
  forall g ps ss ts av u a,
  exists heq,
    multistep g ps ss ts av u a =
    match step g ps ss ts av u
    as res return (step g ps ss ts av u = res -> parse_result)
    with
    | StepAccept sv            => fun _ => if u then Accept sv else Ambig sv
    | StepReject s             => fun _ => Reject s
    | StepK ps' ss' ts' av' u' =>
      fun hs =>
        multistep g ps' ss' ts' av' u'
                  (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ a hs)
    | StepError s              => fun _ => Error s
    end heq.
Proof.
  intros; eexists; apply multistep_unfold.
Qed.              

Lemma multistep_cases' :
  forall (g   : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av))
         (sr  : step_result)
         (pr  : parse_result)
         (heq : step g ps ss ts av u = sr),
    match sr as res return (step g ps ss ts av u = res -> parse_result) with
    | StepAccept sv            => fun _ => if u then Accept sv else Ambig sv
    | StepReject s             => fun _  => Reject s
    | StepK ps' ss' ts' av' u' =>
      fun hs => multistep g ps' ss' ts' av' u'
                          (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ a hs)
    | StepError s              => fun _ => Error s
    end heq = pr
    -> match pr with
       | Accept f => (sr = StepAccept f /\ u = true)
                     \/ (exists ps' ss' ts' av' u' a',
                            sr = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Accept f)
       | Ambig f  => (sr = StepAccept f /\ u = false)
                     \/ (exists ps' ss' ts' av' u' a',
                            sr = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Ambig f)
       | Reject s => sr = StepReject s
                     \/ (exists ps' ss' ts' av' u' a',
                            sr = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Reject s)
       | Error s  => sr = StepError s
                     \/ (exists ps' ss' ts' av' u' a',
                            sr = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Error s)
       end.
Proof.
  intros g ps ss ts av u a sr pr heq.
  destruct pr; destruct sr; destruct u;
  try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto 8].
Qed.

Lemma multistep_cases :
  forall (g   : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av))
         (pr  : parse_result),
    multistep g ps ss ts av u a = pr
    -> match pr with
       | Accept f => (step g ps ss ts av u = StepAccept f /\ u = true)
                     \/ (exists ps' ss' ts' av' u' a',
                            step g ps ss ts av u = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Accept f)
       | Ambig f  => (step g ps ss ts av u = StepAccept f /\ u = false)
                     \/ (exists ps' ss' ts' av' u' a',
                            step g ps ss ts av u = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Ambig f)
       | Reject s => step g ps ss ts av u = StepReject s
                     \/ (exists ps' ss' ts' av' u' a',
                            step g ps ss ts av u = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Reject s)
       | Error s  => step g ps ss ts av u = StepError s
                     \/ (exists ps' ss' ts' av' u' a',
                            step g ps ss ts av u = StepK ps' ss' ts' av' u'
                            /\ multistep g ps' ss' ts' av' u' a' = Error s)
       end.
Proof.
  intros g ps ss ts av u a pr hm; subst.
  rewrite multistep_unfold.
  eapply multistep_cases'; eauto.
Qed.

Lemma multistep_accept_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a  : Acc lex_nat_triple (meas g ss ts av))
         (f  : forest),
    multistep g ps ss ts av u a = Accept f
    -> (step g ps ss ts av u = StepAccept f /\ u = true)
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Accept f).
Proof.
  intros ? ? ? ? ? ? a f hm; subst. 
  destruct (multistep_cases _ _ _ _ _ _ a (Accept f) hm); auto.
Qed.

Lemma multistep_ambig_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a  : Acc lex_nat_triple (meas g ss ts av))
         (f  : forest),
    multistep g ps ss ts av u a = Ambig f
    -> (step g ps ss ts av u = StepAccept f /\ u = false)
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Ambig f).
Proof.
  intros ? ? ? ? ? ? a f hm; subst. 
  destruct (multistep_cases _ _ _ _ _ _ a (Ambig f) hm); auto.
Qed.

Lemma multistep_reject_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av))
         (s   : string),
    multistep g ps ss ts av u a = Reject s
    -> step g ps ss ts av u = StepReject s
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Reject s).
Proof.
  intros ? ? ? ? ? ? a s hm; subst. 
  destruct (multistep_cases _ _ _ _ _ _ a (Reject s) hm); auto.
Qed.

Lemma multistep_invalid_state_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av)),
    multistep g ps ss ts av u a = Error InvalidState
    -> step g ps ss ts av u = StepError InvalidState
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Error InvalidState).
Proof.
  intros ? ? ? ? ? ? a hm; subst.
  destruct (multistep_cases _ _ _ _ _ _ a (Error InvalidState) hm); auto.
Qed.

Lemma multistep_left_recursion_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av))
         (x   : nonterminal),
    multistep g ps ss ts av u a = Error (LeftRecursion x)
    -> step g ps ss ts av u = StepError (LeftRecursion x)
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Error (LeftRecursion x)).
Proof.
  intros ? ? ? ? ? ? a x hm; subst.
  destruct (multistep_cases _ _ _ _ _ _ a (Error (LeftRecursion x)) hm); auto.
Qed.

Lemma multistep_prediction_error_cases :
  forall (g  : grammar)
         (ps  : prefix_stack)
         (ss  : suffix_stack)
         (ts  : list token)
         (av  : NtSet.t)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g ss ts av))
         (e   : prediction_error),
    multistep g ps ss ts av u a = Error (PredictionError e)
    -> step g ps ss ts av u = StepError (PredictionError e)
       \/ (exists ps' ss' ts' av' u' a',
              step g ps ss ts av u = StepK ps' ss' ts' av' u'
              /\ multistep g ps' ss' ts' av' u' a' = Error (PredictionError e)).
Proof.
  intros ? ? ? ? ? ? a e hm; subst.
  destruct (multistep_cases _ _ _ _ _ _ a (Error (PredictionError e)) hm); auto.
Qed.

(* May be deprecated -- initial stacks are created in the body of parse *)
Definition mkInitState (g : grammar) (gamma : list symbol) (ts : list token) :
  prefix_stack * suffix_stack * list token * NtSet.t * bool :=
  ( (PF [] [], []),
    (SF gamma, []),
    ts                ,
    allNts g          ,
    true ). 

Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
  let p_stk0 := (PF [] [], []) in
  let s_stk0 := (SF gamma, []) in
  multistep g p_stk0 s_stk0 ts (allNts g) true (lex_nat_triple_wf _). 

(*
(* A WELL-FORMEDNESS INVARIANT FOR THE PARSER STACK *)

Definition frames_wf (g : grammar) (frs : list frame) : Prop :=
  locations_wf g (map loc frs).

Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
  match stk with
  | (fr, frs) => frames_wf g (fr :: frs)
  end.

Hint Unfold frames_wf stack_wf.

Lemma step_preserves_stack_wf_invar :
  forall g av av' stk stk' ts ts' u u',
    step g (Pst av stk ts u) = StepK (Pst av' stk' ts' u')
    -> stack_wf g stk 
    -> stack_wf g stk'.
Proof.
  intros g av av' (fr, frs) (fr', frs') ts ts' u u' hs hw.
  unfold step in hs; unfold stack_wf in *; unfold frames_wf in *.
  dmeqs h; tc; inv hs; sis. 
  - eapply return_preserves_locations_wf_invar; eauto.
  - apply consume_preserves_locations_wf_invar; auto.
  - apply push_preserves_locations_wf_invar; auto.
    eapply llPredict_succ_in_rhssForNt; eauto.
  - apply push_preserves_locations_wf_invar; auto.
    eapply llPredict_ambig_in_rhssForNt; eauto.
Qed.

Lemma frames_wf_app :
  forall g p s,
    frames_wf g (p ++ s)
    -> frames_wf g p /\ frames_wf g s.
Proof.
  intros g p s hw.
  eapply locations_wf_app; eauto.
  apply map_app.
Qed.

Lemma frames_wf_app_l :
  forall g pre suf,
    frames_wf g (pre ++ suf)
    -> frames_wf g pre.
Proof.
  intros g pre suf hw.
  eapply frames_wf_app in hw; eauto.
  firstorder.
Qed.

Lemma frames_wf_tl :
  forall g fr frs,
    frames_wf g (fr :: frs)
    -> frames_wf g frs.
Proof.
  intros g fr frs hw.
  rewrite cons_app_singleton in hw.
  eapply frames_wf_app in hw; eauto.
  firstorder.
Qed.

(* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

Definition unavailable_nts_invar g st : Prop :=
  match st with
  | Pst av stk _ _ =>
    unavailable_nts_are_open_calls g av (lstackOf stk)
  end.

Lemma unavailable_nts_invar_starts_true :
  forall g ys ts,
    unavailable_nts_invar g (mkInitState g ys ts).
Proof.
  intros g ys ts; unfold mkInitState; unfold unavailable_nts_are_open_calls.
  intros x hi hn; ND.fsetdec.
Qed.

Lemma return_preserves_unavailable_nts_invar :
  forall g av fr cr cr' frs o o' pre pre' x suf' v v' v'',
    fr     = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') v''
    -> stack_wf g (fr, cr :: frs)
    -> unavailable_nts_are_open_calls g av (lstackOf (fr, cr :: frs))
    -> unavailable_nts_are_open_calls g (NtSet.add x av) (lstackOf (cr', frs)).
Proof.
  intros g av fr cr cr' frs o o' pre pre' x suf' v v' v'' ? ? ? hw hu; subst; sis.
  intros x' hi hn.
  assert (hn' : ~ NtSet.In x' av) by ND.fsetdec.
  apply hu in hn'; auto.
  destruct hn' as [hng [frs_pre [cr [frs_suf [suf [heq [ha heq']]]]]]].
  destruct frs_pre as [| fr_pre frs_pre]; inv heq; inv ha; sis.
  - inv heq'; ND.fsetdec.
  - split; eauto 8.
    inv hw; rewrite app_nil_r in *.
    apply nullable_app; eauto.
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

(* THE STACK SYMBOLS THAT HAVE ALREADY BEEN PROCESSED REPRESENT
   A (PARTIAL) DERIVATION; THIS PREDICATE RELATES THOSE SYMBOLS
   TO THE WORD (PREFIX) INVOLVED IN THE DERIVATION. *)
Inductive frames_derivation (g : grammar) : list frame -> list token -> Prop :=
| FD_nil :
    frames_derivation g [] []
| FD_cons :
    forall o pre suf v wpre wsuf frs,
      gamma_derivation g pre wsuf v
      -> frames_derivation g frs wpre
      -> frames_derivation g (Fr (Loc o pre suf) v :: frs) (wpre ++ wsuf).

Hint Constructors frames_derivation.

Definition stack_derivation g stk w :=
  match stk with
  | (fr, frs) => frames_derivation g (fr :: frs) w
  end.

(* Tactic for inverting a frames_derivation hypothesis *)
Ltac inv_fd hfd wpre wsuf hgd hsd' := inversion hfd as [ | ? ? ? ? ? ? wpre wsuf hgd hsd']; subst; clear hfd.

(* Tactic for inverting a stack_derivation hypothesis *)
Ltac inv_sd hsd wpre wsuf hgd hsd' := inversion hsd as [? ? ? ? wpre hgd | ? ? ? ? ? ? wpre wsuf hgd hsd']; subst; clear hsd.

Lemma frames_derivation_inv_cons :
  forall g o pre suf v frs w,
    frames_derivation g (Fr (Loc o pre suf) v :: frs) w
    -> exists wpre wsuf,
      w = wpre ++ wsuf
      /\ gamma_derivation g pre wsuf v
      /\ frames_derivation g frs wpre.
Proof.
  intros g o pre suf v frs w hf; inv hf; eauto.
Qed.

Lemma frames_derivation_bottom :
  forall g o pre suf v w,
    frames_derivation g [Fr (Loc o pre suf) v] w
    -> gamma_derivation g pre w v.
Proof.
  intros g o pre suf v w hf.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [wpre [wsuf [heq [hg hf]]]]; inv hf; auto.
Qed.

Lemma stack_derivation_inv_return :
  forall g o o' pre pre' suf suf' v v' frs w,
    stack_derivation g (Fr (Loc o pre suf) v, Fr (Loc o' pre' suf') v' :: frs) w
    -> exists wpre wmid wsuf,
      w = wpre ++ wmid ++ wsuf
      /\ gamma_derivation g pre wsuf v
      /\ gamma_derivation g pre' wmid v'
      /\ frames_derivation g frs wpre.
Proof.
  intros g o o' pre pre' suf suf' v v' frs w hf.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [wpre [wsuf [heq [hg hf]]]]; subst.
  apply frames_derivation_inv_cons in hf; firstorder; subst.
  rewrite <- app_assoc; eauto 8.
Qed.

Lemma return_preserves_stack_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' w,
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_derivation g (ce, cr :: frs) w
    -> stack_derivation g (cr', frs) w.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' w
         hw ? ? ? hs; subst.
  inv hw; rewrite app_nil_r in *.
  apply stack_derivation_inv_return in hs.
  destruct hs as [wpre [wmid [wsuf [heq [hg [hg' hf]]]]]]; subst.
  constructor; auto.
  eapply forest_app_singleton_node; eauto.
Qed.

Lemma consume_preserves_stack_derivation :
  forall g fr fr' frs o pre suf a l v w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> stack_derivation g (fr, frs) w
    -> stack_derivation g (fr', frs) (w ++ [(a, l)]).
Proof.
  intros g fr fr' frs o pre suf a l v w ? ? hs; subst.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [wpre [wsuf [heq [hg hf]]]]; subst.
  rewrite <- app_assoc; constructor; auto.
  apply gamma_derivation_app; auto.
  apply terminal_head_gamma_derivation; auto.
Qed.

Lemma push_preserves_stack_derivation :
  forall g fr frs o' suf' w,
    stack_derivation g (fr, frs) w
    -> stack_derivation g (Fr (Loc o' [] suf') [], fr :: frs) w.
Proof.
  intros g [[o pre suf] v] frs o' suf' w hs.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [wpre [wsuf [heq [hg hf]]]]; subst.
  rew_nil_r (wpre ++ wsuf); constructor; auto.
Qed.

(* Parser invariant: the processed stack symbols represent a 
   partial derivation of a full word *)
Inductive stack_prefix_derivation (g : grammar) (stk : parser_stack) (wsuf w : list token) : Prop :=
| SPD :
    forall wpre,
      stack_derivation g stk wpre
      -> wpre ++ wsuf = w
      -> stack_prefix_derivation g stk wsuf w.

Lemma return_preserves_stack_prefix_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' wsuf w,
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_prefix_derivation g (ce, cr :: frs) wsuf w
    -> stack_prefix_derivation g (cr', frs) wsuf w.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' wsuf w
         hw ? ? ? hs; inv hs; econstructor; eauto.
  eapply return_preserves_stack_derivation; eauto.
Qed.

Lemma consume_preserves_stack_prefix_derivation :
  forall g fr fr' frs o pre suf a l v wsuf w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> stack_prefix_derivation g (fr, frs) ((a, l) :: wsuf) w
    -> stack_prefix_derivation g (fr', frs) wsuf w.
Proof.
  intros g fr fr' frs o pre suf a l v wsuf w ? ? hs; inv hs; econstructor.
  - eapply consume_preserves_stack_derivation; eauto.
  - apps.
Qed.

Lemma push_preserves_stack_prefix_derivation :
  forall g fr frs o' suf' wsuf w,
    stack_prefix_derivation g (fr, frs) wsuf w
    -> stack_prefix_derivation g (Fr (Loc o' [] suf') [], fr :: frs) wsuf w.
Proof.
  intros g [[o pre suf] v] frs o' suf' wsuf w hs; inv hs; econstructor; eauto.
  apply push_preserves_stack_derivation; auto.
Qed.

Lemma step_preserves_stack_prefix_derivation :
  forall g av av' stk stk' wsuf wsuf' w u u',
    stack_wf g stk
    -> stack_prefix_derivation g stk wsuf w
    -> step g (Pst av stk wsuf u) = StepK (Pst av' stk' wsuf' u')
    -> stack_prefix_derivation g stk' wsuf' w.
Proof.
  intros g av av' stk stk' wsuf wsuf' w u u' hw hi hs.
  unfold step in hs.
  dms; inv hs; tc.
  - eapply return_preserves_stack_prefix_derivation;  eauto.
  - eapply consume_preserves_stack_prefix_derivation; eauto.
  - eapply push_preserves_stack_prefix_derivation;    eauto.
  - eapply push_preserves_stack_prefix_derivation;    eauto.
Qed.

Lemma stack_prefix_derivation_init :
  forall g ys ts,
    stack_prefix_derivation g (Fr (Loc None [] ys) [], []) ts ts.
Proof.
  intros g ys ts.
  apply SPD with (wpre := []); auto.
  rew_nil_r ([] : list token).
  constructor; auto.
Qed.

Lemma stack_prefix_derivation_final :
  forall g o pre suf v w,
    stack_prefix_derivation g (Fr (Loc o pre suf) v, []) [] w
    -> gamma_derivation g pre w v.
Proof.
  intros g o pre suf v w hs.
  destruct hs as [wpre hs heq]; subst; rewrite app_nil_r.
  eapply frames_derivation_bottom; eauto.
Qed.

(* Another invariant of the step function--the symbols
   in the stack's bottom frame remain the same *)

(* First, a tactic to help with the following lemma *)
Ltac destr_tl :=
  match goal with
  | |- context[bottomFrame (?h, _ :: ?t)] => destruct t
  | |- context[bottomFrame (?h, ?t)]      => destruct t
  end.

Lemma step_preserves_bottomFrameSyms_invar :
  forall g av av' stk stk' ts ts' u u',
    step g (Pst av stk ts u) = StepK (Pst av' stk' ts' u')
    -> bottomFrameSyms stk = bottomFrameSyms stk'.
Proof.
  intros g av av' stk stk' ts ts' u u' hs.
  unfold step in hs.
  dms; inv hs; tc; unfold bottomFrameSyms; destr_tl; sis; auto; apps.
Qed.
*)