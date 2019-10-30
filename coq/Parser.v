Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

Record frame := Fr { loc : location
                   ; sem : forest
                   }.                               

Definition parser_stack := (frame * list frame)%type.

Definition lstackOf (stk : parser_stack) : location_stack :=
  let (fr, frs) := stk in (fr.(loc), map loc frs).

Fixpoint bottomFrame' (h : frame) (t : list frame) : frame :=
  match t with
  | []        => h
  | fr :: frs => bottomFrame' fr frs
  end.

Definition bottomFrame (stk : parser_stack) : frame :=
  let (h, t) := stk in bottomFrame' h t.

Definition bottomFrameSyms (stk : parser_stack) : list symbol :=
  let fr := bottomFrame stk
  in  fr.(loc).(rpre) ++ fr.(loc).(rsuf).
  
Record parser_state    := Pst { avail  : NtSet.t
                              ; stack  : parser_stack     
                              ; tokens : list token
                              ; unique : bool
                              }.

Inductive parse_error :=
| InvalidState    : parse_error
| LeftRecursion   : nonterminal -> parse_error
| PredictionError : prediction_error -> parse_error.

Inductive step_result := StepAccept : forest -> step_result
                       | StepReject : string -> step_result
                       | StepK      : parser_state -> step_result
                       | StepError  : parse_error -> step_result.

Inductive parse_result := Accept : forest -> parse_result
                        | Ambig  : forest -> parse_result
                        | Reject : string -> parse_result
                        | Error  : parse_error -> parse_result.

Definition step (g : grammar) (st : parser_state) : step_result :=
  match st with
  | Pst av (fr, frs) ts u =>
    match fr with
    | Fr (Loc xo pre suf) sv =>
      match suf with
      | [] => 
        match frs with
        (* empty stack --> accept *)
        | [] => 
          match ts with
          | []     => StepAccept sv
          | _ :: _ => StepReject "stack exhausted, tokens remain"
          end
        (* nonempty stack --> return to caller frame *)
        | (Fr (Loc xo_cr pre_cr suf_cr) sv_cr) :: frs_tl =>
          match suf_cr with
          | []                => StepError InvalidState
          | T _ :: _          => StepError InvalidState
          | NT x :: suf_cr_tl => 
            let cr' := Fr (Loc xo_cr (pre_cr ++ [NT x]) suf_cr_tl)
                          (sv_cr ++ [Node x sv])
            in  StepK (Pst (NtSet.add x av) (cr', frs_tl) ts u)
          end
        end
      (* terminal case --> consume a token *)
      | T a :: suf_tl =>
        match ts with
        | []               => StepReject "input exhausted"
        | (a', l) :: ts_tl =>
          if t_eq_dec a' a then 
            let fr' := Fr (Loc xo (pre ++ [T a]) suf_tl) (sv ++ [Leaf l])
            in  StepK (Pst (allNts g) (fr', frs) ts_tl u)
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: suf_tl => 
        if NtSet.mem x av then
          match llPredict g x (lstackOf (fr, frs)) ts with
          | PredSucc rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts u)
          | PredAmbig rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts false)
          | PredReject    => StepReject "prediction found no viable right-hand sides"
          | PredError e => StepError (PredictionError e)
          end
        else if NtSet.mem x (allNts g) then
               StepError (LeftRecursion x)
             else
               StepReject "nonterminal not in grammar"
      end
    end
  end.

Definition meas (g : grammar) (st : parser_state) : nat * nat * nat :=
  match st with
  | Pst av stk ts _ =>
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (List.length ts, stackScore (lstackOf stk) (1 + m) e, stackHeight stk)
  end.

(* It might be possible to delete this lemma and replace it
   with the primed version, or at least remove the
   specialization after pose proof by using stackScore_le_after_return' *)
Lemma state_lt_after_return :
  forall g st st' ts callee caller caller' frs x x' suf_cr_tl av u,
    st = Pst av (callee, caller :: frs) ts u
    -> st' = Pst (NtSet.add x av) (caller', frs) ts u
    -> callee.(loc).(rsuf)  = []
    -> caller.(loc).(rsuf)  = NT x' :: suf_cr_tl
    -> caller'.(loc).(rsuf) = suf_cr_tl
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' ts ce cr cr' frs x x' suf_cr_tl av u
         Hst hst' Hce Hcr Hcr'; subst.
  unfold meas. unfold lstackOf.
  pose proof (stackScore_le_after_return (loc ce) (loc cr) (loc cr')
                                         x x' (rsuf (loc cr')) av (map loc frs)
                                         (1 + maxRhsLength g)) as Hle.
  apply le_lt_or_eq in Hle; auto; destruct Hle as [Hlt | Heq].
  - apply triple_snd_lt; auto.
  - rewrite Heq; apply triple_thd_lt; auto.
Defined.

Lemma loc_proj_eq :
  forall l v, loc (Fr l v) = l.
Proof.
  auto.
Qed.

Lemma state_lt_after_return' :
  forall g st st' av u ts fr cr cr' frs o o' pre pre' suf' x v v' v'',
    st = Pst av (fr, cr :: frs) ts u
    -> st' = Pst (NtSet.add x av) (cr', frs) ts u
    -> fr  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') v''
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros; subst; unfold meas; unfold lstackOf.
  pose proof stackScore_le_after_return' as hs.
  eapply le_lt_or_eq in hs; eauto.
  destruct hs as [hlt | heq].
  - apply triple_snd_lt; eauto.
  - repeat rewrite loc_proj_eq; rewrite heq.
    apply triple_thd_lt; auto.
Defined.

Lemma state_lt_after_push :
  forall g st st' ts callee caller frs x suf_tl gamma av u u',
    st = Pst av (caller, frs) ts u
    -> st' = Pst (NtSet.remove x av) (callee, caller :: frs) ts u'
    -> caller.(loc).(rsuf) = NT x :: suf_tl
    -> callee.(loc).(rsuf) = gamma
    -> In gamma (rhssForNt g x)
    -> NtSet.In x av
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros; subst.
  apply triple_snd_lt.
  eapply stackScore_lt_after_push; eauto.
Defined.

Lemma step_meas_lt :
  forall g st st',
    step g st = StepK st'
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' Hs.
  unfold step in Hs.
  destruct st as [av [fr frs] ts u].
  destruct fr as [[xo pre suf] sv].
  destruct suf as [| [a | y] suf_tl].
  - (* return from the current frame *)
    destruct frs as [| caller frs_tl].
    + destruct ts; tc.
    + destruct caller as [[xo_cr pre_cr suf_cr] sv_cr].
      destruct suf_cr as [| [a | x] suf_cr_tl]; tc.
      inv Hs.
      eapply state_lt_after_return; simpl; eauto.
      simpl; auto.
  - (* terminal case *) 
    destruct ts as [| (a', l) ts_tl]; tc.
    destruct (t_eq_dec a' a); tc; subst.
    inv Hs.
    apply triple_fst_lt; simpl; auto.
  - (* nonterminal case -- push a new frame onto the stack *)
    destruct (NtSet.mem y av) eqn:Hm; tc.
    apply NtSet.mem_spec in Hm.
    destruct (llPredict g y _ ts) as [gamma|gamma| |msg] eqn:Hp; tc.
    + inv Hs.
      apply llPredict_succ_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
    + inv Hs.
      apply llPredict_ambig_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
    + destruct (NtSet.mem y (allNts g)); tc.
Defined.

Lemma StepK_st_acc :
  forall g st st' (a : Acc lex_nat_triple (meas g st)),
    step g st = StepK st' -> Acc lex_nat_triple (meas g st').
Proof.
  intros g st st' a Hs.
  eapply Acc_inv; eauto.
  apply step_meas_lt; auto.
Defined.

Fixpoint multistep (g  : grammar) 
                   (st : parser_state)
                   (a  : Acc lex_nat_triple (meas g st)) :
                   parse_result :=
  match step g st as res return step g st = res -> _ with
  | StepAccept sv    => fun _  => if st.(unique) then Accept sv else Ambig sv
  | StepReject s     => fun _  => Reject s
  | StepError e      => fun _  => Error e
  | StepK st'        => fun hs => multistep g st' (StepK_st_acc _ _ _ a hs)
  end eq_refl.

Definition mkInitState (g : grammar) (gamma : list symbol) (ts : list token) : parser_state :=
  Pst (allNts g) (Fr (Loc None [] gamma) [], []) ts true.

Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
  multistep g (mkInitState g gamma ts) (lex_nat_triple_wf _).

(* PARSER-RELATED LEMMAS *)

(* Lemmas for unfolding / inverting calls to step and multistep *)

Lemma multistep_unfold :
  forall g st a,
    multistep g st a = 
    match step g st as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _  => if st.(unique) then Accept sv else Ambig sv
    | StepReject s  => fun _  => Reject s
    | StepK st'     => fun hs =>
                         multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s   => fun _  => Error s
    end eq_refl.
Proof.
  intros; destruct a; auto.
Qed.              

Lemma multistep_cases' :
  forall (g   : grammar)
         (st  : parser_state)
         (a   : Acc lex_nat_triple (meas g st))
         (sr  : step_result)
         (pr  : parse_result)
         (heq : step g st = sr),
    match sr as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _ => if st.(unique) then Accept sv else Ambig sv
    | StepReject s => fun _  => Reject s
    | StepK st' => fun hs => multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s => fun _ => Error s
    end heq = pr
    -> match pr with
       | Accept f => sr = StepAccept f
                     \/ exists st' a', sr = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Ambig f  => sr = StepAccept f
                     \/ exists st' a', sr = StepK st' 
                                       /\ multistep g st' a' = Ambig f
       | Reject s => sr = StepReject s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Reject s
       | Error s  => sr = StepError s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Error s
       end.
Proof.
  intros g st a sr pr heq.
  destruct pr; destruct sr; destruct (unique st);
    try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto ].
Qed.

Lemma multistep_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (pr  : parse_result),
    multistep g st a = pr
    -> match pr with
       | Accept f => step g st = StepAccept f
                     \/ exists st' a', step g st = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Ambig f  => step g st = StepAccept f
                     \/ exists st' a', step g st = StepK st' 
                                       /\ multistep g st' a' = Ambig f
       | Reject s => step g st = StepReject s
                     \/ exists st' a', step g st = StepK st'
                                       /\ multistep g st' a' = Reject s
       | Error s  => step g st = StepError s
                     \/ exists st' a', step g st = StepK st'
                                       /\ multistep g st' a' = Error s
       end.
Proof.
  intros g st a pr hm; subst.
  rewrite multistep_unfold.
  eapply multistep_cases'; eauto.
Qed.

Lemma multistep_accept_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (f  : forest),
    multistep g st a = Accept f
    -> step g st = StepAccept f
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Accept f.
Proof.
  intros g st a f hm; subst.
  destruct (multistep_cases g st a (Accept f)); auto.
Qed.

Lemma multistep_invalid_state_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st)),
    multistep g st a = Error InvalidState
    -> step g st = StepError InvalidState
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Error InvalidState.
Proof.
  intros g st a hm; subst.
  destruct (multistep_cases g st a (Error InvalidState)); auto.
Qed.

Lemma multistep_left_recursion_cases :
  forall (g  : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (x  : nonterminal),
    multistep g st a = Error (LeftRecursion x)
    -> step g st = StepError (LeftRecursion x)
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Error (LeftRecursion x).
Proof.
  intros g st a x hm; subst.
  destruct (multistep_cases g st a (Error (LeftRecursion x))); auto.
Qed.

Lemma multistep_prediction_error_cases :
  forall (g  : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (e  : prediction_error),
    multistep g st a = Error (PredictionError e)
    -> step g st = StepError (PredictionError e)
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Error (PredictionError e).
Proof.
  intros g st a e hm; subst.
  destruct (multistep_cases g st a (Error (PredictionError e))); auto.
Qed.

Lemma step_StepAccept_facts :
  forall g av stk ts u v,
    step g (Pst av stk ts u) = StepAccept v
    -> (exists xo rpre v',
           stk = (Fr (Loc xo rpre []) v', [])
           /\ v' = v)
       /\ ts = [].
Proof.
  intros g av stk ts u v hs.
  unfold step in hs; dms; tc.
  inv hs; repeat eexists; eauto.
Qed.

Lemma step_LeftRecursion_facts :
  forall g av fr frs ts u x,
    step g (Pst av (fr, frs) ts u) = StepError (LeftRecursion x)
    -> ~ NtSet.In x av
       /\ NtSet.In x (allNts g)
       /\ exists suf,
           fr.(loc).(rsuf) = NT x :: suf.
Proof.
  intros g av fr frs ts u x hs.
  unfold step in hs; repeat dmeq h; tc; inv hs; sis;
  repeat split; eauto.
  - unfold not; intros hi.
    apply NtSet.mem_spec in hi; tc.
  - apply NtSet.mem_spec; auto.
Qed.

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

(* The stack symbols that have already been processed represent
   a (partial) derivation; this predicate relates those symbols
   to the word (prefix) involved in the derivation. *)

(*Inductive stack_derivation (g : grammar) : 
  parser_stack -> list token -> forest -> Prop :=
| SD_nil :
    forall xo pre suf w v,
      gamma_derivation g pre w v
      -> stack_derivation g (Fr (Loc xo pre suf) v, []) w v
| SD_cons :
    forall xo pre suf cr frs w w' v v',
      gamma_derivation g pre w' v'
      -> stack_derivation g (cr, frs) w v
      -> stack_derivation g (Fr (Loc xo pre suf) v', cr :: frs) (w ++ w') (v ++ v').
*)

Inductive frames_derivation (g : grammar) : 
  list frame -> list token -> forest -> Prop :=
| SD_nil : 
    frames_derivation g [] [] []
| SD_cons : 
    forall xo pre suf tl w w' v v',
      gamma_derivation g pre w' v'
      -> frames_derivation g tl w v
      -> frames_derivation g (Fr (Loc xo pre suf) v' :: tl) (w ++ w') (v ++ v').

Hint Constructors frames_derivation.

Definition stack_derivation (g : grammar) (stk : parser_stack) (w : list token) (v : forest) : Prop :=
  match stk with
  | (fr, frs) => frames_derivation g (fr :: frs) w v
  end.

(*Hint Unfold stack_derivation.*)

(* Tactic for inverting a stack_derivation hypothesis *)
Ltac inv_sd hsd wpre wsuf hgd hsd' := 
  inversion hsd as [ ? ? ? ? wpre ? hgd 
                   | ? ? ? ? ? wpre wsuf ? ? hgd hsd']; subst; clear hsd.

(* Parser invariant: the processed stack symbols represent a 
   partial derivation of a full word *)
(* Maybe I can call this "stack partial derivation" *)
Inductive stack_derivation_invar (g : grammar) (stk : parser_stack) (v : forest) (wsuf full_word : list token) : Prop :=
| SD_invar :
    forall wpre,
      stack_derivation g stk wpre v
      -> wpre ++ wsuf = full_word
      -> stack_derivation_invar g stk v wsuf full_word.

Hint Constructors stack_derivation_invar.

(* Tactic for inverting a stack_derivation_invar hypothesis *)
Ltac inv_sdi wpre hsd :=
  match goal with
  | H : stack_derivation_invar _ _ _ _ _ |- _ =>
    inversion H as [wpre hsd ?]; subst; clear H
  end.

Lemma frames_derivation_inv_cons :
  forall g o pre suf v' frs w'' v'',
    frames_derivation g (Fr (Loc o pre suf) v' :: frs) w'' v''
    -> exists w w' v,
      w'' = w ++ w'
      /\ v'' = v ++ v'
      /\ gamma_derivation g pre w' v'
      /\ frames_derivation g frs w v.
Proof.
  intros g o pre suf v' frs w'' v'' hf; inv hf; eauto 8.
Qed.

Lemma frames_derivation_inv_return :
  forall g frs o o' pre pre' suf suf' w''' v' v'' v''',
    frames_derivation g (Fr (Loc o pre suf) v''   ::
                         Fr (Loc o' pre' suf') v' :: frs)
                         w''' v'''
    -> exists w w' w'' v,
      w''' = w ++ w' ++ w''
      /\ v''' = v ++ v' ++ v''
      /\ gamma_derivation g pre w'' v''
      /\ gamma_derivation g pre' w' v'
      /\ frames_derivation g frs w v.
Proof.
  intros g frs o o' pre pre' suf suf' w''' v' v'' v''' hf; subst.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [w_tl [w'' [v_tl [? [? [hg hf]]]]]]; subst.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [w [w' [v [? [? [hg' hf]]]]]]; subst.
  repeat rewrite <- app_assoc; eauto 10.
Qed.

(*Lemma frames_derivation_inv_return :
  forall g fr cr frs o o' pre pre' suf suf' w''' v' v'' v''',
    fr = Fr (Loc o pre suf) v''
    -> cr = Fr (Loc o' pre' suf') v'
    -> frames_derivation g (fr :: cr :: frs) w''' v'''
    -> exists w w' w'' v,
      w''' = w ++ w' ++ w''
      /\ v''' = v ++ v' ++ v''
      /\ gamma_derivation g pre w'' v''
      /\ gamma_derivation g pre' w' v'
      /\ frames_derivation g frs w v.
Proof.
  intros g fr cr frs o o' pre pre' suf suf' w''' v' v'' v''' ? ? hf; subst.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [w_tl [w'' [v_tl [? [? [hg hf]]]]]]; subst.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [w [w' [v [? [? [hg' hf]]]]]]; subst.
  repeat rewrite <- app_assoc; eauto 10.
Qed. *)
(*
Lemma stack_derivation_inv_return :
  forall g fr cr frs w''' v''',
    stack_derivation g (Fr (Loc o pre suf) v'', cr :: frs) w''' v'''
    -> exists w w' w'' v v' v'',
      w''' = w ++ w' ++ w''
      /\ v''' = v ++ v' ++ v''
      /\ gamma_derivation g fr.(loc).(rpre) w'' v''
      /\ gamma_derivation g cr.(loc).(rpre) w' v'
      /\ frames_derivation g frs w v.
Proof.
  intros g fr cr frs w''' v''' hs; simpl in hs.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [wtl [w'' [vtl [v'' [heq [heq' [hg hf]]]]]]]; subst.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [w [w' [v [v' [heq [heq' [hg' hf]]]]]]]; subst.
  repeat rewrite <- app_assoc; eauto 12.
Qed.
*)
(*
Lemma stack_derivation_cases :
  forall g fr frs w''' v''',
    stack_derivation g (fr, frs) w''' v'''
    -> match frs with
       | [] => gamma_derivation g fr.(loc).(rpre) w''' v'''
       | cr :: frs' =>
         exists w w' w'' v v' v'',
         w ++ w' ++ w'' = w'''
         /\ v ++ v' ++ v'' = v'''
         /\ frames_derivation g frs' w v
         /\ gamma_derivation g cr.(loc).(rpre) w' v'
         /\ gamma_derivation g fr.(loc).(rpre) w'' v''
       end.
Proof.
  intros g fr frs w''' v''' hs.
  destruct frs as [| cr frs]; inv hs; eauto.
  - inv H4; auto.
  - inv H4; simpl; repeat eexists; eauto; apps.
Qed.
*)
(*
Lemma stack_derivation_cases :
  forall g fr frs w'' v'',
    stack_derivation g (fr, frs) w'' v''
    -> match frs with
       | []         => gamma_derivation g fr.(loc).(rpre) w'' v''
       | cr :: frs' =>
         exists w w' v v',
         w ++ w' = w''
         /\ v ++ v' = v''
         /\ stack_derivation g (cr, frs') w v
         /\ gamma_derivation g fr.(loc).(rpre) w' v'
       end.
Proof.
  intros g fr frs w'' v'' hs.
  destruct frs as [| cr frs]; inv hs; eauto 8.
Qed. *)

(*
Lemma foo :
  forall g o pre suf w'' v' v'' frs,
    frames_derivation g (Fr (Loc o pre suf) v' :: frs) w'' v''
    -> exists w w' v,
      w ++ w' = w''
      /\ v ++ v' = v''
      /\ gamma_derivation g pre w' v' 
      /\ frames_derivation g frs w v.
Proof.
  intros g o pre suf w'' v' v'' frs hf.
  inv hf; eauto 8.
Qed.
 *)

Lemma return_preserves_stack_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' w''' v v' v'',
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v''
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v''])
    -> stack_derivation g (ce, cr :: frs) w''' (v ++ v' ++ v'')
    -> stack_derivation g (cr', frs) w''' (v ++ v' ++ [Node x v'']).
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' w''' v v' v''
         hwf hce hcr hcr' hs; subst; simpl in hs.
  apply frames_derivation_inv_return in hs.
  destruct hs as [w [w' [w'' [? [? [heq [hg [hg' hf]]]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  inv hwf; rewrite app_nil_r in *.
  repeat (econstructor; eauto).
  eapply forest_app_singleton_node; eauto.
Qed.

Lemma consume_preserves_stack_derivation :
  forall g fr fr' frs o pre suf a l w v v',
    fr = Fr (Loc o pre (T a :: suf)) v'
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v' ++ [Leaf l])
    -> stack_derivation g (fr, frs) w (v ++ v')
    -> stack_derivation g (fr', frs) (w ++ [(a, l)]) (v ++ v' ++ [Leaf l]).
Proof.
  intros g fr fr' frs o pre suf a l w v v' ? ? hs; subst; simpl in hs.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [w_tl [w' [v_tl [? [heq [hg hf]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  (*  eapply SD_invar with (wpre := w_tl ++ w' ++ [(a, l)]); apps. *)
  rewrite <- app_assoc.
  constructor; auto.
  apply gamma_derivation_app; auto.
  apply terminal_head_gamma_derivation; auto.
Qed.

Lemma push_preserves_stack_derivation :
  forall g fr o o' pre suf suf' frs w v v',
    fr = Fr (Loc o pre suf) v'
    -> stack_derivation g (fr, frs) w (v ++ v')
    -> stack_derivation g (Fr (Loc o' [] suf') [], fr :: frs) w (v ++ v').
Proof.
  intros g fr o o' pre suf suf' frs w v v' ? hs; subst.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [w_tl [w' [v_tl [? [heq [hg hf]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  rew_nil_r (w_tl ++ w'); rew_nil_r (v_tl ++ v'); econstructor; eauto.
Qed.  
  


Lemma return_preserves_stack_derivation_invar :
  forall g ce cr cr' frs x o o' pre pre' suf' wsuf fw v v' v'',
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v''
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v''])
    -> stack_derivation_invar g (ce, cr :: frs) (v ++ v' ++ v'') wsuf fw
    -> stack_derivation_invar g (cr', frs) (v ++ v' ++ [Node x v'']) wsuf fw.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' wsuf fw v v' v''
         hwf hce hcr hcr' hi; subst.
  inv_sdi wpre''' hsd; simpl in hsd.
  apply frames_derivation_inv_return in hsd.
  destruct hsd as [w [w' [w'' [? [? [heq [hg [hg' hf]]]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  inv hwf; rewrite app_nil_r in *.
  repeat (econstructor; eauto).
  eapply forest_app_singleton_node; eauto.
Qed.

Lemma consume_preserves_stack_derivation_invar :
  forall g fr fr' frs o pre suf a l wsuf fw v v',
    fr = Fr (Loc o pre (T a :: suf)) v'
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v' ++ [Leaf l])
    -> stack_derivation_invar g (fr, frs) (v ++ v') ((a, l) :: wsuf) fw
    -> stack_derivation_invar g (fr', frs) (v ++ v' ++ [Leaf l]) wsuf fw.
Proof.
  intros g fr fr' frs o pre suf a l wsuf fw v v' ? ? hs; subst.
  inv_sdi wpre hs'; simpl in hs'.
  apply frames_derivation_inv_cons in hs'.
  destruct hs' as [w_tl [w' [v_tl [? [heq [hg hf]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  eapply SD_invar with (wpre := w_tl ++ w' ++ [(a, l)]); apps.
  constructor; auto.
  apply gamma_derivation_app; auto.
  apply terminal_head_gamma_derivation; auto.
Qed.

Lemma push_preserves_stack_derivation_invar :
  forall g fr o o' pre suf suf' frs wsuf fw v v',
    fr = Fr (Loc o pre suf) v'
    -> stack_derivation_invar g (fr, frs) (v ++ v') wsuf fw
    -> stack_derivation_invar g (Fr (Loc o' [] suf') [], fr :: frs) (v ++ v') wsuf fw.
Proof.
  intros g fr o o' pre suf suf' frs wsuf fw v v' ? hs; subst.
  inv_sdi wpre hs'; simpl in hs'.
  apply frames_derivation_inv_cons in hs'.
  destruct hs' as [w [w' [v_tl [? [heq [hg hf]]]]]]; subst.
  apply app_inv_tail in heq; subst.
  eapply SD_invar; eauto.
  rew_nil_r (w ++ w'); rew_nil_r (v_tl ++ v'); econstructor; eauto.
Qed.


Lemma step_preserves_stack_derivation_invar :
  forall g av av' stk stk' wsuf wsuf' w u u',
    stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> step g (Pst av stk wsuf u) = StepK (Pst av' stk' wsuf' u')
    -> stack_derivation_invar g stk' wsuf' w.
Proof.
  intros g av av' stk stk' wsuf wsuf' w u u' hw hi hs.
  unfold step in hs.
  dms; inv hs; tc.
  - eapply return_preserves_stack_derivation_invar;  eauto.
  - eapply consume_preserves_stack_derivation_invar; eauto.
  - eapply push_preserves_stack_derivation_invar;    eauto.
  - eapply push_preserves_stack_derivation_invar;    eauto.
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