Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

Fixpoint bottomElt' {A} (h : A) (t : list A) : A :=
  match t with
  | []        => h
  | h' :: t' => bottomElt' h' t'
  end.

Definition bottomElt {A} (stk : A * list A) : A :=
  let (h, t) := stk in bottomElt' h t.

Definition bottomFrameSyms (stk : location_stack) : list symbol :=
  let fr := bottomElt stk
  in  fr.(rpre) ++ fr.(rsuf).
  
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

Inductive step_result := StepAccept : forest -> step_result
                       | StepReject : string -> step_result
                       | StepK      : location_stack -> value_stack -> list token -> NtSet.t -> bool -> step_result
                       | StepError  : parse_error -> step_result.

Inductive parse_result := Accept : forest -> parse_result
                        | Ambig  : forest -> parse_result
                        | Reject : string -> parse_result
                        | Error  : parse_error -> parse_result.

Definition step (g      : grammar)
                (lstack : location_stack)
                (vstack : value_stack)
                (ts     : list token)
                (av     : NtSet.t)
                (u      : bool) : step_result := 
  match lstack, vstack with
  | (fr, frs), (v, vs) =>
    match fr with
    | Loc pre suf =>
      match suf with
      (* no more symbols to process in current frame *)
      | [] =>
        match frs, vs with
        (* empty symbol and value stacks --> terminate *)
        | [], [] => 
          match ts with
          | []     => StepAccept v
          | _ :: _ => StepReject "stack exhausted, tokens remain"
          end
        (* nonempty symbol and value stacks --> return to caller frame *)
        | Loc pre_cr suf_cr :: frs', v_cr :: vs' =>
          match suf_cr with
          | []                => StepError InvalidState
          | T _  :: _         => StepError InvalidState
          | NT x :: suf_cr'   =>
            let lstack' := (Loc (pre_cr ++ [NT x]) suf_cr, frs') in
            let vstack' := (v_cr ++ [Node x v], vs')             in
            StepK lstack' vstack' ts (NtSet.add x av) u
          end
        | _, _ => StepError InvalidState
        end
      (* terminal case --> consume a token *)
      | T a :: suf' =>
        match ts with
        | []             => StepReject "input exhausted"
        | (a', l) :: ts' =>
          if t_eq_dec a' a then
            let lstack' := (Loc (pre ++ [T a]) suf', frs) in
            let vstack' := (v ++ [Leaf a l], vs)          in
            StepK lstack' vstack' ts' (allNts g) u
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: suf' => 
        if NtSet.mem x av then
          match llPredict g x (fr, frs) ts with
          | PredSucc rhs =>
            let lstack' := (Loc [] rhs, fr :: frs) in
            let vstack' := ([], v :: vs)           in
            StepK lstack' vstack' ts (NtSet.remove x av) u
          | PredAmbig rhs =>
            let lstack' := (Loc [] rhs, fr :: frs) in
            let vstack' := ([], v :: vs)           in
            StepK lstack' vstack' ts (NtSet.remove x av) false
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
    end
  end.

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

Lemma multistep_unfold_ex :
  forall g st a,
  exists heq,
    multistep g st a =
    match step g st as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _  => if st.(unique) then Accept sv else Ambig sv
    | StepReject s  => fun _  => Reject s
    | StepK st'     => fun hs =>
                         multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s   => fun _  => Error s
    end heq.
Proof.
  intros; eexists; apply multistep_unfold.
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
       | Accept f => (sr = StepAccept f /\ st.(unique) = true)
                     \/ exists st' a', sr = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Ambig f  => (sr = StepAccept f /\ st.(unique) = false)
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
       | Accept f => (step g st = StepAccept f /\ st.(unique) = true)
                     \/ exists st' a', step g st = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Ambig f  => (step g st = StepAccept f /\ st.(unique) = false)
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
  forall (g  : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (f  : forest),
    multistep g st a = Accept f
    -> (step g st = StepAccept f /\ st.(unique) = true)
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Accept f.
Proof.
  intros g st a f hm; subst.
  destruct (multistep_cases g st a (Accept f)); auto.
Qed.

Lemma multistep_ambig_cases :
  forall (g  : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (f  : forest),
    multistep g st a = Ambig f
    -> (step g st = StepAccept f /\ st.(unique) = false)
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Ambig f.
Proof.
  intros g st a f hm; subst.
  destruct (multistep_cases g st a (Ambig f)); auto.
Qed.

Lemma multistep_reject_cases :
  forall (g  : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (s  : string),
    multistep g st a = Reject s
    -> step g st = StepReject s
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Reject s.
Proof.
  intros g st a s hm; subst.
  destruct (multistep_cases g st a (Reject s)); auto.
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

Definition mkInitState (g : grammar) (gamma : list symbol) (ts : list token) : parser_state :=
  Pst (allNts g) (Fr (Loc None [] gamma) [], []) ts true.

Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
  multistep g (mkInitState g gamma ts) (lex_nat_triple_wf _).

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