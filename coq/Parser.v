Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

(* PARSER IMPLEMENTATION *)

Record frame := Fr { loc : location
                   ; sem : forest
                   }.                               

Definition parser_stack := (frame * list frame)%type.

Definition locStackOf (stk : parser_stack) : location_stack :=
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
                              }.

Inductive error_type :=
| InvalidState    : error_type
| PredictionError : string -> error_type
| LeftRecursion   : nonterminal -> error_type.

Inductive step_result := StepAccept : forest -> step_result
                       | StepReject : string -> step_result
                       | StepK      : parser_state -> step_result
                       | StepError  : error_type -> step_result.

Inductive parse_result := Accept : forest -> parse_result
                        | Reject : string -> parse_result
                        | Error  : error_type -> parse_result.

Definition step (g : grammar) (st : parser_state) : step_result :=
  match st with
  | Pst av (fr, frs) ts =>
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
          | []                 => StepError InvalidState
          | T _ :: _           => StepError InvalidState
          | NT x :: suf_cr_tl => 
            let cr' := Fr (Loc xo_cr (pre_cr ++ [NT x]) suf_cr_tl)
                          (sv_cr ++ [Node x sv])
            in  StepK (Pst (NtSet.add x av) (cr', frs_tl) ts)
          end
        end
      (* terminal case --> consume a token *)
      | T a :: suf_tl =>
        match ts with
        | []               => StepReject "input exhausted"
        | (a', l) :: ts_tl =>
          if t_eq_dec a' a then 
            let fr' := Fr (Loc xo (pre ++ [T a]) suf_tl) (sv ++ [Leaf l])
            in  StepK (Pst (allNts g) (fr', frs) ts_tl)
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: suf_tl => 
        if NtSet.mem x av then
          match llPredict g x (locStackOf (fr, frs)) ts with
          | PredSucc rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          (* maybe flip a bit indicating ambiguity? *)
          | PredAmbig rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          | PredReject    => StepReject "prediction found no viable right-hand sides"
          | PredError msg => StepError (PredictionError msg)
          end
        else
          StepError (LeftRecursion x)
      end
    end
  end.

Definition meas (g : grammar) (st : parser_state) : nat * nat * nat :=
  match st with
  | Pst av stk ts =>
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (List.length ts, stackScore (locStackOf stk) (1 + m) e, stackHeight stk)
  end.

Lemma state_lt_after_return :
  forall g st st' ts callee caller caller' frs x x' suf_cr_tl av,
    st = Pst av (callee, caller :: frs) ts
    -> st' = Pst (NtSet.add x av) (caller', frs) ts
    -> callee.(loc).(rsuf)  = []
    -> caller.(loc).(rsuf)  = NT x' :: suf_cr_tl
    -> caller'.(loc).(rsuf) = suf_cr_tl
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' ts ce cr cr' frs x x' suf_cr_tl av
         Hst hst' Hce Hcr Hcr'; subst.
  unfold meas. unfold locStackOf.
  pose proof (stackScore_le_after_return (loc ce) (loc cr) (loc cr')
                                         x x' (rsuf (loc cr')) av (map loc frs)
                                         (1 + maxRhsLength g)) as Hle.
  apply le_lt_or_eq in Hle; auto; destruct Hle as [Hlt | Heq].
  - apply triple_snd_lt; auto.
  - rewrite Heq; apply triple_thd_lt; auto.
Defined.

Lemma state_lt_after_push :
  forall g st st' ts callee caller frs x suf_tl gamma av,
    st = Pst av (caller, frs) ts
    -> st' = Pst (NtSet.remove x av) (callee, caller :: frs) ts
    -> caller.(loc).(rsuf) = NT x :: suf_tl
    -> callee.(loc).(rsuf) = gamma
    -> In gamma (rhssForNt g x)
    -> NtSet.In x av
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' ts ce cr frs x suf_tl gamma av
         Hst Hst' Hcr Hce Hi Hm; subst.
  apply triple_snd_lt.
  eapply stackScore_lt_after_push; eauto.
Defined.

Lemma PredSucc_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredSucc gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma Hf.
  eapply PredSucc_result_in_rhssForNt; eauto.
Defined.

Lemma PredAmbig_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredAmbig gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma.
  eapply PredAmbig_result_in_rhssForNt; eauto.
Defined.

Lemma step_meas_lt :
  forall g st st',
    step g st = StepK st'
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' Hs.
  unfold step in Hs.
  destruct st as [av [fr frs] ts].
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
      apply PredSucc_result_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
    + inv Hs.
      apply PredAmbig_result_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
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
  | StepAccept sv    => fun _  => Accept sv
  | StepReject s     => fun _  => Reject s
  | StepError e      => fun _  => Error e
  | StepK st'        => fun Hs => multistep g st' (StepK_st_acc _ _ _ a Hs)
  end eq_refl.

Definition mkInitState (g : grammar) (gamma : list symbol) (ts : list token) : parser_state :=
  Pst (allNts g) (Fr (Loc None [] gamma) [], []) ts.

Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
  multistep g (mkInitState g gamma ts) (lex_nat_triple_wf _).

(* PARSER-RELATED LEMMAS *)

(* Lemmas for unfolding / inverting calls to step and multistep *)

Lemma multistep_unfold :
  forall g st a,
    multistep g st a = 
    match step g st as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _  => Accept sv
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
    | StepAccept sv => fun _ => Accept sv
    | StepReject s => fun _  => Reject s
    | StepK st' => fun hs => multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s => fun _ => Error s
    end heq = pr
    -> match pr with
       | Accept f => sr = StepAccept f
                     \/ exists st' a', sr = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Reject s => sr = StepReject s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Reject s
       | Error s  => sr = StepError s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Error s
       end.
Proof.
  intros g st a sr pr heq.
  destruct pr; destruct sr; subst;
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

Lemma step_StepAccept_facts :
  forall g av stk ts v,
    step g (Pst av stk ts) = StepAccept v
    -> (exists xo rpre v',
           stk = (Fr (Loc xo rpre []) v', [])
           /\ v' = v)
       /\ ts = [].
Proof.
  intros g av stk ts v hs.
  unfold step in hs; dms; tc.
  inv hs; repeat eexists; eauto.
Qed.

Lemma step_LeftRecursion_facts :
  forall g av fr frs ts x,
    step g (Pst av (fr, frs) ts) = StepError (LeftRecursion x)
    -> ~ NtSet.In x av
       /\ exists suf,
        fr.(loc).(rsuf) = NT x :: suf.
Proof.
  intros g av fr frs ts x hs.
  unfold step in hs; repeat dmeq heq; tc; inv hs; sis.
  split; eauto.
  unfold not; intros hi.
  apply NtSet.mem_spec in hi; tc.
Qed.

(* A well-formedness invariant for the parser stack *)

Inductive frames_wf (g : grammar) : list frame -> Prop :=
| WF_nil :
    frames_wf g []
| WF_bottom :
    forall xo pre suf v,
      frames_wf g [Fr (Loc xo pre suf) v]
| WF_upper :
    forall x xo pre pre' suf suf' v v' frs,
      In (x, pre' ++ suf') g
      -> frames_wf g (Fr (Loc xo pre (NT x :: suf)) v ::
                      frs)
      -> frames_wf g (Fr (Loc (Some x) pre' suf') v'  ::
                      Fr (Loc xo pre (NT x :: suf)) v ::
                      frs).

Hint Constructors frames_wf.

Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
  match stk with
  | (fr, frs) => frames_wf g (fr :: frs)
  end.

(*
Inductive stack_wf (g : grammar) : parser_stack -> Prop :=
| WF_nil :
    forall pre suf v,
      stack_wf g (Fr (Loc None pre suf) v, [])
| WF_cons :
    forall x xo' pre pre' suf suf' v v' frs,
      In (x, pre ++ suf) g
      -> stack_wf g (Fr (Loc xo' pre' (NT x :: suf')) v', frs) 
      -> stack_wf g (Fr (Loc (Some x) pre suf) v, 
                     Fr (Loc xo' pre' (NT x :: suf')) v' :: frs).

Hint Constructors stack_wf.
 *)

Lemma step_preserves_stack_wf_invar :
  forall g av av' stk stk' ts ts',
    step g (Pst av stk ts) = StepK (Pst av' stk' ts')
    -> stack_wf g stk 
    -> stack_wf g stk'.
Proof.
  intros g av av' stk stk' ts ts' hs hw.
  unfold step in hs.
  repeat (dmeq h); inv hs; tc.
  - (* return *)
    inv hw.
    inv H10; constructor; auto.
    rewrite <- app_assoc; auto.
  - inv hw; auto.
    + constructor; auto.
    + constructor; auto.
      rewrite <- app_assoc; auto.
  - constructor; simpl; auto.
    eapply llPredict_succ_arg_result_in_grammar; eauto.
  - constructor; simpl; auto. 
    eapply llPredict_ambig_arg_result_in_grammar; eauto.
Qed.

Lemma inv_hd_tl :
  forall A (x x' : A) (xs xs' : list A),
    x :: xs = x' :: xs'
    -> x' = x /\ xs' = xs.
Proof.
  intros A x x' xs xs' heq.
  inv heq; auto.
Qed.

Lemma frames_wf_app :
  forall g l,
    frames_wf g l
    -> forall p s,
      l = p ++ s
      -> frames_wf g p /\ frames_wf g s.
Proof.
  intros g l hw.
  induction hw; intros p s heq.
  - symmetry in heq; apply app_eq_nil in heq.
    destruct heq; subst; auto.
  - destruct p as [| fr p]; sis; subst; auto.
    apply inv_hd_tl in heq.
    destruct heq as [hh ht].
    apply app_eq_nil in ht; destruct ht; subst; auto.
  - destruct p as [| fr  p]; sis; subst; auto.
    destruct p as [| fr' p]; sis; subst; inv heq; auto.
    specialize (IHhw (Fr (Loc xo pre (NT x :: suf)) v :: p) s).
    destruct IHhw as [hs hp]; auto.
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

(* The stack symbols that have already been processed represent
   a (partial) derivation; this predicate relates those symbols
   to the word (prefix) involved in the derivation. *)
Inductive stack_derivation (g : grammar) : parser_stack -> list token -> Prop :=
| SD_nil :
    forall xo pre suf v w,
      gamma_derivation g pre w v
      -> stack_derivation g (Fr (Loc xo pre suf) v, []) w
| SD_cons :
    forall xo pre suf v fr' frs wpre wsuf,
      gamma_derivation g pre wsuf v
      -> stack_derivation g (fr', frs) wpre
      -> stack_derivation g (Fr (Loc xo pre suf) v, fr' :: frs) (wpre ++ wsuf).

Hint Constructors stack_derivation.

(* tactic for inverting a stack_derivation hypothesis *)
Ltac inv_sd hsd wpre wsuf hgd hsd' := inversion hsd as [? ? ? ? wpre hgd | ? ? ? ? ? ? wpre wsuf hgd hsd']; subst; clear hsd.

(* Parser invariant: the processed stack symbols represent a 
   partial derivation of a full word *)
Inductive stack_derivation_invar (g : grammar) (stk : parser_stack) (wsuf w : list token) : Prop :=
| SD_invar :
    forall wpre,
      stack_derivation g stk wpre
      -> wpre ++ wsuf = w
      -> stack_derivation_invar g stk wsuf w.

(* Tactic for inverting a stack_derivation_invar hypothesis *)
Ltac inv_sdi wpre hsd :=
  match goal with
  | H : stack_derivation_invar _ _ _ _ |- _ =>
    inversion H as [wpre hsd ?]; subst; clear H
  end.

Lemma stack_derivation_cases :
  forall g fr frs w,
    stack_derivation g (fr, frs) w
    -> match frs with
       | []          => gamma_derivation g fr.(loc).(rpre) w fr.(sem)
       | fr' :: frs' =>
         exists wpre wsuf,
         wpre ++ wsuf = w
         /\ stack_derivation g (fr', frs') wpre
         /\ gamma_derivation g fr.(loc).(rpre) wsuf fr.(sem)
       end.
Proof.
  intros g fr frs w hsd.
  destruct frs as [| fr' frs]; inv hsd; auto.
  repeat eexists; repeat split; auto.
Qed.

(* another invariant *)

Definition nt_unavailable (g : grammar) (x : nonterminal) (av : NtSet.t) : Prop :=
  In x (lhss g) /\ ~ NtSet.In x av.

Definition processed_symbols_all_nullable (g : grammar) (frs : list frame) : Prop :=
  Forall (fun fr => nullable_gamma g fr.(loc).(rpre)) frs.

Hint Constructors Forall.

Definition unavailable_nts_are_open_calls_invar g st : Prop :=
  match st with
  | Pst av (fr, frs) _ =>
    forall (x : nonterminal),
      nt_unavailable g x av
      -> nullable_gamma g fr.(loc).(rpre)
         /\ (exists frs_pre fr_cr frs_suf suf,
                frs = frs_pre ++ fr_cr :: frs_suf
                /\ processed_symbols_all_nullable g frs_pre
                /\ fr_cr.(loc).(rsuf) = NT x :: suf)
  end.

Lemma all_nts_available_no_nt_unavailable :
  forall g x,
    ~ nt_unavailable g x (allNts g).
Proof.
  unfold not; unfold nt_unavailable; intros g x [hi hn].
  apply in_lhss_in_allNts in hi; auto.
Qed.

Lemma unavailable_nts_invar_starts_true :
  forall g ys ts,
    unavailable_nts_are_open_calls_invar g (mkInitState g ys ts).
Proof.
  intros g ys ts; unfold mkInitState; unfold unavailable_nts_are_open_calls_invar.
  intros x hn.
  apply all_nts_available_no_nt_unavailable in hn; inv hn.
Qed.

Lemma nt_unavailable_add :
  forall g x x' av,
    nt_unavailable g x' (NtSet.add x av)
    -> x' <> x /\ nt_unavailable g x' av.
Proof.
  intros g x x' av hn.
  destruct (NF.eq_dec x' x); subst.
  - unfold nt_unavailable in hn; ND.fsetdec.
  - unfold nt_unavailable in *; destruct hn as [hi hn].
    repeat split; auto.
    ND.fsetdec.
Qed.

Lemma nt_unavailable_remove :
  forall g x x' av,
    nt_unavailable g x' (NtSet.remove x av)
    -> x' <> x
    -> nt_unavailable g x' av.
Proof.
  intros g x x' av hn hneq.
  destruct hn as [hi hn].
  split; auto.
  ND.fsetdec.
Qed.

Lemma nullable_split :
  forall g xs ys,
    nullable_gamma g (xs ++ ys)
    -> nullable_gamma g ys.
Proof.
  induction xs; intros.
  - auto.
  - inv H.
    eapply IHxs; eauto.
Qed.

Lemma nullable_app :
  forall g xs ys,
    nullable_gamma g xs
    -> nullable_gamma g ys
    -> nullable_gamma g (xs ++ ys).
Proof.
  intros g xs ys Hng Hng'.
  induction xs as [| x xs]; simpl in *; auto.
  inv Hng.
  constructor; auto.
Qed.

Lemma step_preserves_unavailable_nts_invar :
  forall g st st',
    step g st = StepK st'
    -> stack_wf g st.(stack)
    -> unavailable_nts_are_open_calls_invar g st
    -> unavailable_nts_are_open_calls_invar g st'.
Proof.
  intros g st st' hs hw hu.
  destruct st as [av (fr, frs) ts].
  destruct fr as [[xo pre suf] v]; sis.
  destruct suf as [| [a | x] suf].
  - destruct frs as [| [[xo_prev pre_prev suf_prev] v_prev] frs].
    + destruct ts; tc.
    + destruct suf_prev as [| [a | x] suf_prev]; tc; inv hs.
      unfold unavailable_nts_are_open_calls_invar; sis.
      intros x' hn.
      apply nt_unavailable_add in hn; destruct hn as [hneq hn].
      apply hu in hn; clear hu.
      destruct hn as [hng [frs_pre [fr_cr [frs_suf [suf [heq [hall heq']]]]]]].
      destruct frs_pre as [| fr_pre frs_pre]; sis.
      * inv heq; sis.
        inv heq'; tc.
      * inv heq. 
        inv hall; sis.
        split.
        -- apply nullable_app; auto.
           constructor; auto.
           inv hw; rewrite app_nil_r in *.
           econstructor; eauto.
        -- repeat eexists; repeat split; eauto.
  - destruct ts as [| (a', l) ts]; tc.
    destruct (t_eq_dec a' a); tc; subst; inv hs.
    (* lemma *)
    unfold unavailable_nts_are_open_calls_invar; sis.
    intros x hn.
    apply all_nts_available_no_nt_unavailable in hn; inv hn.
  - destruct (NtSet.mem x av) eqn:hm; tc.
    destruct (llPredict g x _) as [rhs | rhs | | m] eqn:hl; inv hs.
    + unfold unavailable_nts_are_open_calls_invar; sis.
      intros x' hn.
      split; auto.
      destruct (NF.eq_dec x' x); subst.
      * exists [].
        exists (Fr (Loc xo pre (NT x :: suf)) v).
        exists frs.
        exists suf.
        sis.
        repeat split; auto.
        constructor.
      * apply nt_unavailable_remove in hn; auto. 
        apply hu in hn.
        destruct hn as [hng [frs_pre [fr_cr [frs_suf [suf' [heq [hall heq']]]]]]]; subst.
        exists ((Fr (Loc xo pre (NT x :: suf)) v) :: frs_pre).
        exists fr_cr.
        exists frs_suf.
        exists suf'.
        repeat split; auto.
        constructor; auto.
    +  unfold unavailable_nts_are_open_calls_invar; sis.
      intros x' hn.
      split; auto.
      destruct (NF.eq_dec x' x); subst.
      * exists [].
        exists (Fr (Loc xo pre (NT x :: suf)) v).
        exists frs.
        exists suf.
        sis.
        repeat split; auto.
        constructor.
      * apply nt_unavailable_remove in hn; auto. 
        apply hu in hn.
        destruct hn as [hng [frs_pre [fr_cr [frs_suf [suf' [heq [hall heq']]]]]]]; subst.
        exists ((Fr (Loc xo pre (NT x :: suf)) v) :: frs_pre).
        exists fr_cr.
        exists frs_suf.
        exists suf'.
        repeat split; auto.
        constructor; auto.
Qed.