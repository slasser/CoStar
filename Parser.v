Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

Module ParserFn (Import D : Defs.T).

  Module Export PC := PredictionCompleteFn D.

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

  Definition step (g : grammar)
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

  Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
    let p_stk0 := (PF [] [], []) in
    let s_stk0 := (SF gamma, []) in
    multistep g p_stk0 s_stk0 ts (allNts g) true (lex_nat_triple_wf _). 

  (* cache-optimized version *)

  Inductive step_result_opt :=
  | StepAccept_opt : forest -> step_result_opt
  | StepReject_opt : string -> step_result_opt
  | StepK_opt      : prefix_stack -> suffix_stack -> list token -> NtSet.t -> bool -> step_result_opt
  | StepError_opt  : parse_error -> step_result_opt.

  Definition step_opt (g      : grammar)
                      (cm     : PC.PEF.P.SLL.closure_map)
                      (p_stk  : prefix_stack)
                      (s_stk  : suffix_stack)
                      (ts     : list token)
                      (av     : NtSet.t)
                      (u      : bool) : step_result_opt := 
    match p_stk, s_stk with
    | (PF pre v, p_frs), (SF suf, s_frs) =>
      match suf with
      (* no more symbols to process in current frame *)
      | [] =>
        match p_frs, s_frs with
        (* empty stacks --> terminate *)
        | [], [] => 
          match ts with
          | []     => StepAccept_opt (rev v)
          | _ :: _ => StepReject_opt "stack exhausted, tokens remain"
          end
        (* nonempty stacks --> return to caller frames *)
        | PF pre_cr v_cr :: p_frs', SF suf_cr :: s_frs' =>
          match suf_cr with
          | []                => StepError_opt InvalidState
          | T _  :: _         => StepError_opt InvalidState
          | NT x :: suf_cr'   =>
            let p_stk' := (PF (NT x :: pre_cr) (Node x (rev v) :: v_cr), p_frs') in
            let s_stk' := (SF suf_cr', s_frs')                                   in
            StepK_opt p_stk' s_stk' ts (NtSet.add x av) u          end
        | _, _ => StepError_opt InvalidState
        end
      (* terminal case --> consume a token *)
      | T a :: suf' =>
        match ts with
        | []             => StepReject_opt "input exhausted"
        | (a', l) :: ts' =>
          if t_eq_dec a' a then
            let p_stk' := (PF (T a :: pre) (Leaf a l :: v), p_frs) in
            let s_stk' := (SF suf', s_frs)                         in
            StepK_opt p_stk' s_stk' ts' (allNts g) u
          else
            StepReject_opt "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: _ => 
        if NtSet.mem x av then
          match adaptivePredict g cm x s_stk ts with
          | PredSucc rhs =>
            let p_stk' := (PF [] [], PF pre v :: p_frs) in
            let s_stk' := (SF rhs, SF suf :: s_frs)     in
            StepK_opt p_stk' s_stk' ts (NtSet.remove x av) u
          | PredAmbig rhs =>
            let p_stk' := (PF [] [], PF pre v :: p_frs) in
            let s_stk' := (SF rhs, SF suf :: s_frs)     in
            StepK_opt p_stk' s_stk' ts (NtSet.remove x av) false
          | PredReject =>
            StepReject_opt "prediction found no viable right-hand sides"
          | PredError e =>
            StepError_opt (PredictionError e)
          end
        else if NtSet.mem x (allNts g) then
               StepError_opt (LeftRecursion x)
             else
               StepReject_opt "nonterminal not in grammar"
      end
    end.
    
    (* 
  Lemma step_meas_lt_opt :
    forall g p_stk p_stk' s_stk s_stk' ts ts' av av' u u' c c',
      step_opt g p_stk s_stk ts av u c = StepK_opt p_stk' s_stk' ts' av' u' c'
      -> lex_nat_triple (meas g s_stk' ts' av') (meas g s_stk ts av).
  Proof.
    intros g pstk pstk' sstk stk' ts ts' av av' u u' c c' hs; unfold step_opt in hs.
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
     *)
    
  Axiom magic : forall A, A.
    
  Lemma StepK_result_acc_opt :
    forall g cm ps ps' ss ss' ts ts' av av' u u' (a : Acc lex_nat_triple (meas g ss ts av)),
      step_opt g cm ps ss ts av u = StepK_opt ps' ss' ts' av' u'
      -> Acc lex_nat_triple (meas g ss' ts' av').
  Proof.
    intros; eapply Acc_inv; eauto.
    apply magic.
  Defined.
  
  Fixpoint multistep_opt (g  : grammar)
                         cm 
                         (ps : prefix_stack)
                         (ss : suffix_stack)
                         (ts : list token)
                         (av : NtSet.t)
                         (u  : bool)
                         (a  : Acc lex_nat_triple (meas g ss ts av))
                         {struct a} : parse_result :=
    match step_opt g cm ps ss ts av u as res return step_opt g cm ps ss ts av u = res -> _ with
    | StepAccept_opt v             => fun _  => if u then Accept v else Ambig v
    | StepReject_opt s             => fun _  => Reject s
    | StepError_opt e              => fun _  => Error e
    | StepK_opt ps' ss' ts' av' u' =>
      fun hs => multistep_opt g cm ps' ss' ts' av' u'
                              (StepK_result_acc_opt _ _ _ _ _ _ _ _ _ _ _ _ a hs)
    end eq_refl.
  
  Definition parse_opt (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
    let cm     := PC.PEF.P.SLL.mkGraph g      in
    let p_stk0 := (PF [] [], []) in
    let s_stk0 := (SF gamma, []) in
    multistep_opt g cm p_stk0 s_stk0 ts (allNts g) true (lex_nat_triple_wf _). 
  
End ParserFn.
