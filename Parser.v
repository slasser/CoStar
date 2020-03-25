Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.SLL_Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.

Module ParserFn (Import D : Defs.T).

  Module Export SP := SllPredictionFn D.

  Inductive parse_error :=
  | InvalidState    : parse_error
  | LeftRecursion   : nonterminal -> parse_error
  | PredictionError : prediction_error -> parse_error.

  (* to do : move this lower *)
  Inductive parse_result := Accept : forest -> parse_result
                          | Ambig  : forest -> parse_result
                          | Reject : string -> parse_result
                          | Error  : parse_error -> parse_result.

  (* cache-optimized version *)

  Inductive step_result :=
  | StepAccept : forest -> step_result
  | StepReject : string -> step_result
  | StepK      : prefix_stack -> suffix_stack -> list token -> NtSet.t
                 -> bool -> cache -> step_result
  | StepError  : parse_error -> step_result.

  Definition step (g  : grammar)
                  (cm : closure_map)
                  (ps : prefix_stack)
                  (ss : suffix_stack)
                  (ts : list token)
                  (av : NtSet.t)
                  (un : bool) 
                  (ca : cache) : step_result := 
    match ps, ss with
    | (PF pre v, p_frs), (SF o suf, s_frs) =>
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
        | PF pre_cr v_cr :: p_frs', SF o_cr suf_cr :: s_frs' =>
          match suf_cr with
          | []                => StepError InvalidState
          | T _  :: _         => StepError InvalidState
          | NT x :: suf_cr'   =>
            let ps' := (PF (NT x :: pre_cr) (Node x (rev v) :: v_cr), p_frs') in
            let ss' := (SF o_cr suf_cr', s_frs')                              in
            StepK ps' ss' ts (NtSet.add x av) un ca          
          end
        | _, _ => StepError InvalidState
        end
      (* terminal case --> consume a token *)
      | T a :: suf' =>
        match ts with
        | []             => StepReject "input exhausted"
        | (a', l) :: ts' =>
          if t_eq_dec a' a then
            let ps' := (PF (T a :: pre) (Leaf a l :: v), p_frs) in
            let ss' := (SF o suf', s_frs)                       in
            StepK ps' ss' ts' (allNts g) un ca
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: _ => 
        if NtSet.mem x av then
          match adaptivePredict g cm x ss ts ca with
          | (PredSucc rhs, ca') =>
            let ps' := (PF [] [], PF pre v :: p_frs)        in
            let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
            StepK ps' ss' ts (NtSet.remove x av) un ca'
          | (PredAmbig rhs, ca') =>
            let ps' := (PF [] [], PF pre v :: p_frs)        in
            let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
            StepK ps' ss' ts (NtSet.remove x av) false ca'
          | (PredReject, _)  =>
            StepReject "prediction found no viable right-hand sides"
          | (PredError e, _) =>
            StepError (PredictionError e) 
          end
        else if NtSet.mem x (allNts g) then
               StepError (LeftRecursion x)
             else
               StepReject "nonterminal not in grammar"
      end
    end.
  
  Lemma step_StepAccept_facts :
    forall g cm ps ss ts av un ca v,
      step g cm ps ss ts av un ca = StepAccept v
      -> ts = []
         /\ exists o, ss = (SF o [], [])
         /\ exists pre,
             ps = (PF pre (rev v), []).
  Proof.
    intros g cm ps ss ts av un ca v hs.
    unfold step in hs; dms; tc.
    inv hs; rewrite rev_involutive; eauto.
  Qed.

  Lemma step_LeftRecursion_facts :
    forall g cm ps ss ts av un ca x,
      step g cm ps ss ts av un ca = StepError (LeftRecursion x)
      -> ~ NtSet.In x av
         /\ NtSet.In x (allNts g)
         /\ exists o suf frs,
             ss = (SF o (NT x :: suf), frs).
  Proof.
    intros g cm ps ss ts av un ca x hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis;
      repeat split; eauto.
    - unfold not; intros hi; apply NtSet.mem_spec in hi; tc.
    - apply NtSet.mem_spec; auto.
  Qed.

  Definition meas (g  : grammar)
                  (ss : suffix_stack)
                  (ts : list token)
                  (av :  NtSet.t) : nat * nat * nat := 
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (List.length ts, stackScore ss (1 + m) e, stackHeight ss).

  Lemma meas_lt_after_return :
    forall g ce cr cr' o o_cr x suf frs ts av,
      ce  = SF o []
      -> cr  = SF o_cr (NT x :: suf)
      -> cr' = SF o_cr suf
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
    forall g cr ce o o' x suf rhs frs ts av,
      cr = SF o (NT x :: suf)
      -> ce = SF o' rhs
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
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca',
      cache_stores_target_results g ca cm
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> lex_nat_triple (meas g ss' ts' av') (meas g ss ts av).
  Proof.
    intros g cm ps ps' ss ss' ts ts' av av' un un' ca ca' hc hs; unfold step in hs.
    destruct ss as ([ o [| [a|x] suf] ], frs).
    - dms; tc; inv hs.
      eapply meas_lt_after_return; eauto.
    - dms; tc; inv hs.
      apply triple_fst_lt; auto.
    - destruct ps as ([pre v], p_frs).
      destruct (NtSet.mem x av) eqn:hm; [.. | dms; tc].
      apply NtSet.mem_spec in hm.
      destruct (adaptivePredict _ _ _ _ _ _) eqn:hp; dms; tc; inv hs.
      + eapply meas_lt_after_push; eauto.
        eapply adaptivePredict_succ_in_grammar; eauto.
      + eapply meas_lt_after_push; eauto.
        eapply adaptivePredict_ambig_in_grammar; eauto.
  Qed.

  Lemma StepK_result_acc :
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca' (a : Acc lex_nat_triple (meas g ss ts av)),
      cache_stores_target_results g ca cm
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> Acc lex_nat_triple (meas g ss' ts' av').
  Proof.
    intros; eapply Acc_inv; eauto.
    eapply step_meas_lt; eauto.
  Defined.

  Lemma step_preserves_cache_invar :
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca',
      cache_stores_target_results g ca cm
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> cache_stores_target_results g ca' cm.
  Admitted.
  
  Fixpoint multistep (g  : grammar)
                     (cm : closure_map)
                     (ps : prefix_stack)
                     (ss : suffix_stack)
                     (ts : list token)
                     (av : NtSet.t)
                     (un : bool)
                     (ca : cache)
                     (hc : cache_stores_target_results g ca cm)
                     (a  : Acc lex_nat_triple (meas g ss ts av))
                     {struct a} : parse_result :=
    match step g cm ps ss ts av un ca as res return step g cm ps ss ts av un ca = res -> _ with
    | StepAccept v                  => fun _  => if un then Accept v else Ambig v
    | StepReject s                  => fun _  => Reject s
    | StepError e                   => fun _  => Error e
    | StepK ps' ss' ts' av' un' ca' =>
      fun hs =>
        let hc' := step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hs
        in  multistep g cm ps' ss' ts' av' un' ca' hc'
                      (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ a hc hs)
    end eq_refl.

  Lemma multistep_unfold :
    forall g cm ps ss ts av un ca a,
      multistep g cm ps ss ts av un ca a =
      match step g cm ps ss ts av un ca as res return step g cm ps ss ts av un ca = res -> _ with
      | StepAccept v                  => fun _  => if un then Accept v else Ambig v
      | StepReject s                  => fun _  => Reject s
      | StepError e                   => fun _  => Error e
      | StepK ps' ss' ts' av' un' ca' =>
        fun hs => multistep g cm ps' ss' ts' av' un' ca' _
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ a hs)
      end eq_refl.
  Proof.
    intros; destruct a; auto.
  Qed.

  (*
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
   *)
  
  Lemma multistep_cases' :
    forall (g   : grammar)
           (cm  : closure_map)
           (ps  : prefix_stack)
           (ss  : suffix_stack)
           (ts  : list token)
           (av  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (a   : Acc lex_nat_triple (meas g ss ts av))
           (sr  : step_result)
           (pr  : parse_result)
           (heq : step g cm ps ss ts av un ca = sr),
      match sr as res return (step g cm ps ss ts av un ca = res -> parse_result) with
      | StepAccept sv                 => fun _ => if un then Accept sv else Ambig sv
      | StepReject s                  => fun _  => Reject s
      | StepK ps' ss' ts' av' un' ca' =>
        fun hs => multistep g cm ps' ss' ts' av' un' ca'
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ a hs)
      | StepError s              => fun _ => Error s
      end heq = pr
      -> match pr with
         | Accept f => (sr = StepAccept f /\ un = true)
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              sr = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Accept f)
         | Ambig f  => (sr = StepAccept f /\ un = false)
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              sr = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Ambig f)
         | Reject s => sr = StepReject s
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              sr = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Reject s)
         | Error s  => sr = StepError s
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              sr = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Error s)
         end.
  Proof.
    intros g cm ps ss ts av un ca a sr pr heq.
    destruct pr; destruct sr; destruct un;
      try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto 10].
  Qed.

  Lemma multistep_cases :
    forall (g   : grammar)
           (cm  : closure_map)
           (ps  : prefix_stack)
           (ss  : suffix_stack)
           (ts  : list token)
           (av  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (a   : Acc lex_nat_triple (meas g ss ts av))
           (pr  : parse_result),
      multistep g cm ps ss ts av un ca a = pr
      -> match pr with
         | Accept f => (step g cm ps ss ts av un ca = StepAccept f /\ un = true)
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Accept f)
         | Ambig f  => (step g cm ps ss ts av un ca = StepAccept f /\ un = false)
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Ambig f)
         | Reject s => step g cm ps ss ts av un ca = StepReject s
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Reject s)
         | Error s  => step g cm ps ss ts av un ca = StepError s
                       \/ (exists ps' ss' ts' av' un' ca' a',
                              step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                              /\ multistep g cm ps' ss' ts' av' un' ca' a' = Error s)
         end.
  Proof.
    intros g cm ps ss ts av un ca a pr hm; subst.
    rewrite multistep_unfold.
    eapply multistep_cases'; eauto.
  Qed.

  Lemma multistep_accept_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a  : Acc lex_nat_triple (meas g ss ts av))
           (f  : forest),
      multistep g cm ps ss ts av un ca a = Accept f
      -> (step g cm ps ss ts av un ca = StepAccept f /\ un = true)
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Accept f).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_ambig_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a  : Acc lex_nat_triple (meas g ss ts av))
           (f  : forest),
      multistep g cm ps ss ts av un ca a = Ambig f
      -> (step g cm ps ss ts av un ca = StepAccept f /\ un = false)
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Ambig f).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_reject_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a  : Acc lex_nat_triple (meas g ss ts av))
           (s  : string),
      multistep g cm ps ss ts av un ca a = Reject s
      -> step g cm ps ss ts av un ca = StepReject s
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Reject s).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_invalid_state_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a  : Acc lex_nat_triple (meas g ss ts av)),
      multistep g cm ps ss ts av un ca a = Error InvalidState
      -> step g cm ps ss ts av un ca = StepError InvalidState
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Error InvalidState).
  Proof.
    intros ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_left_recursion_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a  : Acc lex_nat_triple (meas g ss ts av))
           (x  : nonterminal),
      multistep g cm ps ss ts av un ca a = Error (LeftRecursion x)
      -> step g cm ps ss ts av un ca = StepError (LeftRecursion x)
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Error (LeftRecursion x)).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_prediction_error_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (a   : Acc lex_nat_triple (meas g ss ts av))
           (e   : prediction_error),
      multistep g cm ps ss ts av un ca a = Error (PredictionError e)
      -> step g cm ps ss ts av un ca = StepError (PredictionError e)
         \/ (exists ps' ss' ts' av' un' ca' a',
                step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
                /\ multistep g cm ps' ss' ts' av' un' ca' a' = Error (PredictionError e)).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
    let cm     := mkGraph g           in
    let p_stk0 := (PF [] [], [])      in
    let s_stk0 := (SF None gamma, []) in
    multistep g cm p_stk0 s_stk0 ts (allNts g) true empty_cache (lex_nat_triple_wf _). 
Print Assumptions parse.  
End ParserFn.
