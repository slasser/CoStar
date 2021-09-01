Require Import FMaps Omega PeanoNat String. 
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.SLLPrediction.
Require Import CoStar.Tactics.
Require Import CoStar.Termination.
Require Import CoStar.Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Module ParserFn (Import D : Defs.T).

  Module Export SLLP := SllPredictionFn D.

  Inductive parse_error :=
  | InvalidState    : parse_error
  | LeftRecursion   : nonterminal -> parse_error
  | PredictionError : prediction_error -> parse_error.

  (* For validation *)
  Definition showParseError (e : parse_error) : string :=
    match e with
    | InvalidState      => "InvalidState"
    | LeftRecursion x   => "LeftRecursion " ++ showNT x
    | PredictionError e => "PredictionError (" ++ showPredictionError e ++ ")"
    end.

  (* to do : move this lower *)
  Inductive parse_result : Type :=
  | Accept : forall (x : nonterminal), nt_semty x -> parse_result
  | Ambig  : forall (x : nonterminal), nt_semty x -> parse_result
  | Reject : string -> parse_result
  | Error  : parse_error -> parse_result. 
  
  (* For validation *)
  Definition showResult (pr : parse_result) : string :=
    match pr with
    | Accept x v => "Accept"
    | Ambig x v  => "Ambig"
    | Reject s   => "Reject: " ++ s
    | Error e    => "Error:  " ++ showParseError e
    end.
  
  Inductive step_result :=
  | StepAccept : forall (x : nonterminal), nt_semty x -> step_result
  | StepReject : string -> step_result
  | StepK      : parser_stack -> list token -> NtSet.t -> bool -> cache -> step_result
  | StepError  : parse_error -> step_result.

  Lemma lhss_invar_eqs :
    forall rm sk x pre vs suf y suf' frs,
      stack_lhss_from_keyset rm sk
      -> sk = (Fr x pre vs suf, frs)
      -> suf = NT y :: suf'
      -> stack_lhss_from_keyset rm (Fr x pre vs (NT y :: suf'), frs).
  Proof.
    intros; subst; auto.
  Qed.
  
  Definition emptyStackMsg (t : token) : string :=
    "parser stack exhausted but tokens remain\n " ++
    "next token: " ++ showToken t.

  Definition emptyInputMsg (a : terminal) : string :=
    "empty input while trying to match terminal " ++ showT a.

  Definition mismatchMsg (a : terminal) (t : token) : string :=
    "terminal mismatch, next parser terminal: " ++ showT a ++
    ", next input token: " ++ showToken t.

  Definition notFoundMsg (x : nonterminal) : string :=
    showNT x ++ " is not a left-hand side in the grammar".

  Definition failedPredictionMsg (x : nonterminal) (ts : list token) : string :=
    "prediction found no viable right-hand sides for " ++ showNT x ++
    match ts with
    | []     => ""
    | t :: _ => ", next token: " ++ showToken t
    end.

  Definition step
             (gr : grammar)
             (hw : grammar_wf gr)
             (rm : rhs_map)
             (cm : closure_map)
             (sk : parser_stack)
             (ts : list token)
             (vi : NtSet.t)
             (un : bool) 
             (ca : cache)
             (hc : cache_stores_target_results rm cm ca)
             (hk : stack_lhss_from_keyset rm sk) : step_result :=
    match sk as sk' return sk = sk' -> _ with
    | (Fr x pre vs suf, frs) =>
      fun hsk =>
        match suf as suf' return suf = suf' -> _ with
        (* no more symbols to process in current frame *)
        | [] =>
          fun _ =>
            match frs with
            (* empty stacks --> terminate *)
            | [] => 
              match ts with
              | [] =>
                match pre, vs with
                | [NT x], (v, tt) => StepAccept x v
                | _, _ => StepError InvalidState
                end
              | t :: _ => StepReject (emptyStackMsg t)
              end
            (* nonempty stacks --> return to caller frames *)
            | Fr x_cr pre_cr vs_cr suf_cr :: frs' =>
              let pre' := rev pre in
              let vs'  := revTuple pre vs in
              match findPredicateAndAction (x, pre') gr hw with
              (* check predicate and reduce *)
              | Some (Some p, f) =>
                if p vs' then
                  let sk' := (Fr x_cr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
                  in  StepK sk' ts (NtSet.remove x vi) un ca
                else
                  StepReject "some failed predicate message here"
              (* reduce *)
              | Some (None, f) =>
                let sk' := (Fr x_cr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
                in  StepK sk' ts (NtSet.remove x vi) un ca
              (* impossible case *)
              | None =>
                StepError InvalidState
              end
            end
        (* terminal case --> consume a token *)
        | T a :: suf' =>
          fun _ => 
            match ts with
            | []             => StepReject (emptyInputMsg a)
            | @existT _ _ a' v :: ts' =>
              if t_eq_dec a' a then
                let sk' := (Fr x (T a' :: pre) (v, vs) suf', frs)
                in  StepK sk' ts' NtSet.empty un ca
              else
                StepReject (mismatchMsg a (@existT _ _ a' v))
            end
        (* nonterminal case --> push a frame onto the stack *)
        | NT y :: suf' =>
          fun hsuf =>
            if NtSet.mem y vi then
              (* Unreachable for a left-recursive grammar *)
              match NM.find y rm with
              | Some _ => StepError (LeftRecursion y) 
              | None   => StepReject (notFoundMsg y)
              end
            else
              match adaptivePredict gr hw rm cm x pre vs y suf' frs ts ca hc
                                    (lhss_invar_eqs _ _ _ _ _ _ _ _ _ hk hsk hsuf)
              with
              | (PredSucc rhs, ca') =>
                let sk' := (Fr y [] tt rhs, Fr x pre vs suf' :: frs) in
                StepK sk' ts (NtSet.add y vi) un ca'
              | (PredAmbig rhs, ca') =>
                let sk' := (Fr y [] tt rhs, Fr x pre vs suf' :: frs) in
                StepK sk' ts (NtSet.add y vi) false ca'
              | (PredReject, _)  =>
                StepReject (failedPredictionMsg y ts)
              | (PredError e, _) =>
                StepError (PredictionError e) 
              end
        end eq_refl
    end eq_refl.

  Lemma step_StepAccept_facts :
    forall pm cm ps ss ts vi un ca hc hk t,
      step pm cm ps ss ts vi un ca hc hk = StepAccept t
      -> ts = []
         /\ exists o, ss = (SF o [], [])
         /\ exists pre,
             ps = (PF pre [t], []).
  Proof.
    intros pm cm ps ss ts vi un ca hc hk t hs.
    unfold step in hs; dms; tc.
    inv hs; eauto.
  Qed.

  Lemma step_LeftRecursion_facts :
    forall pm cm ps ss ts vi un ca hc hk x,
      step pm cm ps ss ts vi un ca hc hk = StepError (LeftRecursion x)
      -> NtSet.In x vi
         /\ (exists yss, NM.find x pm = Some yss)
         /\ (exists o suf frs,
             ss = (SF o (NT x :: suf), frs)).
  Proof.
    intros cm pm ps ss ts vi un ca hc hk x hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis;
      repeat split; eauto.
    apply NF.mem_iff; auto.
  Qed.

  Lemma step_preserves_cache_invar :
    forall pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk,
      step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> cache_stores_target_results pm cm ca'.
  Proof.
    intros pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk hs.
    unfold step in hs; dmeqs H; tc; inv hs; auto.
    - eapply adaptivePredict_succ_preserves_cache_invar;  eauto.
    - eapply adaptivePredict_ambig_preserves_cache_invar; eauto.
  Defined.

  Lemma step_preserves_push_invar :
    forall pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk,
      step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> stack_pushes_from_keyset pm ss'.
  Proof.
    intros pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk hs.
    unfold step in hs; dmeqs H; tc; inv hs; eauto.
    - eapply return_preserves_pushes_invar; eauto.
    - eapply consume_preserves_pushes_invar; eauto.
    - eapply push_preserves_pushes_invar; eauto.
      eapply rhssFor_keySet.
      eapply adaptivePredict_succ_in_rhssFor; eauto.
    - eapply push_preserves_pushes_invar; eauto.
      eapply rhssFor_keySet.
      (* lemma *)
      eapply llPredict_ambig_in_rhssFor; eauto.
      eapply adaptivePredict_ambig_llPredict_ambig; eauto.
  Qed.

  Definition meas (pm : production_map)
                  (ss : suffix_stack)
                  (ts : list token)
                  (vi :  NtSet.t) : nat * nat * nat := 
    let m := maxRhsLength (grammarOf pm)                in
    let e := NtSet.cardinal (NtSet.diff (keySet pm) vi) in
    (List.length ts, stackScore ss (1 + m) e, stackHeight ss).

  Lemma meas_lt_after_return :
    forall pm ce cr cr' o o_cr x suf frs ts vi,
      ce     = SF o []
      -> cr  = SF o_cr (NT x :: suf)
      -> cr' = SF o_cr suf
      -> stack_pushes_from_keyset pm (ce, cr :: frs)
      -> lex_nat_triple (meas pm (cr', frs) ts (NtSet.remove x vi))
                        (meas pm (ce, cr :: frs) ts vi).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? hs;
      subst; unfold meas; inv hs.
    pose proof stackScore_le_after_return as hs.
    eapply le_lt_or_eq in hs; eauto.
    destruct hs as [hlt | heq].
    - apply triple_snd_lt; eauto. 
    - rewrite heq; apply triple_thd_lt; auto.
  Defined.

  Lemma meas_lt_after_push :
    forall pm cr ce o o' x suf rhs frs ts vi,
      cr = SF o (NT x :: suf)
      -> ce = SF o' rhs
      -> In (x, rhs) (grammarOf pm)
      -> ~ NtSet.In x vi
      -> lex_nat_triple (meas pm (ce, cr :: frs) ts (NtSet.add x vi))
                        (meas pm (cr, frs) ts vi).
  Proof.
    intros; subst.
    apply triple_snd_lt.
    eapply stackScore_lt_after_push; eauto.
    eapply grammarOf_keySet; eauto.
  Defined.

  Lemma step_meas_lt :
    forall pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk,
      step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> lex_nat_triple (meas pm ss' ts' vi') (meas pm ss ts vi).
  Proof.
    intros pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk hs; unfold step in hs.
    destruct ss as ([ o [| [a|x] suf] ], frs).
    - dms; tc; inv hs.
      eapply meas_lt_after_return; eauto.
    - dms; tc; inv hs.
      apply triple_fst_lt; auto.
    - destruct ps as ([pre v], p_frs).
      destruct (NtSet.mem x vi) eqn:hm; [dms; tc | ..].
      apply NF.not_mem_iff in hm.
      destruct (adaptivePredict _ _ _ _ _ _ _ _ _ _) eqn:ha; dms; tc; inv hs.
      + eapply meas_lt_after_push; eauto.
        apply rhssFor_grammarOf.
        eapply adaptivePredict_succ_in_rhssFor; eauto.
      + eapply meas_lt_after_push; eauto.
        apply rhssFor_grammarOf.
        (* lemma *)
        eapply llPredict_ambig_in_rhssFor.
        eapply adaptivePredict_ambig_llPredict_ambig; eauto.
  Qed.

  Lemma StepK_result_acc :
    forall pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca'
           hc hk (a : Acc lex_nat_triple (meas pm ss ts vi)),
      step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> Acc lex_nat_triple (meas pm ss' ts' vi').
  Proof.
    intros; eapply Acc_inv; eauto.
    eapply step_meas_lt; eauto.
  Defined.
  
  Fixpoint multistep (pm : production_map)
                     (cm : closure_map)
                     (ps : prefix_stack)
                     (ss : suffix_stack)
                     (ts : list token)
                     (vi : NtSet.t)
                     (un : bool)
                     (ca : cache)
                     (hc : cache_stores_target_results pm cm ca)
                     (hk : stack_pushes_from_keyset pm ss)
                     (ha : Acc lex_nat_triple (meas pm ss ts vi))
                     {struct ha} : parse_result :=
    match step pm cm ps ss ts vi un ca hc hk as res return step pm cm ps ss ts vi un ca hc hk = res -> _ with
    | StepAccept v                  => fun _  => if un then Accept v else Ambig v
    | StepReject s                  => fun _  => Reject s
    | StepError e                   => fun _  => Error e
    | StepK ps' ss' ts' vi' un' ca' =>
      fun hs => multistep pm cm ps' ss' ts' vi' un' ca'
                          (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                          (step_preserves_push_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                          (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
    end eq_refl.

  Lemma multistep_unfold :
    forall pm cm ps ss ts vi un ca hc hk ha,
      multistep pm cm ps ss ts vi un ca hc hk ha =
      match step pm cm ps ss ts vi un ca hc hk as res return step pm cm ps ss ts vi un ca hc hk = res -> _ with
      | StepAccept v                  => fun _  => if un then Accept v else Ambig v
      | StepReject s                  => fun _  => Reject s
      | StepError e                   => fun _  => Error e
      | StepK ps' ss' ts' vi' un' ca' =>
        fun hs => multistep pm cm ps' ss' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_push_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end eq_refl.
  Proof.
    intros; destruct ha; auto.
  Qed.
  
  Lemma multistep_cases' :
    forall (pm  : production_map)
           (cm  : closure_map)
           (ps  : prefix_stack)
           (ss  : suffix_stack)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results pm cm ca)
           (hk  : stack_pushes_from_keyset pm ss)
           (ha  : Acc lex_nat_triple (meas pm ss ts vi))
           (sr  : step_result)
           (pr  : parse_result)
           (heq : step pm cm ps ss ts vi un ca hc hk = sr),
      match sr as res return (step pm cm ps ss ts vi un ca hc hk = res -> parse_result) with
      | StepAccept sv                 => fun _ => if un then Accept sv else Ambig sv
      | StepReject s                  => fun _ => Reject s
      | StepError s                   => fun _ => Error s
      | StepK ps' ss' ts' vi' un' ca' =>
        fun hs => multistep pm cm ps' ss' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_push_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end heq = pr
      -> match pr with
         | Accept f => (sr = StepAccept f /\ un = true)
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              sr = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Accept f)
         | Ambig f  => (sr = StepAccept f /\ un = false)
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              sr = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Ambig f)
         | Reject s => sr = StepReject s
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              sr = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Reject s)
         | Error s  => sr = StepError s
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              sr = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Error s)
         end.
  Proof.
    intros pm cm ps ss ts vi un ca hc hk ha sr pr heq.
    destruct pr; destruct sr; destruct un;
      try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto 12].
  Qed.

  Lemma multistep_cases :
    forall (pm  : production_map)
           (cm  : closure_map)
           (ps  : prefix_stack)
           (ss  : suffix_stack)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results pm cm ca)
           (hk  : stack_pushes_from_keyset pm ss)
           (ha  : Acc lex_nat_triple (meas pm ss ts vi))
           (pr  : parse_result),
      multistep pm cm ps ss ts vi un ca hc hk ha = pr
      -> match pr with
         | Accept f => (step pm cm ps ss ts vi un ca hc hk = StepAccept f /\ un = true)
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Accept f)
         | Ambig f  => (step pm cm ps ss ts vi un ca hc hk = StepAccept f /\ un = false)
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Ambig f)
         | Reject s => step pm cm ps ss ts vi un ca hc hk = StepReject s
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Reject s)
         | Error s  => step pm cm ps ss ts vi un ca hc hk = StepError s
                       \/ (exists ps' ss' ts' vi' un' ca' hc' hk' ha',
                              step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
                              /\ multistep pm cm ps' ss' ts' vi' un' ca' hc' hk' ha' = Error s)
         end.
  Proof.
    intros pm cm ps ss ts vi un ca hc hk ha pr hm; subst.
    rewrite multistep_unfold.
    eapply multistep_cases'; eauto.
  Qed.
  
  Lemma cache_invar_starts_true :
    forall pm cm,
      cache_stores_target_results pm cm empty_cache.
  Proof.
    intros pm cm sps a sps' hf.
    rewrite CacheFacts.empty_o in hf; tc.
  Defined.

  Lemma push_invar_starts_true :
    forall pm x,
      stack_pushes_from_keyset pm (SF None [NT x], []).
  Proof.
    intros pm x; red; auto.
  Qed.

  (* This curried pattern enables us to partially apply the parser to a grammar
     and compute the closure map once, instead of each time we parse an input *)
  Definition parse (g : grammar) : nonterminal -> list token -> parse_result :=
    let pm := mkProductionMap g in
    let cm := mkClosureMap g    in
    fun (x : nonterminal) (ts : list token) =>
      let p_stk0 := (PF []   []    , []) in
      let s_stk0 := (SF None [NT x], []) in
      multistep pm cm p_stk0 s_stk0 ts NtSet.empty true empty_cache
                (cache_invar_starts_true pm cm)
                (push_invar_starts_true _ _)
                (lex_nat_triple_wf _).

End ParserFn.
