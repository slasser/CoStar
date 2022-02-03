Require Import FMaps PeanoNat String. 
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.SLLPrediction_complete.
Require Import CoStar.Tactics.
Require Import CoStar.Termination.
Require Import CoStar.Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Module ParserFn (Import D : Defs.T).

  Module Export SLLPC := SllPredictionCompleteFn D.

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
 
  Inductive step_result : Type :=
  | StepAccept : forall (x : nonterminal), nt_semty x -> step_result 
  | StepReject : string -> step_result
  | StepK      : parser_stack -> list token -> NtSet.t -> bool -> cache -> step_result
  | StepError  : parse_error -> step_result.

  Lemma lhss_invar_eqs :
    forall rm sk pre vs suf x suf' frs,
      stack_pushes_from_keyset rm sk
      -> sk = (Fr pre vs suf, frs)
      -> suf = NT x :: suf'
      -> stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf'), frs).
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
             (hk : stack_pushes_from_keyset rm sk) : step_result :=
    match sk as sk' return sk = sk' -> _ with
    | (Fr pre vs suf, frs) =>
      fun hsk =>
        match suf as suf' return suf = suf' -> _ with
        (* no more symbols to process in current frame *)
        | [] =>
          fun _ =>
            match frs with
            (* empty stack --> terminate *)
            | [] => 
              match ts with
              | [] =>
                match pre, vs with
                | [NT x], (v, tt) => StepAccept x v
                | _, _ => StepError InvalidState
                end
              | t :: _ => StepReject (emptyStackMsg t)
              end
            (* nonempty stack --> return to caller frame *)
            | Fr pre_cr vs_cr (NT x :: suf_cr) :: frs' =>
              let pre' := rev pre in
              let vs'  := revTuple pre vs in
              match findPredicateAndAction (x, pre') gr hw with
              (* check predicate and reduce *)
              | Some (p, f) =>
                if p vs' then
                  let sk' := (Fr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
                  in  StepK sk' ts (NtSet.remove x vi) un ca
                else
                  StepReject "some failed predicate message here"
              (* impossible case *)
              | None =>
                StepError InvalidState
              end
            | _ => StepError InvalidState
            end
        (* terminal case --> consume a token *)
        | T a :: suf' =>
          fun _ => 
            match ts with
            | []             => StepReject (emptyInputMsg a)
            | @existT _ _ a' v :: ts' =>
              if t_eq_dec a' a then
                let sk' := (Fr (T a' :: pre) (v, vs) suf', frs)
                in  StepK sk' ts' NtSet.empty un ca
              else
                StepReject (mismatchMsg a (@existT _ _ a' v))
            end
        (* nonterminal case --> push a frame onto the stack *)
        | NT x :: suf' =>
          fun hsuf =>
            if NtSet.mem x vi then
              (* Unreachable for a left-recursive grammar *)
              match NM.find x rm with
              | Some _ => StepError (LeftRecursion x) 
              | None   => StepReject (notFoundMsg x)
              end
            else
              match adaptivePredict gr hw rm cm pre vs x suf' frs ts ca hc
                                    (lhss_invar_eqs _ _ _ _ _ _ _ _ hk hsk hsuf)
              with
              | (PredSucc rhs, ca') =>
                let sk' := (Fr [] tt rhs, Fr pre vs (NT x :: suf') :: frs) in
                StepK sk' ts (NtSet.add x vi) un ca'
              | (PredAmbig rhs, ca') =>
                let sk' := (Fr [] tt rhs, Fr pre vs (NT x :: suf') :: frs) in
                StepK sk' ts (NtSet.add x vi) false ca'
              | (PredReject, _)  =>
                StepReject (failedPredictionMsg x ts)
              | (PredError e, _) =>
                StepError (PredictionError e) 
              end
        end eq_refl
    end eq_refl.

  Lemma step_StepAccept_facts :
    forall gr hw rm cm sk ts vi un ca hc hk x v,
      step gr hw rm cm sk ts vi un ca hc hk = StepAccept x v
      -> ts = []
         /\ sk = (Fr [NT x] (v, tt) [], []).
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk y v hs.
    unfold step in hs; dms; tc.
    inv hs; auto. 
  Qed.

  Lemma step_LeftRecursion_facts :
    forall gr hw rm cm sk ts vi un ca hc hk x,
      step gr hw rm cm sk ts vi un ca hc hk = StepError (LeftRecursion x)
      -> NtSet.In x vi
         /\ (exists yss, NM.find x rm = Some yss)
         /\ (exists pre vs suf frs,
             sk = (Fr pre vs (NT x :: suf), frs)). 
  Proof.
    intros gr hw cm rm sk ts vi un ca hc hk x hs.
    unfold step in hs; repeat dmeq h; tc; inv hs; sis;
      repeat split; eauto.
    apply NF.mem_iff; auto.
  Qed.

  Lemma step_preserves_cache_invar :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hs.
    unfold step in hs; dmeqs H; tc; inv hs; auto.
    - eapply adaptivePredict_succ_preserves_cache_invar;  eauto.
    - eapply adaptivePredict_ambig_preserves_cache_invar; eauto.
  Defined.

  Lemma step_preserves_pki :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      rhs_map_correct rm gr
      -> step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> stack_pushes_from_keyset rm sk'.
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hr hs.
    unfold step in hs; dmeqs H; tc; inv hs; red; red in hk; sis.
    - eapply return_preserves_keyset_invar; eauto.
    - eapply consume_preserves_keyset_invar; eauto.
    - eapply push_preserves_keyset_invar; eauto.
      eapply rhssFor_keySet.
      eapply adaptivePredict_succ_in_rhssFor; eauto.
    - eapply push_preserves_keyset_invar; eauto.
      eapply rhssFor_keySet.
      eapply llPredict_ambig_in_rhssFor; eauto.
      eapply adaptivePredict_ambig_llPredict_ambig; eauto.
  Qed.

  Definition bottom_stack_sym_eq_start_sym (sk : parser_stack) (x : nonterminal) : Prop :=
    bottomFrameSyms sk = [NT x].

  Lemma step_preserves_bfs_invar :
    forall gr hw x rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      bottom_stack_sym_eq_start_sym sk x
      -> step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> bottom_stack_sym_eq_start_sym sk' x.
  Proof.
    intros gr hw x rm cm (fr, frs) (fr', frs') ts ts' vi vi' un un' ca ca' hc hk hb hs.
    unfold step in hs; dmeqs H; tc; inv hs; inv hb;
      unfold bottom_stack_sym_eq_start_sym in *; unfold bottomFrameSyms in *; auto.
    - destruct frs'; sis; auto; apps.
    - destruct frs'; sis; auto; apps.
  Qed.

  Lemma step_accept_result_eq_start :
    forall gr hw rm cm sk ts vi un ca hc hk x x' v,
      bottom_stack_sym_eq_start_sym sk x
      -> step gr hw rm cm sk ts vi un ca hc hk = StepAccept x' v
      -> x' = x.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk x x' v hb hs.
    apply step_StepAccept_facts in hs.
    destruct hs as (heq & heq'); subst.
    inv hb; auto.
  Qed.
        
  (* termination-related lemmas for the multistep function below *)
  
  Definition parser_meas
             (rm : rhs_map)
             (sk : parser_stack)
             (ts : list token)
             (vi :  NtSet.t) : nat * nat * nat :=
    let (stkScore, stkHeight) := meas rm vi (stackSuffixes sk)
    in  (List.length ts, stkScore, stkHeight).

  Lemma parser_meas_lt_after_return :
    forall rm ce cr cr' pre pre' pre'' vs vs' vs'' x suf frs ts vi,
      ce     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr pre'' vs'' suf
      -> stack_pushes_from_keyset rm (ce, cr :: frs)
      -> lex_nat_triple (parser_meas rm (cr', frs) ts (NtSet.remove x vi))
                        (parser_meas rm (ce, cr :: frs) ts vi).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? hk; subst; unfold meas.
    red in hk.
    eapply meas_lt_after_return with (vi := vi) in hk; sis; eauto.
    inversion hk as [ ? ? ? ? hl | ? ? ? hl heq heq']; subst; clear hk.
    - apply triple_snd_lt; auto.
    - unfold parser_meas; sis; rewrite heq'.
      apply triple_thd_lt; auto.
  Defined.

  Lemma parser_meas_lt_after_push :
    forall rm cr ce pre vs x suf rhs frs ts vi,
      cr = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> In rhs (rhssFor x rm)
      -> NtSet.mem x vi = false 
      -> lex_nat_triple (parser_meas rm (ce, cr :: frs) ts (NtSet.add x vi))
                        (parser_meas rm (cr, frs) ts vi).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hi hm; subst.
    apply triple_snd_lt.
    eapply stackScore_lt_after_push; sis; auto.
    - eapply rhssFor_keySet; eauto.
    - apply NF.not_mem_iff in hm; auto.
    - eapply rhssFor_allRhss; eauto.
  Defined.
  
  Lemma step_parser_meas_lt :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> lex_nat_triple (parser_meas rm sk' ts' vi') (parser_meas rm sk ts vi).
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk hs; unfold step in hs.
    destruct sk as ([pre vs suf], frs).
    dmeqs H; tc; inv hs.
    - eapply parser_meas_lt_after_return with (pre'' := NT _ :: _); eauto.
    - apply triple_fst_lt; auto.
    - eapply parser_meas_lt_after_push; eauto.
      eapply adaptivePredict_succ_in_rhssFor; eauto.
    - eapply parser_meas_lt_after_push; eauto.
      eapply llPredict_ambig_in_rhssFor; eauto.
      eapply adaptivePredict_ambig_llPredict_ambig; eauto.
  Qed.

  Lemma StepK_result_acc :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca'
           hc hk (a : Acc lex_nat_triple (parser_meas rm sk ts vi)),
      step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> Acc lex_nat_triple (parser_meas rm sk' ts' vi').
  Proof.
    intros; eapply Acc_inv; eauto.
    eapply step_parser_meas_lt; eauto.
  Defined.

  Inductive parse_result (x : nonterminal) : Type :=
  | Accept : nt_semty x  -> parse_result x
  | Ambig  : nt_semty x  -> parse_result x
  | Reject : string      -> parse_result x
  | Error  : parse_error -> parse_result x.
  
  (* For validation *)
  Definition showResult (x : nonterminal) (pr : parse_result x) : string :=
    match pr with
    | Accept _ v => "Accept"
    | Ambig  _ v => "Ambig"
    | Reject _ s => "Reject: " ++ s
    | Error  _ e => "Error:  " ++ showParseError e
    end.

  Fixpoint multistep
           (gr : grammar)
           (hw : grammar_wf gr)
           (rm : rhs_map)
           (hr : rhs_map_correct rm gr)
           (cm : closure_map)
           (x  : nonterminal)
           (sk : parser_stack)
           (ts : list token)
           (vi : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results rm cm ca)
           (hk : stack_pushes_from_keyset rm sk)
           (hb : bottom_stack_sym_eq_start_sym sk x)
           (ha : Acc lex_nat_triple (parser_meas rm sk ts vi))
           {struct ha} : parse_result x :=
    match step gr hw rm cm sk ts vi un ca hc hk as res return step gr hw rm cm sk ts vi un ca hc hk = res -> _ with
    | StepAccept x' v' =>
      fun hs  =>
        let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
        in  if un then Accept x v else Ambig x v
    | StepReject s              => fun _  => Reject _ s
    | StepError e               => fun _  => Error  _ e
    | StepK sk' ts' vi' un' ca' =>
      fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                          (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                          (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                          (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                          (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
    end eq_refl.

  Lemma multistep_unfold :
    forall gr hw rm hr cm x sk ts vi un ca hc hk hb ha,
      multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha =
      match step gr hw rm cm sk ts vi un ca hc hk as res return step gr hw rm cm sk ts vi un ca hc hk = res -> _ with
      | StepAccept x' v' =>
        fun hs =>
          let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
          in  if un then Accept x v else Ambig x v
      | StepReject s                  => fun _  => Reject _ s
      | StepError e                   => fun _  => Error  _ e
      | StepK sk' ts' vi' un' ca' =>
        fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                            (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end eq_refl.
  Proof.
    intros; destruct ha; auto.
  Qed.
  
  Lemma multistep_cases' :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (rm  : rhs_map)
           (hr  : rhs_map_correct rm gr)
           (cm  : closure_map)
           (x   : nonterminal)
           (sk  : parser_stack)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hk  : stack_pushes_from_keyset rm sk)
           (hb  : bottom_stack_sym_eq_start_sym sk x)
           (ha  : Acc lex_nat_triple (parser_meas rm sk ts vi))
           
           (sr  : step_result)
           (pr  : parse_result x)
           (heq : step gr hw rm cm sk ts vi un ca hc hk = sr),
      match sr as res return (step gr hw rm cm sk ts vi un ca hc hk = res -> parse_result x) with
      | StepAccept x' v' =>
        fun hs =>
          let v := cast_nt_semty x' x (step_accept_result_eq_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs) v'
          in  if un then Accept x v else Ambig x v
      | StepReject s                  => fun _ => Reject _ s
      | StepError s                   => fun _ => Error _ s
      | StepK sk' ts' vi' un' ca' =>
        fun hs => multistep gr hw rm hr cm x sk' ts' vi' un' ca'
                            (step_preserves_cache_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hs)
                            (step_preserves_pki _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk hr hs)
                            (step_preserves_bfs_invar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hs)
                            (StepK_result_acc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk ha hs)
      end heq = pr
      -> match pr with
         | Accept _ f => (sr = StepAccept x f /\ un = true)
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Accept x f)
         | Ambig _ f  => (sr = StepAccept x f /\ un = false)
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Ambig x f)
         | Reject _ s => sr = StepReject s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Reject _ s)
         | Error _ s  => sr = StepError s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              sr = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Error _ s)
         end.
  Proof.
    intros gr hw rm hr cm x sk ts vi un ca hc hk hb ha sr pr heq.
    destruct pr; destruct sr; destruct un;
      try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto 12].
    - pose proof heq as heq'.
      eapply step_accept_result_eq_start in heq'; eauto; subst.
      rewrite cast_nt_semty_refl; simpl.
      intros heq'; inv heq'; auto.
    - pose proof heq as heq'.
      eapply step_accept_result_eq_start in heq'; eauto; subst.
      rewrite cast_nt_semty_refl; simpl.
      intros heq'; inv heq'; auto.
  Qed.

  Lemma multistep_cases :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (rm  : rhs_map)
           (hr  : rhs_map_correct rm gr)
           (cm  : closure_map)
           (sk  : parser_stack)
           (x   : nonterminal)
           (ts  : list token)
           (vi  : NtSet.t)
           (un  : bool)
           (ca  : cache)
           (hc  : cache_stores_target_results rm cm ca)
           (hb  : bottom_stack_sym_eq_start_sym sk x)
           (hk  : stack_pushes_from_keyset rm sk)
           (ha  : Acc lex_nat_triple (parser_meas rm sk ts vi))
           (pr  : parse_result x),
      multistep gr hw rm hr cm x sk ts vi un ca hc hk hb ha = pr
      -> match pr with
         | Accept _ f => (step gr hw rm cm sk ts vi un ca hc hk = StepAccept x f /\ un = true)
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
                                /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Accept x f)
         | Ambig _ f  => (step gr hw rm cm sk ts vi un ca hc hk = StepAccept x f /\ un = false)
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
                                /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Ambig x f)
         | Reject _ s => step gr hw rm cm sk ts vi un ca hc hk = StepReject s
                         \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                                step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Reject x s)
         | Error _ s  => step gr hw rm cm sk ts vi un ca hc hk = StepError s
                       \/ (exists sk' ts' vi' un' ca' hc' hk' hb' ha',
                              step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
                              /\ multistep gr hw rm hr cm x sk' ts' vi' un' ca' hc' hk' hb' ha' = Error x s)
         end.
  Proof.
    intros gr hw rm hr cm x sk ts vi un ca hc hk hb ha pr hm; subst.
    rewrite multistep_unfold.
    eapply multistep_cases'; eauto.
  Qed.
  
  Lemma cache_invar_starts_true :
    forall rm cm,
      cache_stores_target_results rm cm empty_cache.
  Proof.
    intros rm cm sps a sps' hf.
    rewrite CacheFacts.empty_o in hf; tc.
  Defined.

  Lemma push_invar_starts_true :
    forall rm x,
      stack_pushes_from_keyset rm (Fr [] tt [NT x], []). 
  Proof.
    intros rm x; repeat red; sis; auto.
  Qed.

  Lemma bottom_stack_sym_invar_start_true :
    forall x,
      bottom_stack_sym_eq_start_sym (Fr [] tt [NT x], []) x.
  Proof.
    intros x; red; auto.
  Qed.

  (* This curried pattern enables us to partially apply the parser to a grammar
     and compute the closure map once, instead of each time we parse an input *)
  Definition parse (gr : grammar) (hw : grammar_wf gr) : forall (x : nonterminal), list token -> parse_result x :=
    let rm := mkRhsMap gr         in
    let hr := mkRhsMap_correct gr in
    let cm := mkClosureMap gr     in
    fun (x : nonterminal) (ts : list token) =>
      let sk0 := (Fr [] tt [NT x], []) in
      multistep gr hw rm hr cm x sk0 ts NtSet.empty true empty_cache
                (cache_invar_starts_true rm cm)
                (push_invar_starts_true _ _)
                (bottom_stack_sym_invar_start_true _)
                (lex_nat_triple_wf _).

End ParserFn.
