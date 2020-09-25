Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.SLLPrediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Module ParserFn (Import D : Defs.T).

  Module Export SOS := SllPredictionCompleteFn D.

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
  Inductive parse_result := Accept : tree -> parse_result
                          | Ambig  : tree -> parse_result
                          | Reject : string -> parse_result
                          | Error  : parse_error -> parse_result.

  (* For validation *)
  Definition showResult (pr : parse_result) : string :=
    match pr with
    | Accept tr => "Accept"
    | Ambig tr  => "Ambig"
    | Reject s  => "Reject: " ++ s
    | Error e   => "Error:  " ++ showParseError e
    end.
  
  Inductive step_result :=
  | StepAccept : tree -> step_result
  | StepReject : string -> step_result
  | StepK      : prefix_stack -> suffix_stack -> list token -> NtSet.t
                 -> bool -> cache -> step_result
  | StepError  : parse_error -> step_result.

  Lemma push_invar_eqs :
    forall pm ss o x suf suf' frs,
      stack_pushes_from_keyset pm ss
      -> ss = (SF o suf, frs)
      -> suf = NT x :: suf'
      -> stack_pushes_from_keyset pm (SF o (NT x :: suf'), frs).
  Proof.
    intros; subst; auto.
  Qed.

  Definition step (pm : production_map)
                  (cm : closure_map)
                  (ps : prefix_stack)
                  (ss : suffix_stack)
                  (ts : list token)
                  (vi : NtSet.t)
                  (un : bool) 
                  (ca : cache)
                  (hc : cache_stores_target_results pm cm ca)
                  (hk : stack_pushes_from_keyset pm ss) : step_result := 
    match ps with
    | (PF pre v, p_frs) =>
      match ss as ss' return ss = ss' -> _ with
      | (SF o suf, s_frs) =>
        fun hss => 
          match suf as suf' return suf = suf' -> _ with
          (* no more symbols to process in current frame *)
          | [] =>
            fun _ => 
              match p_frs, s_frs with
              (* empty stacks --> terminate *)
              | [], [] => 
                match ts with
                | [] =>
                  match v with
                  | [t] => StepAccept t
                  | _   => StepError InvalidState
                  end
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
                  StepK ps' ss' ts (NtSet.remove x vi) un ca          
                end
              | _, _ => StepError InvalidState
              end
          (* terminal case --> consume a token *)
          | T a :: suf' =>
            fun _ => 
              match ts with
              | []             => StepReject "input exhausted"
              | (a', l) :: ts' =>
                if t_eq_dec a' a then
                  let ps' := (PF (T a :: pre) (Leaf a l :: v), p_frs) in
                  let ss' := (SF o suf', s_frs)                       in
                  StepK ps' ss' ts' NtSet.empty un ca
                else
                  StepReject "token mismatch"
              end
          (* nonterminal case --> push a frame onto the stack *)
          | NT x :: suf' =>
            fun hsuf => 
              if NtSet.mem x vi then
                (* Unreachable for a left-recursive grammar *)
                match NM.find x pm with
                | Some _ => StepError (LeftRecursion x) 
                | None   => StepReject "nonterminal not in grammar" 
                end
              else
                match adaptivePredict pm cm o x suf' s_frs ts ca hc
                                      (push_invar_eqs _ _ _ _ _ _ _ hk hss hsuf)
                with
                | (PredSucc rhs, ca') =>
                  let ps' := (PF [] [], PF pre v :: p_frs)        in
                  let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
                  StepK ps' ss' ts (NtSet.add x vi) un ca'
                | (PredAmbig rhs, ca') =>
                  let ps' := (PF [] [], PF pre v :: p_frs)        in
                  let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
                  StepK ps' ss' ts (NtSet.add x vi) false ca'
                | (PredReject, _)  =>
                  StepReject "prediction found no viable right-hand sides"
                | (PredError e, _) =>
                  StepError (PredictionError e) 
                end
          end eq_refl
      end eq_refl
    end.
  
(*  Definition step (pm : production_map)
                  (cm : closure_map)
                  (ps : prefix_stack)
                  (ss : suffix_stack)
                  (ts : list token)
                  (vi : NtSet.t)
                  (un : bool) 
                  (ca : cache)
                  (hc : cache_stores_target_results pm cm ca)
                  (hk : stack_pushes_from_keyset pm ss) : step_result := 
    match ps as , ss as ps', ss' return ps, ss = ps', ss' with
    | (PF pre v, p_frs), (SF o suf, s_frs) =>
      match suf with
      (* no more symbols to process in current frame *)
      | [] =>
        match p_frs, s_frs with
        (* empty stacks --> terminate *)
        | [], [] => 
          match ts with
          | [] =>
            match v with
            | [t] => StepAccept t
            | _   => StepError InvalidState
            end
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
            StepK ps' ss' ts (NtSet.remove x vi) un ca          
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
            StepK ps' ss' ts' NtSet.empty un ca
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: suf' => 
        if NtSet.mem x vi then
          (* Unreachable for a left-recursive grammar *)
          match NM.find x pm with
          | Some _ => StepError (LeftRecursion x) 
          | None   => StepReject "nonterminal not in grammar" 
          end
        else
          match adaptivePredict pm cm o x suf s_frs ts ca hc _ with
          | (PredSucc rhs, ca') =>
            let ps' := (PF [] [], PF pre v :: p_frs)        in
            let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
            StepK ps' ss' ts (NtSet.add x vi) un ca'
          | (PredAmbig rhs, ca') =>
            let ps' := (PF [] [], PF pre v :: p_frs)        in
            let ss' := (SF (Some x) rhs, SF o suf :: s_frs) in
            StepK ps' ss' ts (NtSet.add x vi) false ca'
          | (PredReject, _)  =>
            StepReject "prediction found no viable right-hand sides"
          | (PredError e, _) =>
            StepError (PredictionError e) 
          end
      end
    end.
 *)

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

(*  Lemma multistep_accept_cases :
    forall (gr : grammar)
           (pm  : production_map)
           (hp  : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av))
           (t  : tree),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Accept t
      -> (step gr pm hp cm ps ss ts vi un ca = StepAccept t /\ un = true)
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Accept t).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_ambig_cases :
    forall (gr : grammar)
           (pm : production_map)
           (hp : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av))
           (t  : tree),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Ambig t 
      -> (step gr pm hp cm ps ss ts vi un ca = StepAccept t /\ un = false)
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Ambig t).

  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_reject_cases :
    forall (gr : grammar)
           (pm : production_map)
           (hp : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av))
           (s  : string),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Reject s
      -> step gr pm hp cm ps ss ts vi un ca = StepReject s
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Reject s).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hm; subst. 
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_invalid_state_cases :
    forall (gr : grammar)
           (pm : production_map)
           (hp : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av)),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Error InvalidState
      -> step gr pm hp cm ps ss ts vi un ca = StepError InvalidState
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Error InvalidState).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_left_recursion_cases :
    forall (gr : grammar)
           (pm : production_map)
           (hp : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av))
           (x  : nonterminal),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Error (LeftRecursion x)
      -> step gr pm hp cm ps ss ts vi un ca = StepError (LeftRecursion x)
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Error (LeftRecursion x)).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.

  Lemma multistep_prediction_error_cases :
    forall (gr : grammar)
           (pm : production_map)
           (hp : production_map_correct pm gr)
           (cm : closure_map)
           (ps : prefix_stack)
           (ss : suffix_stack)
           (ts : list token)
           (av : NtSet.t)
           (un : bool)
           (ca : cache)
           (hc : cache_stores_target_results gr pm hp cm ca)
           (ha : Acc lex_nat_triple (meas gr ss ts av))
           (e  : prediction_error),
      multistep gr pm hp cm ps ss ts vi un ca hc ha = Error (PredictionError e)
      -> step gr pm hp cm ps ss ts vi un ca = StepError (PredictionError e)
         \/ (exists ps' ss' ts' vi' un' ca' hc' ha',
                step gr pm hp cm ps ss ts vi un ca = StepK ps' ss' ts' vi' un' ca'
                /\ multistep gr pm hp cm ps' ss' ts' vi' un' ca' hc' ha' = Error (PredictionError e)).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? hm; subst.
    destruct (multistep_cases _ _ _ _ _ _ _ _ _ _ _ _ _ hm); auto.
  Qed.
 *)
  
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
