Require Import FMaps List MSets Program.Wf.
Require Import GallStar.Lex.
Require Import GallStar.LLPrediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module SllPredictionFn (Import D : Defs.T).

  Module Export PC := PredictionCompleteFn D.
  
  (* First, some static analysis over a grammar *)

  Lemma suffix_frame_eq_dec :
    forall fr fr' : suffix_frame, {fr = fr'} + {fr <> fr'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Qed.

  Module MDT_SF.
    Definition t       := suffix_frame.
    Definition eq_dec  := suffix_frame_eq_dec.
  End MDT_SF.
  Module SF_as_DT      := Make_UDT(MDT_SF).
  Module FrameSet      := MSetWeakList.Make SF_as_DT.
  Module FrameSetFacts := WFactsOn SF_as_DT FrameSet.
  Module FrameMap      := FMapWeakList.Make SF_as_DT.

  Definition edge := (suffix_frame * suffix_frame)%type.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

  Lemma edge_eq_dec :
    forall e e' : edge, {e = e'} + {e <> e'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Qed.

  Module MDT_Edge.
    Definition t      := edge.
    Definition eq_dec := edge_eq_dec.
  End MDT_Edge.
  Module Edge_as_DT   := Make_UDT(MDT_Edge).
  Module EdgeSet      := MSetWeakList.Make Edge_as_DT.
  Module EdgeSetFacts := WFactsOn Edge_as_DT EdgeSet.

  Module FS := FrameSet.
  Module FM := FrameMap.
  Module ES := EdgeSet.
  
  Definition oneToMany {A B : Type} (s : A) (ds : list B) : list (A * B) :=
    map (pair s) ds.

  Definition beqNt x x' : bool :=
    match nt_eq_dec x' x with
    | left _ => true
    | right _ => false
    end.

  Fixpoint prodsOf (x : nonterminal) (ps : list production) := 
    filter (fun p => beqNt x (lhs p)) ps.

  Fixpoint pushEdges' (g : grammar) (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with 
    | []          => []
    | T _ :: ys'  => pushEdges' g x ys'
    | NT y :: ys' =>
      let es := map (fun rhs => (SF (Some x) ys, SF (Some y) rhs))
                    (rhssForNt g y)
      in  es ++ pushEdges' g x ys'
    end.

  Definition pushEdges (g : grammar) : list edge :=
    flat_map (fun p => pushEdges' g (lhs p) (rhs p)) g.

  Fixpoint returnEdges' (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with
    | []          => []
    | T _ :: ys'  => returnEdges' x ys'
    | NT y :: ys' =>
      (SF (Some y) [], SF (Some x) ys') :: returnEdges' x ys'
    end.

  Definition returnEdges (g : grammar) : list edge :=
    flat_map (fun p => returnEdges' (lhs p) (rhs p)) g.

  Definition finalEdges g : list edge :=
    map (fun x => (SF (Some x) [], SF None [])) (lhss g).

  Definition fromEdgelist (es : list edge) : ES.t :=
    fold_right ES.add ES.empty es.

  Definition epsilonEdges g : list edge :=
    pushEdges g ++ returnEdges g ++ finalEdges g.

  Fixpoint dsts (es : list edge) (s : suffix_frame) : list suffix_frame :=
    match es with
    | []             => []
    | (s', d) :: es' =>
      if suffix_frame_eq_dec s' s then d :: dsts es' s else dsts es' s
    end.

  Definition mem (e : edge) (es : list edge) : bool :=
    if in_dec edge_eq_dec e es then true else false.

  Definition newEdges' (es : list edge) (e : edge) : list edge :=
    let (a, b) := e in
    let cs     := filter (fun c => negb (mem (a, c) es)) (dsts es b)
    in  oneToMany a cs.

  Definition newEdges (es : list edge) : list edge :=
    flat_map (newEdges' es) es.

  Definition sources es := map src es.
  Definition dests   es := map dst es.

  Definition allEdges es := 
    let ss := sources es in
    let ds := dests   es in
    flat_map (fun s => oneToMany s ds) ss.

  Definition stable (fr : suffix_frame) : bool :=
    match fr with
    | SF None []             => true
    | SF (Some x) (T _ :: _) => true
    | _                      => false
    end.

  Fixpoint stablePositions' x ys : list suffix_frame :=
    match ys with
    | []          => []
    | T a :: ys'  => SF (Some x) ys :: stablePositions' x ys'
    | NT _ :: ys' => stablePositions' x ys'
    end.

  Definition stablePositions (g : grammar) : list suffix_frame :=
    SF None [] :: flat_map (fun p => stablePositions' (lhs p) (rhs p)) g.

  (* might not be necessary *)
  Definition reflEdges (g : grammar) : list edge :=
    map (fun p => (p, p)) (stablePositions g).

  Definition m (es : list edge) : nat :=
    ES.cardinal (ES.diff (fromEdgelist (allEdges es)) (fromEdgelist es)).

  Axiom magic : forall A, A.

  Program Fixpoint transClosure (es : list edge)
          { measure (m es) } : list edge :=
    let es' := newEdges es in
    match es' as es'' return es' = es'' -> _ with
    | []     => fun _   => es
    | _ :: _ => fun heq => transClosure (es' ++ es)
    end eq_refl.
  Next Obligation.
    rewrite heq; simpl.
    unfold m.
    apply magic.
  Defined.

  Definition dstStable (e : edge) : bool :=
    let (_, b) := e in stable b.

  Definition stableEdges (es : list edge) : list edge :=
    filter dstStable es.

  Definition mkGraphEdges (g : grammar) : list edge :=
    stableEdges (transClosure (epsilonEdges g)) ++ (reflEdges g).

  (* A closure graph is a map where each key K is a grammar position
     and each value V is a set of positions that are epsilon-reachable from K *)
  Definition closure_map := FM.t FS.t.

  Definition addEdge (e : edge) (m : closure_map) : closure_map :=
    let (k, v) := e in
    match FM.find k m with
    | Some vs => FM.add k (FS.add v vs) m
    | None    => FM.add k (FS.singleton v) m
    end.

  Definition fromEdges (es : list edge) : closure_map :=
    fold_right addEdge (FM.empty FS.t) es.

  Definition mkGraph (g : grammar) : closure_map :=
    fromEdges (mkGraphEdges g).

  Definition destFrames (cm : closure_map) (fr : suffix_frame) : list suffix_frame :=
    match FM.find fr cm with
    | Some s => FS.elements s
    | None   => []
    end.

  (* Now for the parts that correspond to the LL prediction module *)

  Definition simReturn (cm : closure_map) (sp : subparser) : option (list subparser) :=
    match sp with
    | Sp pred (SF (Some x) [], []) =>
      let dsts := destFrames cm (SF (Some x) []) in
      let sps' := map (fun d => Sp pred (d, [])) dsts
      in  Some sps'
    | _ => None
    end.

  Lemma simReturn_preserves_prediction :
    forall cm sp sp' sps',
      simReturn cm sp = Some sps'
      -> In sp' sps'
      -> prediction sp' = prediction sp.
  Proof.
    intros cm [pred (fr, frs)] sp' sps' hs hi; sis; dms; tc; inv hs.
    apply in_map_iff in hi; destruct hi as [? [? ?]]; subst; auto.
  Qed.
  
  Fixpoint sllc' (g  : grammar)
                 (cm : closure_map)
                 (av : NtSet.t)
                 (sp : subparser)
                 (a  : Acc lex_nat_pair (meas g av sp))
    : closure_result :=
    match simReturn cm sp with
    | Some sps' => inr sps'
    | None      =>
      match spClosureStep g av sp as r return spClosureStep g av sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hin =>
                                  sllc' g cm av' sp'
                                            (acc_after_step _ _ _ _ hs hin a))
          in  aggrClosureResults crs
      end eq_refl
    end.

  Lemma sllc'_unfold :
    forall g cm av sp a,
      sllc' g cm av sp a =
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match spClosureStep g av sp as r return spClosureStep g av sp = r -> _ with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK av' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hin =>
                                    sllc' g cm av' sp'
                                          (acc_after_step _ _ _ _ hs hin a))
            in  aggrClosureResults crs
        end eq_refl
      end.
  Proof.
    intros g cm av sp a; destruct a; auto. 
  Qed.

  Lemma sllc'_cases' :
    forall (g   : grammar)
           (cm  : closure_map)
           (av  : NtSet.t)
           (sp  : subparser)
           (a   : Acc lex_nat_pair (meas g av sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result)
           (heq : spClosureStep g av sp = sr),
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sr as r return spClosureStep g av sp = r -> closure_result with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK av' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hin => sllc' g cm av' sp'
                                                       (acc_after_step _ _ _ _ hs hin a))
            in  aggrClosureResults crs
        end heq
      end = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : spClosureStep g av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc' g cm av' sp'
                                       (acc_after_step _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ (sr = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (av'  : NtSet.t)
                     (hs   : spClosureStep g av sp = CstepK av' sps')
                     (crs  : list closure_result),
               crs = dmap sps' (fun sp' hi => 
                                  sllc' g cm av' sp'
                                        (acc_after_step _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inr sps
         end.
  Proof.
    intros g cm av sp a sr cr heq.
    dms; tc; intros heq'; try solve [inv heq'; eauto | eauto 8].
  Qed.
  
  Lemma sllc'_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (sp : subparser)
           (av : NtSet.t)
           (a  : Acc lex_nat_pair (meas g av sp))
           (cr : closure_result),
      sllc' g cm av sp a = cr
      -> match cr with
         | inl e => 
           spClosureStep g av sp = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : spClosureStep g av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc' g cm av' sp'
                                   (acc_after_step _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ (spClosureStep g av sp = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (av'  : NtSet.t)
                     (hs   : spClosureStep g av sp = CstepK av' sps')
                     (crs  : list closure_result),
               crs = dmap sps' (fun sp' hi => 
                                  sllc' g cm av' sp'
                                        (acc_after_step _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inr sps
           end.
  Proof.
    intros g cm av sp a cr hs; subst.
    rewrite sllc'_unfold.
    eapply sllc'_cases'; eauto.
  Qed.

  Lemma sllc'_success_cases :
    forall g cm av sp a sps,
      sllc' g cm av sp a = inr sps
      -> simReturn cm sp = Some sps
         \/ (spClosureStep g av sp = CstepDone /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (av'  : NtSet.t)
                   (hs   : spClosureStep g av sp = CstepK av' sps')
                   (crs  : list closure_result),
             crs = dmap sps' (fun sp' hi => 
                                sllc' g cm av' sp'
                                      (acc_after_step _ _ _ _ hs hi a))
             /\ aggrClosureResults crs = inr sps.
  Proof.
    intros g cm av sp a sps hs; apply sllc'_cases with (cr := inr sps); auto.
  Qed.

  Lemma sllc'_error_cases :
    forall g cm sp av a e,
      sllc' g cm av sp a = inl e
      -> spClosureStep g av sp = CstepError e
         \/ exists (sps : list subparser)
                   (av' : NtSet.t)
                   (hs  : spClosureStep g av sp = CstepK av' sps)
                   (crs : list closure_result),
          crs = dmap sps (fun sp' hi => 
                            sllc' g cm av' sp' (acc_after_step _ _ _ _ hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros g cm sp av a e hs; apply sllc'_cases with (cr := inl e); auto.
  Qed.

    Lemma sllc'_preserves_prediction' :
    forall g cm pair (a : Acc lex_nat_pair pair) av sp sp' sps' a',
      pair = meas g av sp
      -> sllc' g cm av sp a' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros g cm pair a.
    induction a as [pair hlt IH]; intros av sp sp' sps' a' heq hs hi; subst.
    apply sllc'_success_cases in hs.
    destruct hs as [hs | [[hs heq] | [sps'' [av' [hs [crs [heq heq']]]]]]]; subst.
    - eapply simReturn_preserves_prediction; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - (* lemma *)
      eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      + apply spClosureStep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply spClosureStep_meas_lt; eauto.
  Qed.

  Lemma sllc'_preserves_prediction :
    forall g cm av sp sp' sps' (a : Acc lex_nat_pair (meas g av sp)),
      sllc' g cm av sp a = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply sllc'_preserves_prediction'; eauto.
  Qed.
  
  Definition sllClosure (g : grammar) (cm : closure_map) (sps : list subparser) :
    sum prediction_error (list subparser) :=
    aggrClosureResults (map (fun sp => sllc' g cm (allNts g) sp (lex_nat_pair_wf _)) sps).

  Lemma sllClosure_preserves_prediction :
    forall g cm sps sp' sps',
      sllClosure g cm sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp' = prediction sp.
  Proof.
    intros g cm sps sp' sps' hc hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    apply in_map_iff in hi'; destruct hi' as [sp [hspc hi''']].
    eexists; split; eauto.
    eapply sllc'_preserves_prediction; eauto.
  Qed.

  (* SLL prediction *)

  Definition cache_key := (list subparser * terminal)%type.

  Lemma cache_key_eq_dec : 
    forall k k' : cache_key,
      {k = k'} + {k <> k'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Defined.

  Module MDT_CacheKey.
    Definition t := cache_key.
    Definition eq_dec := cache_key_eq_dec.
  End MDT_CacheKey.
  Module CacheKey_as_DT := Make_UDT(MDT_CacheKey).
  Module Cache := FMapWeakList.Make CacheKey_as_DT.
  Module CacheFacts := WFacts_fun CacheKey_as_DT Cache.

  (* A cache is a finite map with (list subparser * terminal) keys 
     and (list subparser) values *)
  Definition cache : Type := Cache.t (list subparser).

  Definition empty_cache : cache := Cache.empty (list subparser).
  
  Definition sllTarget g cm (sps : list subparser) (a : terminal) : sum prediction_error (list subparser) :=
    match move a sps with
    | inl e    => inl e
    | inr sps' =>
      match sllClosure g cm sps' with
      | inl e => inl e
      | inr sps'' => inr sps''
      end
    end.

  Lemma sllTarget_preserves_prediction :
    forall g cm sps a sp' sps',
      sllTarget g cm sps a = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp = prediction sp'.
  Proof.
    intros g cm sps a sp' sps'' hs hi.
    unfold sllTarget in hs.
    destruct (move _ _)         as [? | sps' ] eqn:hm; tc.
    destruct (sllClosure _ _ _) as [? | ?    ] eqn:hc; tc; inv hs.
    eapply sllClosure_preserves_prediction in hc; eauto.
    destruct hc as [sp'' [hi'' heq]]; rewrite heq.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [? [? ?]]; eauto.
  Qed.

  Definition cache_stores_target_results g cm ca :=
    forall sps a sps',
      Cache.find (sps, a) ca = Some sps'
      -> sllTarget g cm sps a = inr sps'.
  
  Lemma sllTarget_add_preserves_cache_invar :
    forall gr cm ca sps a sps',
      cache_stores_target_results gr cm ca
      -> sllTarget gr cm sps a = inr sps'
      -> cache_stores_target_results gr cm (Cache.add (sps, a) sps' ca).
  Proof.
    intros gr cm ca sps a sps' hc ht ka kb v hf.
    destruct (cache_key_eq_dec (ka, kb) (sps, a)) as [he | hn].
    - inv he; rewrite CacheFacts.add_eq_o in hf; inv hf; auto.
    - rewrite CacheFacts.add_neq_o in hf; auto.
  Qed.
  
  Fixpoint sllPredict' (gr  : grammar)
                       (cm  : closure_map)
                       (sps : list subparser)
                       (ts  : list token)
                       (ca  : cache) : prediction_result * cache :=
    match sps with 
    | []         => (PredReject, ca)
    | sp :: sps' =>
      if allPredictionsEqual sp sps' then
        (PredSucc sp.(prediction), ca)
      else
        match ts with
        | []            => (handleFinalSubparsers sps, ca)
        | (a, l) :: ts' =>
          match Cache.find (sps, a) ca with 
          | Some sps' => sllPredict' gr cm sps' ts' ca
          | None      =>
            match sllTarget gr cm sps a with
            | inl e    => (PredError e, ca)
            | inr sps' =>
              let ca' := Cache.add (sps, a) sps' ca
              in  sllPredict' gr cm sps' ts' ca'
            end
          end
        end
    end.

  Lemma sllPredict'_succ_preserves_cache_invar :
    forall gr cm ts sps ca ys ca',
      cache_stores_target_results gr cm ca
      -> sllPredict' gr cm sps ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr cm ca'.
  Proof.
    intros gr cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca ys ca' hc hs; sis.
    - dms; tc; inv hs; auto.
    - dm; tc; dm; try solve [inv hs; auto]; dm; eauto.
      dmeq ht; tc. apply IH in hs; auto.
      apply sllTarget_add_preserves_cache_invar; auto.
  Qed.

  Lemma sllPredict'_success_result_in_original_subparsers :
    forall g cm ts ca ca' ys sps,
      cache_stores_target_results g cm ca
      -> sllPredict' g cm sps ts ca = (PredSucc ys, ca')
      -> exists sp, In sp sps /\ sp.(prediction) = ys.
  Proof.
    intros g cm ts. 
    induction ts as [| (a,l) ts IH]; intros ca ca' ys sps hc hp; sis.
    - destruct sps as [| sp sps']; tc; dmeq hall.
      + inv hp; exists sp; split; auto.
        apply in_eq.
      + injection hp; intros _ hh. 
        apply handleFinalSubparsers_succ_facts in hh.
        destruct hh as (sp' & _ & hi & heq & _); eauto. 
    - destruct sps as [| sp sps'] eqn:hs; tc; dmeq hall.
      + inv hp; exists sp; split; auto.
        apply in_eq.
      + dmeq hf; tc.
        * apply IH in hp; auto; destruct hp as [sp' [hi heq]]; subst.
          apply hc in hf; auto.
          eapply sllTarget_preserves_prediction; eauto.
        * dmeq ht; tc.
          apply IH in hp.
          -- destruct hp as [sp' [hi ?]]; subst.
             eapply sllTarget_preserves_prediction; eauto.
          -- (* lemma *)
            red.
            intros ss t ss' hfind.
            destruct (cache_key_eq_dec (ss, t) (sp :: sps', a)).
            ++ inv e.
               rewrite CacheFacts.add_eq_o in hfind; auto.
               inv hfind; auto.
            ++ rewrite CacheFacts.add_neq_o in hfind; auto.
  Qed.
  
  Definition sllInitSps (g : grammar) (x : nonterminal) : list subparser :=
    map (fun rhs => Sp rhs (SF (Some x) rhs, []))
        (rhssForNt g x).

  Lemma sllInitSps_prediction_in_rhssForNt :
    forall g x sp,
      In sp (sllInitSps g x)
      -> In sp.(prediction) (rhssForNt g x).
  Proof.
    intros g x sp hi; unfold sllInitSps in hi.
    apply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  Definition sllStartState (g : grammar) (cm : closure_map)
             (x : nonterminal) : sum prediction_error (list subparser) :=
    sllClosure g cm (sllInitSps g x).

  Lemma sllStartState_sp_prediction_in_rhssForNt :
    forall g cm x sp' sps',
      sllStartState g cm x = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhssForNt g x).
  Proof.
    intros g cm x sp' sps' hs hi.
    unfold sllStartState in hs.
    eapply sllClosure_preserves_prediction in hs; eauto.
    destruct hs as [sp [hi' heq]]; rewrite heq.
    apply sllInitSps_prediction_in_rhssForNt; auto.
  Qed.

  Definition sllPredict (g : grammar) (cm : closure_map) (x : nonterminal)
             (ts : list token) (c : cache) : prediction_result * cache :=
    match sllStartState g cm x with
    | inl msg => (PredError msg, c)
    | inr sps => sllPredict' g cm sps ts c
    end.

  Lemma sllPredict_succ_in_rhssForNt :
    forall g cm x ts ca ca' ys,
      cache_stores_target_results g cm ca
      -> sllPredict g cm x ts ca = (PredSucc ys, ca')
      -> In ys (rhssForNt g x).
  Proof.
    intros g cm x ts ca ca' ys hc hs; unfold sllPredict in hs.
    dmeq hs'; tc.
    eapply sllPredict'_success_result_in_original_subparsers in hs; eauto.
    destruct hs as [sp [hi heq]]; subst.
    eapply sllStartState_sp_prediction_in_rhssForNt; eauto.
  Qed.

  Lemma sllPredict_succ_preserves_cache_invar :
    forall gr cm x ts ca ys ca',
      cache_stores_target_results gr cm ca
      -> sllPredict gr cm x ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr cm ca'.
  Proof.
    intros gr cm x ts ca ys ca' hc hs.
    unfold sllPredict in hs; dms; tc.
    eapply sllPredict'_succ_preserves_cache_invar; eauto.
  Qed.
      
  Definition adaptivePredict g cm x stk ts c : prediction_result * cache :=
    let sll_res := sllPredict g cm x ts c in
    match sll_res with
    | (PredAmbig _, _) => (llPredict g x stk ts, c)
    | _ => sll_res
    end.
  
  Lemma adaptivePredict_succ_in_rhssForNt :
    forall g cm x ss ts ca ca' ys,
      cache_stores_target_results g cm ca
      -> adaptivePredict g cm x ss ts ca = (PredSucc ys, ca')
      -> In ys (rhssForNt g x).
  Proof.
    intros g cm x ss ts ca ca' ys hc ha.
    unfold adaptivePredict in ha; dmeqs h; tc; inv ha.
    - eapply sllPredict_succ_in_rhssForNt; eauto.
    - eapply llPredict_succ_in_rhssForNt; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_in_grammar :
    forall g cm x ss ts ca ca' ys,
      cache_stores_target_results g cm ca
      -> adaptivePredict g cm x ss ts ca = (PredSucc ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g cm x ss ts ca ca' ys hc ha.
    apply rhssForNt_in_iff.
    eapply adaptivePredict_succ_in_rhssForNt; eauto.
  Qed.

  Lemma adaptivePredict_ambig_in_grammar :
    forall g cm x ss ts ca ca' ys,
      cache_stores_target_results g cm ca
      -> adaptivePredict g cm x ss ts ca = (PredAmbig ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g cm x ss ts ca ca' ys hc ha.
    unfold adaptivePredict in ha; dms; tc; inv ha.
    eapply llPredict_ambig_in_grammar; eauto.
  Qed.

  Lemma adaptivePredict_succ_preserves_cache_invar :
    forall gr cm x ss ts ca ys ca',
      cache_stores_target_results gr cm ca
      -> adaptivePredict gr cm x ss ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr cm ca'.
  Proof.
    intros gr cm x ss ts ca ys ca' hc ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
    eapply sllPredict_succ_preserves_cache_invar; eauto.
  Qed.

  Lemma adaptivePredict_ambig_preserves_cache_invar :
    forall gr cm x ss ts ca ys ca',
      cache_stores_target_results gr cm ca
      -> adaptivePredict gr cm x ss ts ca = (PredAmbig ys, ca')
      -> cache_stores_target_results gr cm ca'.
    intros gr cm x ss ts ca ys ca' hc ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
  Qed.
  
  (* Equivalence of LL and SLL *)
  
  Lemma sll'_ll'_equiv_succ :
    forall g cm sps sps' ts c c' ys,
      sllPredict' g cm sps ts c = (PredSucc ys, c')
      -> llPredict' g sps' ts = PredReject
         \/llPredict' g sps' ts = PredSucc ys.
  Proof.
    intros g cm sps sps' ts c c' ys hs.
    unfold sllPredict' in hs.
    induction ts as [| t ts IH].
    - destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual sp sps) eqn:ha.
      + (* SLL all equal *)
        inv hs.
        destruct sps' as [| sp' sps']; auto.
        right. simpl.
        (* an invariant relating the LL and SLL subaparsers
           should prove that SLL all equal -> LL all equal *)
  Abort.

  (*
Lemma sll_ll_equiv_succ :
  forall g cm fr frs x suf ts c c' ys,
    no_left_recursion g
    -> suffix_stack_wf g (fr, frs)
    -> fr = SF (NT x :: suf)
    -> SLL.sllPredict g cm x ts c = (PredSucc ys, c')
    -> llPredict g x (fr, frs) ts = PredSucc ys.
Proof.
  intros g cm fr frs x suf ts c c' ys hn hw ? hs; subst.
  unfold SLL.sllPredict in hs.
  destruct (SLL.startState g cm x) as [e | sps] eqn:hss; tc.
  unfold llPredict.
  destruct (startState g x _) as [e | sps'] eqn:hss'.
  - (* lemma *)
    destruct e as [ | x'].
    + exfalso; eapply startState_never_returns_SpInvalidState; eauto.
    + exfalso; eapply closure_never_finds_left_recursion; eauto.
  - (* what do we know at this point?
         - sllPredict' succeeded, so there must be an sp in sps with label ys
         - there must also be an sp' in sps' with label ys *)
    admit.
Abort.

Lemma adaptivePredict_equiv_llPredict :
  forall g cm x stk ts c c' r,
    SLL.adaptivePredict g cm x stk ts c = (r, c')
    -> llPredict g x stk ts = r.
Proof.
  intros g cm x stk ts c c' r ha.
  unfold SLL.adaptivePredict in ha.
  destruct (SLL.sllPredict _ _ _ _ _) as (r', c'') eqn:hs.
  destruct r' as [ys | ys | | e]; inv ha; auto.
  - (* PredSucc *)
    admit.
  - admit.
  - admit.
Admitted.
*)
End SllPredictionFn.

(* Equivalence of LL and SLL *)
(*
Lemma sll'_ll'_equiv_succ :
  forall g cm sps sps' ts c c' ys,
    
sllPredict' g cm sps ts c = (PredSucc ys, c')
    -> llPredict' g sps' ts = PredReject
       \/llPredict' g sps' ts = PredSucc ys.
Proof.
  intros g cm sps sps' ts c c' ys hs.
  unfold SLL.sllPredict' in hs.
  induction ts as [| t ts IH].
  - destruct sps as [| sp sps]; tc.
    destruct (SLL.allPredictionsEqual sp sps) eqn:ha.
    + (* SLL all equal *)
      destruct sps' as [| sp' sps']; auto.
      right.
Abort.

Lemma sll_ll_equiv_succ :
  forall g cm fr frs x suf ts c c' ys,
    no_left_recursion g
    -> suffix_stack_wf g (fr, frs)
    -> fr = SF (NT x :: suf)
    -> SLL.sllPredict g cm x ts c = (PredSucc ys, c')
    -> llPredict g x (fr, frs) ts = PredSucc ys.
Proof.
  intros g cm fr frs x suf ts c c' ys hn hw ? hs; subst.
  unfold SLL.sllPredict in hs.
  destruct (SLL.startState g cm x) as [e | sps] eqn:hss; tc.
  unfold llPredict.
  destruct (startState g x _) as [e | sps'] eqn:hss'.
  - (* lemma *)
    destruct e as [ | x'].
    + exfalso; eapply startState_never_returns_SpInvalidState; eauto.
    + exfalso; eapply closure_never_finds_left_recursion; eauto.
  - (* what do we know at this point?
         - sllPredict' succeeded, so there must be an sp in sps with label ys
         - there must also be an sp' in sps' with label ys *)
    admit.
Abort.

Lemma adaptivePredict_equiv_llPredict :
  forall g cm x stk ts c c' r,
    SLL.adaptivePredict g cm x stk ts c = (r, c')
    -> llPredict g x stk ts = r.
Proof.
  intros g cm x stk ts c c' r ha.
  unfold SLL.adaptivePredict in ha.
  destruct (SLL.sllPredict _ _ _ _ _) as (r', c'') eqn:hs.
  destruct r' as [ys | ys | | e]; inv ha; auto.
  - (* PredSucc *)
    admit.
  - admit.
  - admit.
Admitted.

*)  
