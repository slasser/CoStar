Require Import FMaps List MSets Program.Wf.
Require Import GallStar.Lex.
Require Import GallStar.Prediction_complete.
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

  Definition callSites (cm : closure_map) (fr : suffix_frame) : list suffix_frame :=
    match FM.find fr cm with
    | Some s => FS.elements s
    | None   => []
    end.

  (* Now for the parts that correspond to the LL prediction module *)

  (* "SLL closure" operation *)

  Definition sllClosureStep (g  : grammar)
                           (cm : closure_map)
                           (av : NtSet.t)
                           (sp : subparser) : subparser_closure_step_result :=
    match sp with
    | Sp pred (fr, frs) =>
      match fr with
      | SF o [] =>
        match frs with
        | [] =>
          (* SLL-specific part -- simulate a return to all call sites *)
          match o with
          | None   => CstepDone [sp] (* maybe this is an error? *)
          | Some x =>
            let sps' := map (fun fr' => Sp pred (fr', [])) (callSites cm fr)
            in  CstepDone sps'
          end
        | SF _ [] :: _                       => CstepError SpInvalidState
        | SF _ (T _ :: _) :: _               => CstepError SpInvalidState
        | SF o_cr (NT x :: suf_cr) :: frs_tl =>
          let stk':= (SF o_cr suf_cr, frs_tl) 
          in  CstepK (NtSet.add x av) [Sp pred stk'] 
        end
      | SF _ (T _ :: _)    => CstepDone [sp]
      | SF _ (NT x :: suf) =>
        if NtSet.mem x av then
          let sps' := map (fun rhs => Sp pred 
                                         (SF (Some x) rhs, fr :: frs))
                          (rhssForNt g x)
          in  CstepK (NtSet.remove x av) sps' 
        else if NtSet.mem x (allNts g) then
               CstepError (SpLeftRecursion x)
             else
               CstepK NtSet.empty [] 
      end
    end.

  Lemma sll_cstep_done_eq_or_map_lookup :
    forall g cm av sp pr fr frs sps,
      sp = Sp pr (fr, frs)
      -> sllClosureStep g cm av sp = CstepDone sps
      -> sps = [sp] \/ sps = map (fun fr' => Sp pr (fr', [])) (callSites cm fr).
  Proof.
    intros g cm av sp pr fr frs sps ? hs; subst.
    unfold sllClosureStep in hs; dms; tc; inv hs; auto.
  Qed.
  
  Lemma CstepK_sll_equiv_ll :
    forall (g      : grammar)
           (cm     : closure_map)
           (sp sp' : subparser)
           (sps'   : list subparser)
           (av av' : NtSet.t),
      sllClosureStep g cm av sp = CstepK av' sps'
      -> spClosureStep g av sp = CstepK av' sps'.
  Proof.
    intros g cm sp sp' sps' av av' hs; unfold sllClosureStep in hs; dms; tc.
  Defined.

  Lemma acc_after_sll_step :
    forall g cm sp sp' sps' av av',
      sllClosureStep g cm av sp = CstepK av' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (meas g av sp)
      -> Acc lex_nat_pair (meas g av' sp').
  Proof.
    intros g cm sp sp' sps' av av' heq hi ha.
    eapply Acc_inv; eauto.
    eapply spClosureStep_meas_lt; eauto.
    eapply CstepK_sll_equiv_ll; eauto.
  Defined.

  Definition closure_result := sum prediction_error (list subparser).

  Fixpoint sllSpClosure (g  : grammar)
                        (cm : closure_map)
                        (av : NtSet.t)
                        (sp : subparser)
                        (a  : Acc lex_nat_pair (meas g av sp))
                        : closure_result :=
    match sllClosureStep g cm av sp as r return sllClosureStep g cm av sp = r -> _ with
    | CstepDone sps'  => fun _  => inr sps'
    | CstepError e    => fun _  => inl e
    | CstepK av' sps' => 
      fun hs => 
        let crs :=
            dmap sps' (fun sp' hin =>
                         sllSpClosure g cm av' sp'
                                      (acc_after_sll_step _ _ _ _ _ _ _ hs hin a))
        in  aggrClosureResults crs
    end eq_refl.

  Lemma sllSpClosure_unfold :
    forall g cm av sp a,
      sllSpClosure g cm av sp a =
      match sllClosureStep g cm av sp as r return sllClosureStep g cm av sp = r -> _ with
      | CstepDone sps'  => fun _  => inr sps'
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hin =>
                           sllSpClosure g cm av' sp' (acc_after_sll_step _ _ _ _ _ _ _ hs hin a))
          in  aggrClosureResults crs
      end eq_refl.
  Proof.
    intros g cm av sp a; destruct a; auto. 
  Qed.
  
  Lemma sllSpClosure_cases' :
    forall (g   : grammar)
           (cm  : closure_map)
           (sp  : subparser)
           (av  : NtSet.t)
           (a   : Acc lex_nat_pair (meas g av sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result)
           (heq : sllClosureStep g cm av sp = sr),
      match sr as r return sllClosureStep g cm av sp = r -> closure_result with
      | CstepDone sps'  => fun _  => inr sps'
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hin => sllSpClosure g cm av' sp'
                                                            (acc_after_sll_step _ _ _ _ _ _ _ hs hin a))
          in  aggrClosureResults crs
      end heq = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : sllClosureStep g cm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllSpClosure g cm av' sp'
                                              (acc_after_sll_step _ _ _ _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           match sp with
           | Sp pred (fr, frs) =>
             (sr = CstepDone sps
              /\ (sps = [sp] \/ sps = map (fun fr' => Sp pred (fr', [])) (callSites cm fr)))
             \/ exists (sps' : list subparser)
                       (av'  : NtSet.t)
                       (hs   : sllClosureStep g cm av sp = CstepK av' sps')
                       (crs  : list closure_result),
                 crs = dmap sps' (fun sp' hi => 
                                    sllSpClosure g cm av' sp'
                                                 (acc_after_sll_step _ _ _ _ _ _ _ hs hi a))
                 /\ aggrClosureResults crs = inr sps
           end
         end.
  Proof.
    intros g cm [pr (fr, frs)] av a sr cr heq.
    destruct sr as [| sps | e];
      destruct cr as [e' | sps']; intros heq'; tc;
        try solve [inv heq'; eauto | eauto 8].
    eapply sll_cstep_done_eq_or_map_lookup in heq; inv heq'; eauto.
  Qed.
  
  Lemma sllSpClosure_cases :
    forall (g  : grammar)
           (cm : closure_map)
           (sp : subparser)
           (av : NtSet.t)
           (a  : Acc lex_nat_pair (meas g av sp))
           (cr : closure_result),
      sllSpClosure g cm av sp a = cr
      -> match cr with
         | inl e => 
           sllClosureStep g cm av sp = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : sllClosureStep g cm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllSpClosure g cm av' sp'
                                   (acc_after_sll_step _ _ _ _ _ _ _ hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           match sp with
           | Sp pred (fr, frs) =>
             (sllClosureStep g cm av sp = CstepDone sps
              /\ (sps = [sp]
                  \/ sps = map (fun fr' => Sp pred (fr', [])) (callSites cm fr)))
             \/ exists (sps' : list subparser)
                       (av'  : NtSet.t)
                       (hs   : sllClosureStep g cm av sp = CstepK av' sps')
                       (crs  : list closure_result),
                 crs = dmap sps' (fun sp' hi => 
                                    sllSpClosure g cm av' sp'
                                      (acc_after_sll_step _ _ _ _ _ _ _ hs hi a))
                 /\ aggrClosureResults crs = inr sps
           end
         end.
  Proof.
    intros g cm av sp a cr hs; subst.
    rewrite sllSpClosure_unfold.
    eapply sllSpClosure_cases'; eauto.
  Qed.

  (*
  Lemma spClosure_success_cases :
    forall g sp av a sps,
      spClosure g av sp a = inr sps
      -> (spClosureStep g av sp = CstepDone sps /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (av'  : NtSet.t)
                   (hs   : spClosureStep g av sp = CstepK av' sps')
                   (crs  : list closure_result),
          crs = dmap sps' (fun sp' hi => 
                             spClosure g av' sp' (acc_after_step _ _ _ _ hs hi a))
          /\ aggrClosureResults crs = inr sps.
  Proof.
    intros g sp av a sps hs; apply spClosure_cases with (cr := inr sps); auto.
  Qed.

  Lemma spClosure_error_cases :
    forall g sp av a e,
      spClosure g av sp a = inl e
      -> spClosureStep g av sp = CstepError e
         \/ exists (sps : list subparser)
                   (av' : NtSet.t)
                   (hs  : spClosureStep g av sp = CstepK av' sps)
                   (crs : list closure_result),
          crs = dmap sps (fun sp' hi => 
                            spClosure g av' sp' (acc_after_step _ _ _ _ hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros g sp av a e hs; apply spClosure_cases with (cr := inl e); auto.
  Qed.
   *)
  
  Definition sllClosure (g : grammar) (cm : closure_map) (sps : list subparser) :
    sum prediction_error (list subparser) :=
    aggrClosureResults (map (fun sp => sllSpClosure g cm (allNts g) sp (lex_nat_pair_wf _)) sps).

  Lemma sllClosure_preserves_prediction :
    forall g cm sps sp' sps',
      sllClosure g cm sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp' = prediction sp.
  Proof.
  Admitted.

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

  Definition target (sps : list subparser) (a : terminal) : sum prediction_error (list subparser) :=
    match move 

  (* To do: maybe only PredSucc and PredAmbig should carry an updated cache *)
  Fixpoint sllPredict' (g : grammar) (cm : closure_map) (sps : list subparser) (ts : list token) (c : cache) : prediction_result * cache :=
    match sps with 
    | []         => (PredReject, c)
    | sp :: sps' =>
      if allPredictionsEqual sp sps' then
        (PredSucc sp.(prediction), c)
      else
        match ts with
        | []            => (handleFinalSubparsers sps, c)
        | (a, l) :: ts' =>
          match Cache.find (sps, a) c with 
          | Some sps' => sllPredict' g cm sps' ts' c
          | None      => 
            match move (a, l) sps with
            | inl msg => (PredError msg, c)
            | inr mv  =>
              match sllClosure g cm mv with
              | inl msg => (PredError msg, c)
              | inr cl  =>
                let c' := Cache.add (sps, a) cl c
                in  sllPredict' g cm cl ts' c'
              end
            end
          end
        end
    end.

  Lemma sllPredict'_success_result_in_original_subparsers :
    forall g cm ts ca ca' ys sps,
      sllPredict' g cm sps ts ca = (PredSucc ys, ca')
      -> exists sp, In sp sps /\ sp.(prediction) = ys.
  Proof.
    intros g cm ts. 
    induction ts as [| (a,l) ts IH]; intros ca ca' ys sps hp; sis.
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
        * (* need an invariant about the cache here *)
          apply IH in hp; destruct hp as [sp' [hi heq]]; subst.
          admit.
        * destruct (move _ _) as [m | sps''] eqn:hm; tc.
          destruct (sllClosure _ _ _) as [m | sps'''] eqn:hc; tc.
          apply IH in hp; destruct hp as [? [? ?]]; subst.
          eapply sllClosure_preserves_prediction in hc; eauto.
          destruct hc as [sp'' [hi'' heq]]; rewrite heq.
          eapply move_preserves_prediction in hm; eauto.
          destruct hm as [? [? ?]]; eauto.
  Admitted.
  
  Definition sllInitSps (g : grammar) (x : nonterminal) : list subparser :=
    map (fun rhs => Sp rhs (SF (Some x) rhs, []))
        (rhssForNt g x).

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
  Admitted.

  Definition sllPredict (g : grammar) (cm : closure_map) (x : nonterminal)
             (ts : list token) (c : cache) : prediction_result * cache :=
    match sllStartState g cm x with
    | inl msg => (PredError msg, c)
    | inr sps => sllPredict' g cm sps ts c
    end.

  Lemma sllPredict_succ_in_rhssForNt :
    forall g cm x ts ca ca' ys,
      sllPredict g cm x ts ca = (PredSucc ys, ca')
      -> In ys (rhssForNt g x).
  Proof.
    intros g cm x ts ca ca' ys hs; unfold sllPredict in hs.
    dmeq hs'; tc.
    eapply sllPredict'_success_result_in_original_subparsers in hs.
    destruct hs as [sp [hi heq]]; subst.
    eapply sllStartState_sp_prediction_in_rhssForNt; eauto.
  Qed.
      
  Definition adaptivePredict g cm x stk ts c : prediction_result * cache :=
    let sll_res := sllPredict g cm x ts c in
    match sll_res with
    | (PredAmbig _, _) => (llPredict g x stk ts, c)
    | _ => sll_res
    end.
  
  Lemma adaptivePredict_succ_in_rhssForNt :
    forall g cm x ss ts ca ca' ys,
      adaptivePredict g cm x ss ts ca = (PredSucc ys, ca')
      -> In ys (rhssForNt g x).
  Proof.
    intros g cm x ss ts ca ca' ys ha.
    unfold adaptivePredict in ha; dmeqs h; tc; inv ha.
    - eapply sllPredict_succ_in_rhssForNt; eauto.
    - eapply llPredict_succ_in_rhssForNt; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_in_grammar :
    forall g cm x ss ts ca ca' ys,
      adaptivePredict g cm x ss ts ca = (PredSucc ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g cm x ss ts ca ca' ys ha.
    apply rhssForNt_in_iff.
    eapply adaptivePredict_succ_in_rhssForNt; eauto.
  Qed.

  Lemma adaptivePredict_ambig_in_grammar :
    forall g cm x ss ts ca ca' ys,
      adaptivePredict g cm x ss ts ca = (PredAmbig ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g cm x ss ts ca ca' ys ha.
    unfold adaptivePredict in ha; dms; tc; inv ha.
    eapply llPredict_ambig_in_grammar; eauto.
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
