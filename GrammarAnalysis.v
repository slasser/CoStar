Require Import List MSets Relation_Operators.
Require Import GallStar.LLPrediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionCompleteFn D.

  Definition edge := (suffix_frame * suffix_frame)%type.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

  (* COMPUTATION OF SINGLE-STEP FRAME CLOSURE EDGES *)
  
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

  Definition finalReturnEdges g : list edge :=
    map (fun x => (SF (Some x) [], SF None [])) (lhss g).

  Definition epsilonEdges g : list edge :=
    pushEdges g ++ returnEdges g ++ finalReturnEdges g.
  

  (* FINITE SETS OF EDGES -- USED IN TRANSITIVE CLOSURE TERMINATION PROOF *)
  
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
  Module ES           := EdgeSet.
  Module EF           := WFactsOn Edge_as_DT EdgeSet.
  Module EP           := EqProperties EdgeSet.
  Module ED           := WDecideOn Edge_as_DT EdgeSet.

  (* Some generic finite set facts *)

  Lemma subset_subset_diffs :
    forall a b c : ES.t,
      ES.Subset a b
      -> ES.Subset (ES.diff c b) (ES.diff c a).
  Proof.
    ED.fsetdec.
  Defined.

  Lemma equal_subset__subset_diffs :
    forall u u' a b : ES.t,
      ES.Subset u u'
      -> ES.Subset a b
      -> ES.Subset (ES.diff u b) (ES.diff u' a).
  Proof.
    ED.fsetdec.
  Defined.

  Definition setOf (es : list edge) : ES.t :=
    fold_right ES.add ES.empty es.

  Lemma setOf_subset_app :
    forall es es',
      ES.Subset (setOf es') (setOf (es ++ es')).
  Proof.
    intros es es'; induction es as [| e es IH]; sis; ED.fsetdec.
  Qed.

  Lemma setOf_in_iff :
    forall e es,
      ES.In e (setOf es) <-> In e es.
  Proof.
    intros e es; split; intros hi;
      induction es as [| e' es IH]; sis; try ED.fsetdec.
    - apply ES.add_spec in hi; destruct hi as [hh | ht]; eauto.
    - destruct hi as [hh | ht]; subst.
      + ED.fsetdec.
      + apply IH in ht; ED.fsetdec.
  Qed.

  (* DEFINITIONS RELATED TO TRANSITIVE CLOSURE TERMINATION *)

  Definition allSrcs es : list suffix_frame := map src es.
  Definition allDsts es : list suffix_frame := map dst es.

  Definition allPossibleEdges es : list edge := 
    let ss := allSrcs es in
    let ds := allDsts es in
    flat_map (fun s => oneToMany s ds) ss.

  Lemma allPossibleEdges_src_in_allSrcs :
    forall a b es,
      In (a, b) (allPossibleEdges es)
      -> In a (allSrcs es).
  Proof.
    intros a b es hi.
    apply in_flat_map in hi; destruct hi as [a' [hi hi']].
    apply oneToMany_src_eq in hi'; subst; auto.
  Qed.

  Lemma allPossibleEdges_dst_in_allDsts :
    forall a b es,
      In (a, b) (allPossibleEdges es)
      -> In b (allDsts es).
  Proof.
    intros a b es hi.
    apply in_flat_map in hi; destruct hi as [a' [hi hi']].
    eapply oneToMany_dst_in; eauto.
  Qed.

  Definition list_subset {X} (xs xs' : list X) :=
    forall x, In x xs -> In x xs'.

  Lemma subset__list_subset :
    forall xs ys,
      ES.Subset (setOf xs) (setOf ys)
      -> list_subset xs ys.
  Proof.
    intros xs ys hs x hi.
    apply setOf_in_iff; apply hs; apply setOf_in_iff; auto.
  Qed.

  Lemma subset_allSrcs_app__allSrcs :
    forall es es' a,
      list_subset es' (allPossibleEdges es)
      -> In a (allSrcs (es' ++ es))
      -> In a (allSrcs         es).
  Proof.
    intros es es' a hs hi.
    apply in_map_iff in hi; destruct hi as [(a', b') [heq hi]]; sis; subst.
    apply in_app_or in hi; destruct hi as [hes' | hes]; auto.
    - apply hs in hes'; eapply allPossibleEdges_src_in_allSrcs; eauto.
    - apply in_map_iff; exists (a, b'); auto.
  Qed.

  Lemma subset_allDsts_app__allDsts :
    forall es es' b,
      list_subset es' (allPossibleEdges es)
      -> In b (allDsts (es' ++ es))
      -> In b (allDsts         es).
  Proof.
    intros es es' b hs hi.
    apply in_map_iff in hi; destruct hi as [(a', b') [heq hi]]; sis; subst.
    apply in_app_or in hi; destruct hi as [hes' | hes]; auto.
    - apply hs in hes'; eapply allPossibleEdges_dst_in_allDsts; eauto.
    - apply in_map_iff; exists (a', b); auto.
  Qed.

  Lemma allSrcs_allDsts_allPossibleEdges_in_iff :
    forall a b es,
      (In a (allSrcs es) /\ In b (allDsts es))
      <-> In (a, b) (allPossibleEdges es).
  Proof. 
    intros a b es; split; [intros [hs hd] | intros hi].
    - apply in_flat_map; eexists; split; eauto.
      apply in_map_iff; eauto.
    - apply in_flat_map in hi; destruct hi as [a' [hi hi']]; split.
      + apply oneToMany_src_eq in hi'; subst; auto.
      + apply oneToMany_dst_in in hi'; auto.
  Qed.
  
  Lemma allPossibleEdges_subset__app_subset :
    forall es es',
      ES.Subset (setOf es') (setOf (allPossibleEdges es))
      -> ES.Subset (setOf (allPossibleEdges (es' ++ es)))
                   (setOf (allPossibleEdges         es)).
  Proof.
    intros es es' hs (a, b) hi; apply subset__list_subset in hs;
    apply setOf_in_iff; apply setOf_in_iff in hi.
    apply allSrcs_allDsts_allPossibleEdges_in_iff in hi; destruct hi as [ha hb].
    apply allSrcs_allDsts_allPossibleEdges_in_iff; split.
    - eapply subset_allSrcs_app__allSrcs; eauto.
    - eapply subset_allDsts_app__allDsts; eauto.
  Qed.

  (* TRANSITIVE CLOSURE OF A SET OF EDGES *)

  Fixpoint dsts (s : suffix_frame) (es : list edge) : list suffix_frame :=
    match es with
    | []             => []
    | (s', d) :: es' =>
      if suffix_frame_eq_dec s' s then d :: dsts s es' else dsts s es'
    end.

  Definition bin (e : edge) (es : list edge) : bool :=
    if in_dec edge_eq_dec e es then true else false.

  Lemma bin_in_iff :
    forall e es,
      bin e es = true <-> In e es.
  Proof.
    intros e es; split; intros hi; unfold bin in *; destruct (in_dec _ _ _); tc.
  Qed.

  Definition newEdges'' (e : edge) (es' : list edge) : list edge :=
    let (a, b) := e in
    let cs     := filter (fun c => negb (bin (a, c) es')) (dsts b es')
    in  oneToMany a cs.

  Lemma in_new_edges__not_in_old'' :
    forall e e'' es' es'',
      newEdges'' e es' = es''
      -> In e'' es''
      -> ~ In e'' es'.
  Proof.
    intros (a,b) e'' es' es'' ? hi hi'; subst.
    unfold newEdges'' in hi.
    apply in_map_iff in hi ; destruct hi as [c [? hi]]; subst.
    apply filter_In  in hi ; destruct hi as [hi hn].
    apply negb_true_iff in hn.
    eapply bin_in_iff in hi'; tc.
  Qed.

  Definition newEdges' (es es' : list edge) : list edge :=
    flat_map (fun e => newEdges'' e es') es.

  Lemma in_new_edges__not_in_old' :
    forall es es' es'' e'',
      newEdges' es es' = es''
      -> In e'' es''
      -> ~ In e'' es'.
  Proof.
    intros es; induction es as [| e es IH];
      intros es' es'' e'' hn hi hi'; sis; subst.
    - inv hi.
    - apply in_app_or in hi; destruct hi as [hp | hs].
      + eapply in_new_edges__not_in_old''; eauto. 
      + eapply IH; eauto.
  Qed.
  
  Definition newEdges (es : list edge) : list edge :=
    newEdges' es es.

  Lemma in_new_edges__not_in_old :
    forall es es' e',
      newEdges es = es'
      -> In e' es'
      -> ~ ES.In e' (setOf es).
  Proof.
    intros es es' e' hn hi hi'; unfold newEdges in hn.
    eapply in_new_edges__not_in_old'; eauto.
    apply setOf_in_iff; auto.
  Qed.

  Lemma in_new_edges__not_in_old_cons :
    forall es es' e',
      newEdges es = e' :: es'
      -> ~ ES.In e' (setOf es).
  Proof.
    intros es es' e' hn hi.
    eapply in_new_edges__not_in_old; eauto.
    apply in_eq.
  Qed.

  Definition m (es : list edge) : nat :=
    ES.cardinal (ES.diff (setOf (allPossibleEdges es)) (setOf es)).

  Program Fixpoint transClosure (g  : grammar)
                                (es : list edge)
                                { measure (m es) } : list edge :=
    let es' := newEdges es in
    match es' as es'' return es' = es'' -> _ with
    | []        => fun _   => es
    | e' :: es' => fun heq => transClosure g (e' :: es' ++ es)
    end eq_refl.
  Next Obligation.
    unfold m.
    apply EP.MP.subset_cardinal_lt with (x := e').
    - apply equal_subset__subset_diffs.
      + apply allPossibleEdges_subset__app_subset
              with (es' := e' :: es').
        admit.
      + apply setOf_subset_app with (es := e' :: _).
    - pose proof heq as hn; eapply in_new_edges__not_in_old_cons in hn; eauto.
      assert (ES.In e' (setOf (allPossibleEdges es))) by admit.
      ED.fsetdec.
    - intros hi; eapply ES.diff_spec in hi; destruct hi as [? hi].
      eapply hi; simpl; ED.fsetdec.
  Admitted.

  Definition stable (fr : suffix_frame) : bool :=
    match fr with
    | SF None []             => true
    | SF (Some x) (T _ :: _) => true
    | _                      => false
    end.

  Lemma stable_config__stable_true :
    forall fr frs,
      stable_config (fr, frs)
      -> stable fr = true.
  Proof.
    intros fr frs hs; inv hs; auto. 
  Qed.

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
  
  Definition dstStable (e : edge) : bool :=
    let (_, b) := e in stable b.

  Definition stableEdges (es : list edge) : list edge :=
    filter dstStable es.

  (* Maybe we don't need the refl edges *)
  Definition mkGraphEdges (g : grammar) : list edge :=
    stableEdges (transClosure (epsilonEdges g)) ++ (reflEdges g).

  (* A closure graph is a map where each key K is a suffix frame 
     (i.e., grammar location), and each value V is a list of frames 
     that are epsilon-reachable from K *)
  (* Maybe the value should be a set *)
  Definition closure_map := FM.t (list suffix_frame).

  Definition addEdge (e : edge) (m : closure_map) : closure_map :=
    let (k, v) := e in
    match FM.find k m with
    | Some vs => FM.add k (v :: vs) m
    | None    => FM.add k [v] m
    end.

  Definition fromEdges (es : list edge) : closure_map :=
    fold_right addEdge (FM.empty (list suffix_frame)) es.

  Definition mkClosureMap (g : grammar) : closure_map :=
    fromEdges (mkGraphEdges g).

  Definition destFrames (cm : closure_map) (fr : suffix_frame) : list suffix_frame :=
    match FM.find fr cm with
    | Some frs => frs
    | None     => []
    end.

  (* Correctness of grammar static analysis *)

  Inductive frame_step (g : grammar) :
    suffix_frame -> suffix_frame -> Prop :=
  | Fstep_final_ret :
      forall x ys,
        In (x, ys) g
        -> frame_step g (SF (Some x) [])
                        (SF  None    [])
  | Fstep_nonfinal_ret :
      forall x y pre suf,
        In (x, pre ++ NT y :: suf) g
        -> frame_step g (SF (Some y) [])
                        (SF (Some x) suf)
  | Fstep_push :
      forall o x ys suf,
        In (x, ys) g
        -> frame_step g (SF o (NT x :: suf))
                        (SF (Some x) ys).

  Hint Constructors frame_step : core.

  Lemma closure_step__frame_step :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> suffix_stack_wf g (fr, frs)
      -> closure_step g av sp av' sp'
      -> frame_step g fr fr'.
  Proof.
    intros g av av' ? ? pr pr' fr fr' frs frs' ? ? hw hc; subst; inv hc; eauto.
    inv_suffix_frames_wf hw   hi  hw'  ; rew_anr.
    inv_suffix_frames_wf hw'  hi' hw'' ; eauto.
  Qed.

  Definition frame_multistep (g : grammar) :
    suffix_frame -> suffix_frame -> Prop :=
    clos_refl_trans _ (frame_step g).

  Hint Constructors clos_refl_trans : core.

  Lemma closure_multistep__frame_multistep' :
    forall g av av' sp sp',
      suffix_stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> (forall pr pr' fr fr' frs frs',
             sp     = Sp pr  (fr, frs)
             -> sp' = Sp pr' (fr', frs')
             -> frame_multistep g fr fr').
  Proof.
    intros g av av' sp sp' hw hc. 
    induct_cm hc hs hc' IH; intros pr pr' fr fr' ? ? heq heq'; subst; sis.
    - inv heq; inv heq'; apply rt_refl.
    - inv heq; inv heq'; apply rt_refl.
    - pose proof hs as hs'.
      inv hs'.
      + (* return case *)
        eapply closure_step__frame_step in hs; eauto.
        inv hs.
        * (* final return case *)
          inv hw; rew_anr.
          inv H7.
          eapply rt_trans.
          -- sis. eapply rt_step. eapply Fstep_final_ret; eauto.
          -- eapply IH; eauto. sis; auto. 
        * (* nonfinal return case *)
          eapply rt_trans.
          -- sis. eapply rt_step. eapply Fstep_nonfinal_ret; eauto.
          -- eapply IH; eauto; sis. eapply return_preserves_suffix_frames_wf_invar; eauto.
      + (* push case *)
        eapply closure_step__frame_step in hs; eauto.
        inv hs.
        eapply rt_trans.
        * sis. eapply rt_step. eapply Fstep_push; eauto.
        * eapply IH; eauto; sis.
          apply push_preserves_suffix_frames_wf_invar; eauto.
  Qed.

  Lemma closure_multistep__frame_multistep :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> suffix_stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> frame_multistep g fr fr'.
  Proof.
    intros; eapply closure_multistep__frame_multistep'; eauto.
  Qed.

  (* Correctness spec for the mkClosureMap function *)
  Definition closure_map_complete g cm :=
    forall fr fr',
      frame_multistep g fr fr'
      -> stable fr' = true
      -> exists frs', FM.MapsTo fr frs' cm
                      /\ In fr' frs'.
  
  Theorem mkClosureMap_result_complete :
    forall g,
      closure_map_complete g (mkClosureMap g).
  Admitted.
  
End GrammarAnalysisFn.
