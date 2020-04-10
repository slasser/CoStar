Require Import List MSets Relation_Operators.
Require Import GallStar.LLPrediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionCompleteFn D.

  Definition edge := (suffix_frame * suffix_frame)%type.

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

  Lemma subset_subset_diffs :
    forall a b c : ES.t,
      ES.Subset a b
      -> ES.Subset (ES.diff c b) (ES.diff c a).
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

  Definition bin (e : edge) (es : list edge) : bool :=
    if in_dec edge_eq_dec e es then true else false.

  Lemma bin_in_iff :
    forall e es,
      bin e es = true <-> In e es.
  Proof.
    intros e es; split; intros hi; unfold bin in *; destruct (in_dec _ _ _); tc.
  Qed.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

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

  Fixpoint dsts (es : list edge) (s : suffix_frame) : list suffix_frame :=
    match es with
    | []             => []
    | (s', d) :: es' =>
      if suffix_frame_eq_dec s' s then d :: dsts es' s else dsts es' s
    end.

  Definition newEdges'' (e : edge) (es' : list edge) : list edge :=
    let (a, b) := e in
    let cs     := filter (fun c => negb (bin (a, c) es')) (dsts es' b)
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

  (* idea : use this for closure_step / closure_multistep *)
  Lemma clos_t_rt :
    forall (A : Type) (R : relation A) (x y z : A),
      clos_trans A R x y
      -> clos_refl_trans A R y z
      -> clos_trans A R x z.
  Proof.
    intros A R x y z ht hr.
    induction hr; eauto.
    eapply t_trans; eauto.
    apply t_step; auto.
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

  Fixpoint allFrames'' x ys : list suffix_frame :=
    match ys with
    | []       => SF (Some x) [] :: []
    | y :: ys' => SF (Some x) ys :: allFrames'' x ys'
    end.

  Definition allFrames' (g : grammar) : list suffix_frame :=
    flat_map (fun p => allFrames'' (lhs p) (rhs p)) g.

  Definition allFrames (g : grammar) : list suffix_frame :=
    SF None [] :: allFrames' g.

  Definition allEdges (g : grammar) : list edge :=
    let frs := allFrames g
    in  flat_map (fun fr => oneToMany fr frs) frs.

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

  Definition m (g : grammar) (es : list edge) : nat :=
    ES.cardinal (ES.diff (setOf (allEdges g)) (setOf es)).

  Axiom magic : forall A, A.

  (* idea : use the old measure, which doesn't need to refer to g *)
  Program Fixpoint transClosure (g  : grammar)
                                (es : list edge)
                                (pf : forall e, In e es -> In e (allEdges g))
          { measure (m g es) } : list edge :=
    let es' := newEdges es in
    match es' as es'' return es' = es'' -> _ with
    | []         => fun _   => es
    | e' :: es'' => fun heq => transClosure g (es' ++ es) _
    end eq_refl.
  Next Obligation.
    apply in_app_or in H.
    destruct H as [hp | hs]; eauto.
    
    - admit.
    - eauto.
    
    rewrite heq; simpl.
    unfold m.
    apply EP.MP.subset_cardinal_lt with (x := e').
    - apply subset_subset_diffs.
      apply setOf_subset_app with (es := e' :: _).
    - pose proof heq as hn.
      eapply in_new_edges__not_in_old_cons in hn; eauto.
      assert (ES.In e' (setOf (allEdges g))) by admit.
      ED.fsetdec.
    - intros hi; eapply ES.diff_spec in hi; destruct hi as [? hi].
      eapply hi; simpl; ED.fsetdec.
  Admitted.

  Lemma nullablePass_neq_candidates_lt :
    forall ps nu,
      ~ NtSet.Equal nu (nullablePass ps nu)
      -> countNullCands ps (nullablePass ps nu) < countNullCands ps nu.
  Proof.
    intros ps nu Hneq.
    apply nullablePass_neq_exists in Hneq.
    firstorder.
    apply NtSetEqProps.MP.subset_cardinal_lt with (x := x); try ND.fsetdec.
    apply subset_subset_diffs.
    apply nullablePass_subset.
  Defined.
  
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
