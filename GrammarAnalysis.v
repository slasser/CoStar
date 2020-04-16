Require Import List MSets Relation_Operators Wf_nat.
Require Import GallStar.LLPrediction_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionCompleteFn D.

  Definition edge := (suffix_frame * suffix_frame)%type.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

(*
  X --> [a,Y]
  Y --> [Z,c]
  Z --> [   ]

 *)
  (* Correctness spec *)
  (* to do : need an initial push case,
     and a corresponding function for computing those edges *)
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
      forall x y pre suf rhs,
        In (x, pre ++ NT y :: suf) g
        -> In (y, rhs) g
        -> frame_step g (SF (Some x) (NT y :: suf))
                        (SF (Some y) rhs).

  Hint Constructors frame_step : core.

  Definition step_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_step g x y.

  Definition step_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_step g x y -> In (x, y) es.

  

  Definition frame_multistep (g : grammar) :
    suffix_frame -> suffix_frame -> Prop :=
    clos_trans _ (frame_step g).

  Hint Constructors clos_trans : core.

  Definition mstep_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_multistep g x y.

  Definition mstep_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_multistep g x y -> In (x, y) es.

  Definition mstep_edges_correct (g : grammar) (es : list edge) :=
    mstep_edges_sound g es /\ mstep_edges_complete g es.

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

  Lemma pushEdges'_sound :
    forall g s d x suf pre,
      In (x, pre ++ suf) g
      -> In (s, d) (pushEdges' g x suf)
      -> frame_step g s d.
  Proof.
    intros g s d x suf. 
    induction suf as [| [a|y] suf IH]; sis; intros pre hi' hi; rew_anr.
    - inv hi.
    - apply IH with (pre := pre ++ [T a]); apps.
    - apply in_app_or in hi; destruct hi as [hi | hi].
      + apply in_map_iff in hi; destruct hi as [rhs [heq hi]].
        inv heq; apply rhssForNt_in_iff in hi; eauto.
      + apply IH with (pre := pre ++ [NT y]); apps.
  Qed.

  Lemma pushEdges'_complete :
    forall g x y rhs pre suf rhs',
      rhs = pre ++ NT y :: suf
      -> In (y, rhs') g
      -> In (SF (Some x) (NT y :: suf), SF (Some y) rhs')
            (pushEdges' g x rhs).
  Proof.
    intros g x y rhs; induction rhs as [| [a | y'] suf' IH]; intros pre suf rhs' heq hi; sis.
    - apply app_cons_not_nil in heq; inv heq.
    - destruct pre; sis; inv heq; eauto.
    - destruct pre; sis; inv heq; apply in_or_app; eauto.
      left; apply in_map_iff; eexists; split; eauto.
      apply rhssForNt_in_iff; auto.
  Qed.

  Definition pushEdges (g : grammar) : list edge :=
    flat_map (fun p => pushEdges' g (lhs p) (rhs p)) g.

  Lemma pushEdges_sound :
    forall g s d,
      In (s, d) (pushEdges g)
      -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    eapply pushEdges'_sound with (pre := []); eauto.
  Qed.

  Lemma pushEdges_complete :
    forall g x y pre suf rhs,
      In (x, pre ++ NT y :: suf) g
      -> In (y, rhs) g
      -> In (SF (Some x) (NT y :: suf), SF (Some y) rhs)
            (pushEdges g).
  Proof.
    intros g x y pre suf rhs hi hi'.
    apply in_flat_map; exists (x, pre ++ NT y :: suf); split; auto; sis.
    eapply pushEdges'_complete; eauto.
  Qed.
  
  Fixpoint returnEdges' (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with
    | []          => []
    | T _ :: ys'  => returnEdges' x ys'
    | NT y :: ys' =>
      (SF (Some y) [], SF (Some x) ys') :: returnEdges' x ys'
    end.

  Lemma returnEdges'_sound :
    forall g s d x suf pre,
      In (x, pre ++ suf) g
      -> In (s, d) (returnEdges' x suf)
      -> frame_step g s d.
  Proof.
    intros g s d x suf. 
    induction suf as [| [a|y] suf IH]; sis; intros pre hi' hi; rew_anr.
    - inv hi.
    - apply IH with (pre := pre ++ [T a]); apps.
    - destruct hi as [hh | ht].
      + inv hh; eauto.
      + apply IH with (pre := pre ++ [NT y]); apps.
  Qed.
  
  Lemma returnEdges'_complete :
    forall x y rhs pre suf,
      rhs = pre ++ NT y :: suf
      -> In (SF (Some y) [], SF (Some x) suf)
            (returnEdges' x rhs).
  Proof.
    intros x y rhs; induction rhs as [| [a | y'] suf' IH]; intros pre suf heq; sis.
    - apply app_cons_not_nil in heq; inv heq.
    - destruct pre; sis; inv heq; eauto.
    - destruct pre; sis; inv heq; eauto.
  Qed.

  Definition returnEdges (g : grammar) : list edge :=
    flat_map (fun p => returnEdges' (lhs p) (rhs p)) g.

  Lemma returnEdges_sound :
    forall g s d,
      In (s, d) (returnEdges g) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    eapply returnEdges'_sound with (pre := []); eauto.
  Qed.

  Lemma returnEdges_complete :
    forall g x y pre suf,
      In (x, pre ++ NT y :: suf) g
      -> In (SF (Some y) [], SF (Some x) suf) (returnEdges g).
  Proof.
    intros g x y pre suf hi.
    apply in_flat_map; eexists; split; eauto; sis.
    eapply returnEdges'_complete; eauto.
  Qed.

  Definition finalReturnEdges g : list edge :=
    map (fun x => (SF (Some x) [], SF None [])) (lhss g).

  Lemma finalReturnEdges_sound :
    forall g s d,
      In (s, d) (finalReturnEdges g) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_map_iff in hi. destruct hi as [x [heq hi]]; inv heq.
    apply lhss_exists_rhs in hi; destruct hi as [ys hi]; eauto.
  Qed.

  Lemma finalReturnEdges_complete :
    forall g x ys,
      In (x, ys) g
      -> In (SF (Some x) [], SF None []) (finalReturnEdges g).
  Proof.
    intros g x ys hi.
    apply in_map_iff; eexists; split; eauto.
    eapply production_lhs_in_lhss; eauto.
  Qed.
  
  Definition epsilonEdges g : list edge :=
    pushEdges g ++ returnEdges g ++ finalReturnEdges g.

  Lemma epsilonEdges__step_edges_sound :
    forall g,
      step_edges_sound g (epsilonEdges g).
  Proof.
    intros g s d hi; apply in_app_or in hi.
    destruct hi as [hp | hrf];
      [.. | apply in_app_or in hrf; destruct hrf as [hr | hf]].
    - apply pushEdges_sound        ; auto.
    - apply returnEdges_sound      ; auto.
    - apply finalReturnEdges_sound ; auto.
  Qed.

  Lemma epsilonEdges__step_edges_complete :
    forall g,
      step_edges_complete g (epsilonEdges g).
  Proof.
    intros g s d hs; unfold epsilonEdges; inv hs.
    - do 2 (apply in_or_app; right).
      eapply finalReturnEdges_complete; eauto.
    - apply in_or_app; right; apply in_or_app; left.
      eapply returnEdges_complete; eauto.
    - apply in_or_app; left.
      eapply pushEdges_complete; eauto.
  Qed.

  Lemma step_edges_sound__mstep_edges_sound :
    forall g es,
      step_edges_sound g es -> mstep_edges_sound g es.
  Proof.
    intros g es hs s d hi; apply t_step; auto.
  Qed.

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

  Lemma src_in_allSrcs :
    forall a b es,
      In (a, b) es -> In a (allSrcs es).
  Proof.
    intros a b es hi; apply in_map_iff; exists (a, b); split; auto.
  Qed.

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
    - eapply src_in_allSrcs; eauto. 
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
    apply allSrcs_allDsts_allPossibleEdges_in_iff in hi;
    destruct hi as [ha hb].
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

  Lemma dsts_allDsts :
    forall s d es,
      In d (dsts s es) -> In d (allDsts es).
  Proof.
    intros s d es hi; induction es as [| (s', d') es IH]; sis.
    - inv hi.
    - dmeq heq; subst; inv hi; auto.
  Qed.

  Lemma dsts_in_iff :
    forall a b es,
      In b (dsts a es) <-> In (a, b) es.
  Proof.
    intros a b es; split; intros hi; induction es as [| (a', b') es IH]; sis; try solve [inv hi].
    - dm; subst; inv hi; auto.
    - destruct hi as [hh | ht]; dms; tc; subst.
      + inv hh; apply in_eq.
      + apply in_cons; auto.
  Qed.

  Definition bin (e : edge) (es : list edge) : bool :=
    if in_dec edge_eq_dec e es then true else false.

  Lemma bin_true_in_iff :
    forall e es,
      bin e es = true <-> In e es.
  Proof.
    intros e es; split; intros hi; unfold bin in *;
    destruct (in_dec _ _ _); tc.
  Qed.
  
  Definition newEdges' (e : edge) (es' : list edge) : list edge :=
    let (a, b) := e in
    let cs     := filter (fun c => negb (bin (a, c) es')) (dsts b es')
    in  oneToMany a cs.

  Lemma in_new_edges__not_in_old' :
    forall e e'' es' es'',
      newEdges' e es' = es''
      -> In e'' es''
      -> ~ In e'' es'.
  Proof.
    intros (a,b) e'' es' es'' ? hi hi'; subst.
    unfold newEdges' in hi.
    apply in_map_iff in hi ; destruct hi as [c [? hi]]; subst.
    apply filter_In  in hi ; destruct hi as [hi hn].
    apply negb_true_iff in hn.
    eapply bin_true_in_iff in hi'; tc.
  Qed.

  Lemma newEdges'_src_eq :
    forall a a' b c es,
      In (a', c) (newEdges' (a, b) es)
      -> a' = a.
  Proof.
    intros a a' b c es hi.
    apply in_map_iff in hi; destruct hi as [? [heq ?]]; inv heq; auto.
  Qed.

  Lemma newEdges'_rew_src :
    forall a a' b c es,
      In (a', c) (newEdges' (a, b) es)
      -> In (a, c) (newEdges' (a, b) es).
  Proof.
    intros a a' b c es; intros hi.
    assert (heq : a' = a).
    { eapply newEdges'_src_eq; eauto. }
    subst; auto.
  Qed.

  Lemma newEdges'_dst_in_dsts :
    forall a a' b c es,
      In (a', c) (newEdges' (a, b) es)
      -> In c (dsts b es).
  Proof.
    intros a a' b c es hi.
    apply in_map_iff in hi; destruct hi as [? [heq hi]]; inv heq.
    apply filter_In in hi; destruct hi; auto.
  Qed.

  Lemma newEdges'_dst_in_allDsts :
    forall a a' b c es,
      In (a', c) (newEdges' (a, b) es)
      -> In c (allDsts es).
  Proof.
    intros a a' b c es hi.
    eapply dsts_allDsts; eapply newEdges'_dst_in_dsts; eauto.
  Qed.

  Lemma newEdges'_midpt_endpt :
    forall a a' b c es,
      In (a', c) (newEdges' (a, b) es)
      -> In (b, c) es.
  Proof.
    intros a a' b c es hi.
    apply dsts_in_iff.
    eapply newEdges'_dst_in_dsts; eauto.
  Qed.
    
  Lemma newEdges'_preserves_soundness :
    forall g s s' d d' es,
      mstep_edges_sound g es
      -> In (s, d) es
      -> In (s', d') (newEdges' (s, d) es)
      -> frame_multistep g s' d'.
  Proof.
    intros g s s' d d' es hs hi hi'.
    apply t_trans with (y := d); apply hs.
    - apply newEdges'_src_eq in hi'; subst; auto.
    - eapply newEdges'_midpt_endpt; eauto.
  Qed.

  Lemma newEdges'_nil_trans :
    forall es x y z,
      newEdges' (x, y) es = []
      -> In (y, z) es
      -> In (x, z) es.
  Proof.
    intros es x y z hn hi.
    apply map_eq_nil in hn.
    apply filter_nil__f_false with (x := z) in hn.
    - apply bin_true_in_iff; apply negb_false_iff; auto.
    - apply dsts_in_iff; auto.
  Qed.

  Definition newEdges (es : list edge) : list edge :=
    flat_map (fun e => newEdges' e es) es.

  Lemma newEdges_allSrcs :
    forall a b es,
      In (a, b) (newEdges es) -> In a (allSrcs es).
  Proof.
    intros a'' b'' es hi.
    apply in_flat_map in hi; destruct hi as [(a, b) [hi hi']].
    apply newEdges'_src_eq in hi'; subst.
    eapply src_in_allSrcs; eauto.
  Qed.

  Lemma newEdges_allDsts :
    forall a c es,
      In (a, c) (newEdges es) -> In c (allDsts es).
  Proof.
    intros a c es hi.
    apply in_flat_map in hi; destruct hi as [(a', b) [hi hi']].
    eapply newEdges'_dst_in_allDsts; eauto.
  Qed.

  Lemma in_new_edges__not_in_old :
    forall es es'' e'',
      newEdges es = es''
      -> In e'' es''
      -> ~ In e'' es.
  Proof.
    intros es es'' e'' hn hi hi''; subst.
    apply in_flat_map in hi; destruct hi as [(a', b) [hi hi']].
    eapply in_new_edges__not_in_old'; eauto.
  Qed.

  Lemma newEdges_allPossibleEdges :
    forall e es,
      In e (newEdges es) -> In e (allPossibleEdges es).
  Proof.
    intros (a, b) es hi.
    apply allSrcs_allDsts_allPossibleEdges_in_iff; split.
    - eapply newEdges_allSrcs; eauto.
    - eapply newEdges_allDsts; eauto. 
  Qed.
  
  Lemma newEdges_subset_allPossibleEdges :
    forall es es',
      newEdges es = es'
      -> ES.Subset (setOf es') (setOf (allPossibleEdges es)).
  Proof.
    intros es es' ? e hi; subst; apply setOf_in_iff; apply setOf_in_iff in hi.
    apply newEdges_allPossibleEdges; auto.
  Qed.
    
  Lemma newEdges_cons__not_in_old :
    forall es es' e',
      newEdges es = e' :: es'
      -> ~ ES.In e' (setOf es).
  Proof.
    intros es es' e' hn hi.
    apply setOf_in_iff in hi.
    eapply in_new_edges__not_in_old; eauto. 
    apply in_eq.
  Qed.

  Lemma newEdges_cons__allPossibleEdges :
    forall e' es es',
      newEdges es = e' :: es'
      -> ES.In e' (setOf (allPossibleEdges es)).
  Proof.
    intros e' es es' hn; apply setOf_in_iff.
    apply newEdges_allPossibleEdges; rewrite hn; apply in_eq.
  Qed.

  Definition m (es : list edge) : nat :=
    ES.cardinal (ES.diff (setOf (allPossibleEdges es)) (setOf es)).

  Lemma newEdges_cons_meas_lt :
    forall e' es es',
      newEdges es = e' :: es'
      -> m (e' :: es' ++ es) < m es.
  Proof.
    intros e' es es' hf; unfold m.
    apply EP.MP.subset_cardinal_lt with (x := e').
    - apply equal_subset__subset_diffs.
      + apply allPossibleEdges_subset__app_subset
          with (es' := e' :: es').
        apply newEdges_subset_allPossibleEdges; auto.
      + apply setOf_subset_app with (es := e' :: _).
    - assert (hn : ~ ES.In e' (setOf es)).
      { eapply newEdges_cons__not_in_old; eauto. }
      assert (hi : ES.In e' (setOf (allPossibleEdges es))).
      { eapply newEdges_cons__allPossibleEdges; eauto. }
      ED.fsetdec.
    - intros hi; eapply ES.diff_spec in hi; destruct hi as [? hi].
      eapply hi; simpl; ED.fsetdec.
  Defined.
  
  Lemma newEdges_cons_acc :
    forall e' es es',
      Acc lt (m es)
      -> newEdges es = e' :: es'
      -> Acc lt (m (e' :: es' ++ es)).
  Proof.
    intros e' es es' ha h.
    eapply Acc_inv; eauto.
    apply newEdges_cons_meas_lt; auto.
  Defined.

  Lemma newEdges_preserves_soundness :
    forall g es es',
      mstep_edges_sound g es
      -> newEdges es = es'
      -> mstep_edges_sound g (es' ++ es).
  Proof.
    intros g es es' hs hn s d hi; subst.
    apply in_app_or in hi; destruct hi as [hf | hb]; auto.
    apply in_flat_map in hf; destruct hf as [(s', d') [hi hi']].
    eapply newEdges'_preserves_soundness; eauto.
  Qed.
  
  Lemma newEdges_result_trans :
    forall es x y z,
      newEdges es = []
      -> In (x, y) es
      -> In (y, z) es
      -> In (x, z) es.
  Proof.
    intros es x y z hn hi hi'.
    apply flat_map_nil__f_nil with (x := (x, y)) in hn; auto.
    eapply newEdges'_nil_trans; eauto.
  Qed.
  
  Fixpoint transClosure (es : list edge) (ha : Acc lt (m es)) {struct ha} : list edge :=
    match newEdges es as n return newEdges es = n -> _ with
    | []        => fun _   => es
    | e' :: es' => fun heq => transClosure (e' :: es' ++ es)
                                           (newEdges_cons_acc _ _ _ ha heq)
    end eq_refl.

  Lemma transClosure_unfold :
    forall es ha,
      transClosure es ha =
      match newEdges es as n return newEdges es = n -> _ with
      | []        => fun _   => es
      | e' :: es' => fun heq => transClosure (e' :: es' ++ es)
                                             (newEdges_cons_acc _ _ _ ha heq)
      end eq_refl.
  Proof.
    intros es ha; destruct ha; auto.
  Qed.

  Lemma transClosure_cases' :
    forall es es'' ha n (heq : newEdges es = n),
      match n as n' return newEdges es = n' -> _ with
      | []        => fun _   => es
      | e' :: es' => fun heq => transClosure (e' :: es' ++ es)
                                             (newEdges_cons_acc _ _ _ ha heq)
      end heq = es''
      -> newEdges es = [] /\ es'' = es
         \/ (exists e' es' (heq : newEdges es = e' :: es'),
                transClosure (e' :: es' ++ es)
                             (newEdges_cons_acc _ _ _ ha heq) = es'').
  Proof.
    intros; dms; eauto.
  Qed.
  
  Lemma transClosure_cases :
    forall es es'' ha,
      transClosure es ha = es''
      -> newEdges es = [] /\ es'' = es
         \/ (exists e' es' (heq : newEdges es = e' :: es'),
                transClosure (e' :: es' ++ es)
                             (newEdges_cons_acc _ _ _ ha heq) = es'').
  Proof.
    intros es es'' ha ht; rewrite transClosure_unfold in ht.
    eapply transClosure_cases'; eauto.
  Qed.          

  (* Soundness of transitive closure algorithm *)
  
  Lemma transClosure_preserves_soundness' :
    forall g c (ha : Acc lt c) es es' ha',
      c = m es
      -> mstep_edges_sound g es
      -> transClosure es ha' = es'
      -> mstep_edges_sound g es'.
  Proof.
    intros g c ha'.
    induction ha' as [ha' hlt IH]; intros es es'' ha ? hs ht.
    apply transClosure_cases in ht.
    destruct ht as [[hn ?] | [e' [es' [heq' ht]]]]; subst; auto.
    eapply IH with (y := m (e' :: es' ++ es)); eauto.
    - apply newEdges_cons_meas_lt; auto.
    - eapply newEdges_preserves_soundness with (es' := e' :: es'); eauto.
  Qed.

  Lemma transClosure_preserves_soundness :
    forall g es ha,
      mstep_edges_sound g es
      -> mstep_edges_sound g (transClosure es ha).
  Proof.
    intros; eapply transClosure_preserves_soundness'; eauto.
  Qed.

  (* Completeness of transitive closure algorithm *)

  Lemma transClosure_retains_elements' :
    forall c (ha : Acc lt c) es es' ha' x y,
      c = m es
      -> In (x, y) es
      -> transClosure es ha' = es'
      -> In (x, y) es'.
  Proof.
    intros c ha; induction ha as  [ha' hlt IH]; intros es es'' ha x y ? hi ht.
    apply transClosure_cases in ht.
    destruct ht as [[hn ?] | [e' [es' [heq' ht]]]]; subst; auto.
    eapply IH  with (es := e' :: es' ++ es); eauto.
    + apply newEdges_cons_meas_lt; auto.
    + apply in_or_app with (l := e' :: es'); auto.
  Qed.

  Lemma transClosure_retains_elements :
    forall es ha x y,
      In (x, y) es
      -> In (x, y) (transClosure es ha).
  Proof.
    intros; eapply transClosure_retains_elements'; eauto.
  Qed.

  Lemma transClosure_preserves_step_edges_complete :
    forall g es ha,
      step_edges_complete g es
      -> step_edges_complete g (transClosure es ha).
  Proof.
    intros g es ha hc x y hs; apply transClosure_retains_elements; auto.
  Qed.

  Lemma transClosure_result_trans' :
    forall c (ha : Acc lt c) es es' ha' x y z,
      c = m es
      -> transClosure es ha' = es'
      -> In (x, y) es'
      -> In (y, z) es'
      -> In (x, z) es'.
  Proof.
    intros c ha'; induction ha' as [ha' hlt IH].
    intros es es'' ha x y z ? ht hi hi'.
    apply transClosure_cases in ht.
    destruct ht as [[hn ?] | [e' [es' [heq' ht]]]]; subst.
    - eapply newEdges_result_trans; eauto.
    - eapply IH; eauto.
      apply newEdges_cons_meas_lt; auto.
  Qed.

  Lemma transClosure_result_trans  :
    forall es ha x y z,
      In    (x, y) (transClosure es ha)
      -> In (y, z) (transClosure es ha)
      -> In (x, z) (transClosure es ha).
  Proof.
    intros; eapply transClosure_result_trans'; eauto.
  Qed.
  
  Lemma transClosure_complete :
    forall g es es' ha,
      step_edges_complete g es
      -> transClosure es ha = es'
      -> mstep_edges_complete g es'.
  Proof.
    intros g es es' ha hc ht x y hm; subst. induction hm.
    - eapply transClosure_preserves_step_edges_complete; eauto.
    - eapply transClosure_result_trans; eauto.
  Qed.

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

  (*
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
   *)
  
  Definition dstStable (e : edge) : bool :=
    let (_, b) := e in stable b.

  Definition stableEdges (es : list edge) : list edge :=
    filter dstStable es.

  Definition mkGraphEdges (g : grammar) : list edge :=
    stableEdges (transClosure (epsilonEdges g) (lt_wf _)).

  Lemma mkGraphEdges_sound :
    forall g s d,
      In (s, d) (mkGraphEdges g)
      -> frame_multistep g s d /\ stable d = true.
  Proof.
    intros g s d hi; unfold mkGraphEdges in hi.
    apply filter_In in hi; destruct hi as [hi hs]; split.
    - eapply transClosure_preserves_soundness; eauto.
      apply step_edges_sound__mstep_edges_sound.
      apply epsilonEdges__step_edges_sound.
    - unfold dstStable in hs; auto.
  Qed.

  Lemma mkGraphEdges_complete :
    forall g s d,
      frame_multistep g s d
      -> stable d = true
      -> In (s, d) (mkGraphEdges g).
  Proof.
    intros g s d hm hs; unfold mkGraphEdges.
    apply filter_In; split.
    - eapply transClosure_complete; eauto.
      apply epsilonEdges__step_edges_complete.
    - unfold dstStable; auto.
  Qed.
  
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

  Lemma fromEdges_sound :
    forall es s d ds,
      FM.MapsTo s ds (fromEdges es)
      -> In d ds
      -> In (s, d) es.
  Proof.
    intros es; induction es as [| (s', d') es IH]; intros s d ds hm hi.
    - eapply FMF.empty_mapsto_iff; eauto.
    - simpl in hm; dmeq hf.
      + (* value already exists for key *)
        apply FMF.add_mapsto_iff in hm.
        destruct hm as [[heq heq'] | [hneq hm]]; subst.
        * destruct hi as [hh | ht]; subst.
          -- apply in_eq.
          -- apply FMF.find_mapsto_iff in hf.
             eapply IH in hf; eauto.
             apply in_cons; auto.
        * eapply IH in hm; eauto.
          apply in_cons; auto.
      + apply FMF.add_mapsto_iff in hm.
        destruct hm as [[heq heq'] | [hneq hm]]; subst.
        * apply in_singleton_eq in hi; subst.
          apply in_eq.
        * eapply IH in hm; eauto.
          apply in_cons; auto.
  Qed.

  Lemma fromEdges_complete :
    forall es s d,
      In (s, d) es
      -> (exists ds,
             FM.MapsTo s ds (fromEdges es)
             /\ In d ds).
  Proof.
    intros es; induction es as [| (s', d') es IH]; intros s d hi.
    - inv hi. 
    - destruct hi as [hh | ht]; sis.
      + inv hh.
        destruct (FM.find _ _) as [ds' |] eqn:hf.
        * (* value already exists for key *)
          exists (d :: ds'); split.
          -- apply FMF.add_mapsto_iff; auto.
          -- apply in_eq.
        * exists [d]; split.
          -- apply FMF.add_mapsto_iff; auto.
          -- apply in_eq.
      + destruct (FM.find _ _) as [ds' |] eqn:hf.
        * destruct (FMF.eq_dec s' s); subst.
          -- exists (d' :: ds'); split.
             ++ apply FMF.add_mapsto_iff; auto.
             ++ apply IH in ht.
                destruct ht as [ds [hm hi]].
                apply FMF.find_mapsto_iff in hf.
                eapply FMF.MapsTo_fun in hm; eauto; subst.
                apply in_cons; auto.
          -- apply IH in ht.
             destruct ht as [ds [hm hi]].
             exists ds; split; auto.
             apply FMF.add_mapsto_iff; auto.
        * destruct (FMF.eq_dec s' s); subst.
          -- exfalso.
             apply IH in ht.
             destruct ht as [ds [hm hi]].
             apply FMF.find_mapsto_iff in hm; tc.
          -- apply IH in ht.
             destruct ht as [ds [hm hi]].
             exists ds; split; auto.
             apply FMF.add_mapsto_iff; auto.
  Qed.

  Definition mkClosureMap (g : grammar) : closure_map :=
    fromEdges (mkGraphEdges g).
  
   Definition destFrames (fr : suffix_frame) (cm : closure_map) : list suffix_frame :=
    match FM.find fr cm with
    | Some frs => frs
    | None     => []
    end.

  (* Correctness of grammar static analysis *)

  Lemma closure_step__frame_step :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> suffix_stack_wf g (fr, frs)
      -> closure_step g av sp av' sp'
      -> frame_step g fr fr'.
  Proof.
    intros g av av' ? ? pr pr' fr fr' frs frs' ? ? hw hc; subst; inv hc; eauto.
    - inv_suffix_frames_wf hw   hi  hw'  ; rew_anr.
      inv_suffix_frames_wf hw'  hi' hw'' ; eauto.
    - admit. 
  Admitted.

  Lemma closure_multistep__frame_step_trc' :
    forall g av av' sp sp',
      suffix_stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> (forall pr pr' fr fr' frs frs',
             sp     = Sp pr  (fr, frs)
             -> sp' = Sp pr' (fr', frs')
             -> clos_refl_trans_1n _ (frame_step g) fr fr').
  Proof.
    intros g av av' sp sp' hw hc. 
    induct_cm hc hs hc' IH; intros pr pr' fr fr' ? ? heq heq'; subst; sis.
    - inv heq; inv heq'; apply rt1n_refl.
    - inv heq; inv heq'; apply rt1n_refl.
    - pose proof hs as hs'.
      inv hs'.
      + (* return case *)
        eapply closure_step__frame_step in hs; eauto.
        inv hs.
        * (* final return case *)
          inv hw; rew_anr.
          inv H7.
          eapply rt1n_trans.
          -- sis; eapply Fstep_final_ret; eauto.
          -- eapply IH; eauto. sis; auto. 
        * (* nonfinal return case *)
          eapply rt1n_trans.
          -- sis; eapply Fstep_nonfinal_ret; eauto.
          -- eapply IH; eauto; sis.
             eapply return_preserves_suffix_frames_wf_invar; eauto.
      + (* push case *)
        eapply closure_step__frame_step in hs; eauto.
        inv hs.
        eapply rt1n_trans.
        * sis; eapply Fstep_push; eauto.
        * eapply IH; eauto; sis.
          apply push_preserves_suffix_frames_wf_invar; eauto.
  Qed.

  Lemma closure_multistep__frame_step_trc :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> suffix_stack_wf g (stack sp)
      -> closure_multistep g av sp av' sp'
      -> clos_refl_trans_1n _ (frame_step g) fr fr'.
  Proof.
    intros; eapply closure_multistep__frame_step_trc'; eauto.
  Qed.

  Definition closure_map_sound g cm :=
    forall fr fr' frs',
      FM.MapsTo fr frs' cm
      -> In fr' frs'
      -> (frame_multistep g fr fr' /\ stable fr' = true).

  Definition closure_map_complete g cm :=
    forall fr fr',
      frame_multistep g fr fr'
      -> stable fr' = true
      -> exists frs',
          FM.MapsTo fr frs' cm
          /\ In fr' frs'.

  Definition closure_map_correct g cm :=
    closure_map_sound g cm /\ closure_map_complete g cm.

  Lemma mkClosureMap_sound :
    forall g,
      closure_map_sound g (mkClosureMap g).
  Proof.
    intros g s d ds hm hi; unfold mkClosureMap in hm.
    eapply fromEdges_sound in hm; eauto.
    apply mkGraphEdges_sound; auto.
  Qed.

  Lemma mkClosureMap_complete :
    forall g,
      closure_map_complete g (mkClosureMap g).
  Proof.
    intros g s d hf hs; unfold mkClosureMap.
    apply fromEdges_complete.
    apply mkGraphEdges_complete; auto.
  Qed.
    
  Theorem mkClosureMap_result_correct :
    forall g,
      closure_map_correct g (mkClosureMap g).
  Proof.
    intros g; split.
    - apply mkClosureMap_sound.
    - apply mkClosureMap_complete.
  Qed.
  
End GrammarAnalysisFn.
