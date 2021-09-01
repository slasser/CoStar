Require Import List MSets Relation_Operators Wf_nat.
Require Import CoStar.Orders.
Require Import CoStar.LLPrediction.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.
Require Import FSets FSets.FMapAVL FSets.FMapFacts.
Require Import CoLoR.Util.FGraph.TransClos.

Module GrammarAnalysisFn (Import D : Defs.T).

  Module Export LLPC := LLPredictionFn D.
  
  (* The definition of "stability" for SLL stacks *)
  Inductive stable_config : suffix_stack -> Prop :=
  | SC_empty :
      stable_config (SF None [], [])
  | SC_terminal :
      forall o a suf frs,
        stable_config (SF o (T a :: suf), frs).

  Hint Constructors stable_config : core.
  
  Definition all_stable sps :=
    forall sp, In sp sps -> stable_config sp.(sll_stack).

  (* Graph in which nodes are suffix frames, and edges 
     connect "closure-reachable" frames *)

  Definition edge := (suffix_frame * suffix_frame)%type.

  Definition src (e : edge) : suffix_frame := fst e.
  Definition dst (e : edge) : suffix_frame := snd e.

  Inductive frame_step (g : grammar) :
    suffix_frame -> suffix_frame -> Prop :=
  | Fstep_final_ret :
      forall x ys,
        PM.In (x, ys) g
        -> frame_step g (SF (Some x) [])
                        (SF  None    [])
  | Fstep_nonfinal_ret :
      forall x y pre suf,
        PM.In (x, pre ++ NT y :: suf) g
        -> frame_step g (SF (Some y) [])
                        (SF (Some x) suf)
  | Fstep_initial_push :
      forall x rhs,
        PM.In (x, rhs) g
        -> frame_step g (SF None     [NT x])
                        (SF (Some x) rhs)
  | Fstep_noninitial_push :
      forall x y pre suf rhs,
        PM.In (x, pre ++ NT y :: suf) g
        -> PM.In (y, rhs) g
        -> frame_step g (SF (Some x) (NT y :: suf))
                        (SF (Some y) rhs).

  Hint Constructors frame_step : core.

  (* Correspondence between closure_multistep and frame_step relations *)

  (*
  Lemma closure_step__frame_step :
    forall g av av' sp sp' pr pr' fr fr' frs frs',
      sp     = Sp pr  (fr, frs)
      -> sp' = Sp pr' (fr', frs')
      -> suffix_stack_wf g (fr, frs)
      -> closure_step g av sp av' sp'
      -> frame_step g fr fr'.
  Proof.
    intros g av av' ? ? pr pr' fr fr' frs frs' ? ? hw hc; subst; inv hc; eauto.
    - inv_suffix_frames_wf hw   hi  hw'  ; eauto.
      inv_suffix_frames_wf hw'  hi' hw'' ; eauto.
    - inv_suffix_frames_wf hw   hi  hw'  ; eauto.
  Qed.

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
        eapply closure_step__frame_step in hs; eauto; sis.
        inv hs.
        * eapply rt1n_trans; eauto.
          eapply IH; eauto.
          apply push_preserves_suffix_frames_wf_invar; auto.
        * eapply rt1n_trans; eauto.
          eapply IH; eauto.
          apply push_preserves_suffix_frames_wf_invar; auto.
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

   *)
  
  (* COMPUTATION OF SINGLE-STEP FRAME CLOSURE EDGES *)

  Definition step_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_step g x y.

  Definition step_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_step g x y -> In (x, y) es.
  
  Definition frame_multistep (g : grammar) :
    suffix_frame -> suffix_frame -> Prop :=
    clos_trans (frame_step g).

  Hint Constructors clos_trans : core.

  Definition mstep_edges_sound (g : grammar) (es : list edge) :=
    forall x y, In (x, y) es -> frame_multistep g x y.

  Lemma step_edges_sound__mstep_edges_sound :
    forall g es,
      step_edges_sound g es -> mstep_edges_sound g es.
  Proof.
    intros g es hs s d hi; apply t_step; auto.
  Qed.

  Definition mstep_edges_complete (g : grammar) (es : list edge) :=
    forall x y, frame_multistep g x y -> In (x, y) es.

  Definition mstep_edges_correct (g : grammar) (es : list edge) :=
    mstep_edges_sound g es /\ mstep_edges_complete g es.

  Definition initialPushEdges' (ps : list production) (x : nonterminal) : list edge :=
    map (fun rhs => (SF None [NT x], SF (Some x) rhs))
        (rhssFor' ps x).

  Lemma initialPushEdges'_sound :
    forall g s d x,
      In (s, d) (initialPushEdges' (productions g) x)
      -> frame_step g s d.
  Proof.
    intros g s d x hi.
    apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; inv heq.
    eapply rhssFor'_in_iff in hi.
    apply in_productions_iff in hi; auto.
  Qed.

  Lemma initialPushEdges'_complete :
    forall g x rhs,
      PM.In (x, rhs) g
      -> In (SF None [NT x], SF (Some x) rhs)
            (initialPushEdges' (productions g) x).
  Proof.
    intros g x rhs hi.
    apply in_map_iff; eexists; split; eauto.
    apply rhssFor'_in_iff.
    apply in_productions_iff; auto.
  Qed.

  Definition initialPushEdges (ps : list production) : list edge :=
    flat_map (initialPushEdges' ps) (lhss' ps).

  Lemma initialPushEdges_sound :
    forall g s d,
      In (s, d) (initialPushEdges (productions g))
      -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [x [hi hi']].
    eapply initialPushEdges'_sound; eauto.
  Qed.

  Lemma initialPushEdges_complete :
    forall g x rhs,
      PM.In (x, rhs) g
      -> In (SF None [NT x], SF (Some x) rhs) (initialPushEdges (productions g)).
  Proof.
    intros g x rhs hi.
    apply in_flat_map; exists x; split.
    - apply in_productions_iff in hi.
      eapply production_lhs_in_lhss'; eauto.
    - eapply initialPushEdges'_complete; eauto.
  Qed.
  
  Fixpoint pushEdges' (ps : list production) (x : nonterminal) (ys : list symbol) : list edge :=
    match ys with 
    | []          => []
    | T _ :: ys'  => pushEdges' ps x ys'
    | NT y :: ys' =>
      let es := map (fun rhs => (SF (Some x) ys, SF (Some y) rhs))
                    (rhssFor' ps y)
      in  es ++ pushEdges' ps x ys'
    end.

  Lemma pushEdges'_sound :
    forall g s d x suf pre,
      PM.In (x, pre ++ suf) g
      -> In (s, d) (pushEdges' (productions g) x suf)
      -> frame_step g s d.
  Proof.
    intros g s d x suf. 
    induction suf as [| [a|y] suf IH]; sis; intros pre hi' hi; rew_anr.
    - inv hi.
    - apply IH with (pre := pre ++ [T a]); apps.
    - apply in_app_or in hi; destruct hi as [hi | hi].
      + apply in_map_iff in hi; destruct hi as [rhs [heq hi]].
        inv heq.
        apply rhssFor'_in_iff in hi.
        apply in_productions_iff in hi; eauto.
      + apply IH with (pre := pre ++ [NT y]); apps.
  Qed.

  Lemma pushEdges'_complete :
    forall g x y rhs pre suf rhs',
      rhs = pre ++ NT y :: suf
      -> PM.In (y, rhs') g
      -> In (SF (Some x) (NT y :: suf), SF (Some y) rhs')
            (pushEdges' (productions g) x rhs).
  Proof.
    intros g x y rhs; induction rhs as [| [a | y'] suf' IH]; intros pre suf rhs' heq hi; sis.
    - apply app_cons_not_nil in heq; inv heq.
    - destruct pre; sis; inv heq; eauto.
    - destruct pre; sis; inv heq; apply in_or_app; eauto.
      left; apply in_map_iff; eexists; split; eauto.
      apply rhssFor'_in_iff. 
      apply in_productions_iff; auto.
  Qed.

  Definition pushEdges (ps : list production) : list edge :=
    flat_map (fun p => pushEdges' ps (lhs' p) (rhs' p)) ps.

  Lemma pushEdges_sound :
    forall g s d,
      In (s, d) (pushEdges (productions g))
      -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    apply in_productions_iff in hi.
    eapply pushEdges'_sound with (pre := []); eauto.
  Qed.

  Lemma pushEdges_complete :
    forall g x y pre suf rhs,
      PM.In (x, pre ++ NT y :: suf) g
      -> PM.In (y, rhs) g
      -> In (SF (Some x) (NT y :: suf), SF (Some y) rhs)
            (pushEdges (productions g)).
  Proof.
    intros g x y pre suf rhs hi hi'.
    apply in_productions_iff in hi.
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
      PM.In (x, pre ++ suf) g
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

  Definition returnEdges (ps : list production) : list edge :=
    flat_map (fun p => returnEdges' (lhs' p) (rhs' p)) ps.

  Lemma returnEdges_sound :
    forall g s d,
      In (s, d) (returnEdges (productions g)) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_flat_map in hi; destruct hi as [(x, ys) [hi hi']]; sis.
    apply in_productions_iff in hi.
    eapply returnEdges'_sound with (pre := []); eauto.
  Qed.

  Lemma returnEdges_complete :
    forall g x y pre suf,
      PM.In (x, pre ++ NT y :: suf) g
      -> In (SF (Some y) [], SF (Some x) suf) (returnEdges (productions g)).
  Proof.
    intros g x y pre suf hi.
    apply in_productions_iff in hi.
    apply in_flat_map; eexists; split; eauto; sis.
    eapply returnEdges'_complete; eauto.
  Qed.

  Definition finalReturnEdges (ps : list production) : list edge :=
    map (fun x => (SF (Some x) [], SF None [])) (lhss' ps).

  Lemma finalReturnEdges_sound :
    forall g s d,
      In (s, d) (finalReturnEdges (productions g)) -> frame_step g s d.
  Proof.
    intros g s d hi.
    apply in_map_iff in hi.
    destruct hi as [x [heq hi]]; inv heq.
    apply in_lhss'_exists_rhs in hi.
    destruct hi as [ys hi].
    apply in_productions_iff in hi; eauto.
  Qed.

  Lemma finalReturnEdges_complete :
    forall g x ys,
      PM.In (x, ys) g
      -> In (SF (Some x) [], SF None []) (finalReturnEdges (productions g)).
  Proof.
    intros g x ys hi.
    apply in_map_iff; eexists; split; eauto.
    apply in_productions_iff in hi.
    eapply production_lhs_in_lhss'; eauto.
  Qed.
  
  Definition epsilonEdges (g : grammar) : list edge :=
    let ps := productions g
    in  initialPushEdges ps ++ pushEdges ps ++ returnEdges ps ++ finalReturnEdges ps.

  Lemma epsilonEdges__step_edges_sound :
    forall g,
      step_edges_sound g (epsilonEdges g).
  Proof.
    intros g s d hi; apply in_app_or in hi; destruct hi as [hi | hprf].
    - apply initialPushEdges_sound; auto. 
    - apply in_app_or in hprf; destruct hprf as [hp | hrf].
      + apply pushEdges_sound ; auto.
      + apply in_app_or in hrf; destruct hrf as [hr | hf].
        * apply returnEdges_sound      ; auto.
        * apply finalReturnEdges_sound ; auto.
  Qed.

  Lemma epsilonEdges__step_edges_complete :
    forall g,
      step_edges_complete g (epsilonEdges g).
  Proof.
    intros g s d hs; unfold epsilonEdges; inv hs.
    - do 3 (apply in_or_app; right).
      eapply finalReturnEdges_complete; eauto.
    - do 2 (apply in_or_app; right); apply in_or_app; left.
      eapply returnEdges_complete; eauto.
    - apply in_or_app; left.
      eapply initialPushEdges_complete; eauto.
    - apply in_or_app; right; apply in_or_app; left.
      eapply pushEdges_complete; eauto.
  Qed.

  (* transitive closure operation *)

  Definition liftEdge (e : edge) : option (suffix_frame * list suffix_frame) :=
    match e with
    | (s, d) => Some (s, [d])
    end.
  
  Definition transClos (es : list edge) : FM.t FS.t :=
    TC.trans_clos_list liftEdge es.

  (* soundness of transitive closure operation *)

  Definition tc_soundness_invar g cm :=
    forall s d, TC.G.rel cm s d -> frame_multistep g s d.

  Definition tc_soundness_invar_list g prs :=
    forall s d ds, In (s, ds) prs -> FS.In d ds -> frame_multistep g s d.

  Lemma tc_soundness_invar_list_tail :
    forall g s ds prs,
      tc_soundness_invar_list g ((s, ds) :: prs)
      -> tc_soundness_invar_list g prs.
  Proof.
    intros g s ds prs hs; red; red in hs; intros; eapply hs; eauto.
    apply in_cons; auto.
  Qed.

  Lemma in_elements_find_iff :
    forall s (ds : FS.t) cm,
      In (s, ds) (FM.elements cm)
      <-> FM.find s cm = Some ds.
  Proof.
    intros s ds cm; split; intros hi.
    - apply FMF.find_mapsto_iff.
      apply FMF.elements_mapsto_iff.
      apply In_InA; auto.
      (* lemma *)
      constructor.
      + repeat red; intros; auto.
      + repeat red; intros x y he; destruct he; auto.
      + repeat red. intros (a, b) (c, d) (e, f) he he'; sis.
        repeat red in he, he'; sis; destruct he; destruct he'; subst; auto.
    - apply FMF.find_mapsto_iff in hi.
      apply FM.elements_1 in hi.
      apply InA_alt in hi.
      destruct hi as [(s', ds') [he hi]].
      repeat red in he; sis; destruct he; subst; auto.
  Qed.

  Lemma invars_equiv :
    forall g cm,
      tc_soundness_invar g cm <-> tc_soundness_invar_list g (FM.elements cm).
  Proof.
    intros g cm; split; intros hs.
    - intros s d ds hi hi'.
      apply hs; eexists; split; eauto.
      apply in_elements_find_iff; auto.
    - intros s d hr.
      destruct hr as [ds [hf hi]].
      eapply hs; eauto.
      apply in_elements_find_iff; auto.
  Qed.
      
  Lemma add_edge_pres_soundness :
    forall g s d cm,
      frame_multistep g s d
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g (TC.G.add_edge s d cm).
  Proof.
    intros g s d cm hf hs.
    unfold TC.G.add_edge.
    red; intros s' d' hr; red in hr.
    destruct hr as [ds' [hfi hin]].
    destruct (SF_as_UOT.eq_dec s' s) as [he | hn]; subst.
    - rewrite FMF.add_eq_o in hfi; auto; inv hfi.
      destruct (SF_as_UOT.eq_dec d' d) as [he' | hn']; subst; auto.
      apply FS.add_3 in hin; auto.
      apply hs; apply TC.G.In_succs_rel; auto.
    - rewrite FMF.add_neq_o in hfi; auto.
      apply hs; red; eauto.
  Qed.

  Lemma fold_add_edge_preserves_soundness :
    forall g s ds cm,
      (forall d, In d ds -> frame_multistep g s d)
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g
                            (fold_left
                               (fun a e =>
                                  TC.G.add_edge s e a)
                               ds cm).
  Proof.
    intros g s ds; induction ds as [| d ds IH]; intros cm ha hs; sis; auto.
    apply IH; auto.
    apply add_edge_pres_soundness; auto.
  Qed.

  Lemma in_elements_iff_in_FS :
    forall fr s,
      In fr (FS.elements s) <-> FS.In fr s.
  Proof.
    intros fr s; split; intros hi.
    - eapply FSF.elements_iff.
      eapply In_InA; eauto.
    - eapply FSF.elements_iff in hi. 
      eapply InA_alt in hi; destruct hi as [fr' [heq hi]]; subst; auto.
  Qed.
  
  Lemma in_elements_add :
    forall x y zs,
      In x (FS.elements (FS.add y zs))
      -> x = y \/ In x (FS.elements zs).
  Proof.
    intros x y zs hi.
    apply in_elements_iff_in_FS in hi.
    apply FSF.add_iff in hi; destruct hi; auto.
    right; apply in_elements_iff_in_FS; auto.
  Qed.

  Lemma add_pred_preserves_soundness :
    forall g cm cm' s s' d ds',
      frame_multistep g s d
      -> (forall d', FS.In d' ds' -> frame_multistep g s' d')
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g cm'
      -> tc_soundness_invar g
                            (TC.add_pred s (FS.add d (TC.G.succs d cm)) s' ds' cm').
  Proof.
    intros g cm cm' s s' d ds' hf ha hs hs'.
    unfold TC.add_pred; dmeq heq; auto.
    rewrite FS.fold_1; apply fold_add_edge_preserves_soundness; auto.
    intros d' hi.
    assert (hf' : frame_multistep g s' d).
    { eapply t_trans; eauto.
      apply ha; apply FSF.mem_iff; auto. }
    apply in_elements_add in hi; destruct hi as [? | hi]; subst; auto.
    eapply t_trans; eauto.
    apply hs; eauto.
    apply TC.G.In_succs_rel; auto.
    apply in_elements_iff_in_FS; auto.
  Qed.

  Lemma fold_add_pred_preserves_tc_soundness_invar :
    forall g prs cm cm' s d,
      frame_multistep g s d
      -> tc_soundness_invar_list g prs
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g cm'
      -> tc_soundness_invar g
                            (fold_left
                               (fun a p =>
                                  TC.add_pred s (FS.add d (TC.G.succs d cm)) 
                                              (fst p) (snd p) a)
                               prs cm').
  Proof.
    intros g prs; induction prs as [| (s', ds') prs IH]; intros cm cm' s d hf hs hs' hs''; sis; auto.
    apply IH; auto.
    - eapply tc_soundness_invar_list_tail; eauto. 
    - eapply add_pred_preserves_soundness; eauto.
      intros d' hi; eapply hs; eauto.
      apply in_eq.
  Qed.
      
  Lemma trans_add_edge_preserves_tc_soundness_invar :
    forall g cm s d,
      frame_multistep g s d
      -> tc_soundness_invar g cm
    -> tc_soundness_invar g (TC.trans_add_edge s d cm).
  Proof.
    intros g cm s d hf hs.
    unfold TC.trans_add_edge; dm; auto.
    rewrite FM.fold_1.
    apply fold_add_pred_preserves_tc_soundness_invar; auto.
    - apply invars_equiv; auto.
    - (* lemma *)
      rewrite FS.fold_1; apply fold_add_edge_preserves_soundness; auto.
      intros d' hi; apply in_elements_add in hi.
      destruct hi as [? | hi]; subst; auto.
      apply t_trans with (y := d); auto.
      apply hs; apply TC.G.In_succs_rel; apply in_elements_iff_in_FS; auto.
  Qed.
  
  Lemma fold_trans_add_edge_preserves_tc_soundness_invar :
    forall g es cm,
      mstep_edges_sound g es
      -> tc_soundness_invar g cm
      -> tc_soundness_invar g (fold_left (TC.trans_add_edge_list liftEdge) es cm).
  Proof.
    intros g es; induction es as [| (s, d) es IH]; intros cm hs hs'; sis; auto.
    apply IH; clear IH.
    - red; intros; apply hs; apply in_cons; auto.
    - unfold TC.trans_add_edge_list; unfold TC.trans_add_edge'; sis.
      apply trans_add_edge_preserves_tc_soundness_invar; auto.
      apply hs; apply in_eq.
  Qed.

  Lemma transClos_result_sound :
    forall g,
      tc_soundness_invar g (transClos (epsilonEdges g)).
  Proof.
    intros g; unfold transClos, TC.trans_clos_list.
    apply fold_trans_add_edge_preserves_tc_soundness_invar. 
    - apply step_edges_sound__mstep_edges_sound.
      apply epsilonEdges__step_edges_sound.
    - (* lemma : invariant starts true *)
      red. intros s d hr.
      red in hr.
      destruct hr as [ds [hf hi]].
      rewrite FMF.empty_o in hf; inv hf.
  Qed.

  (* completeness of transitive closure operation *)

  Definition closure_map_complete_wrt_edges cm es :=
    forall x y, In (x, y) es -> TC.G.rel cm x y.

  Lemma add_edge_preserves_old_edges :
    forall x x' y y' cm,
      TC.G.rel cm x y
      -> TC.G.rel (TC.G.add_edge x' y' cm) x y.
  Proof.
    intros x x' y y' cm hr; red; red in hr.
    destruct hr as [ys [hf hi]].
    unfold TC.G.add_edge.
    destruct (SF_as_UOT.eq_dec x' x) as [he | hn]; subst.
    - destruct (SF_as_UOT.eq_dec y' y) as [he' | hn']; subst.
      + eexists; split.
        * rewrite FMF.add_eq_o; auto.
        * apply FS.add_1; auto.
      + eexists; split.
        * rewrite FMF.add_eq_o; auto.
        * apply FS.add_2.
          unfold TC.G.succs; rewrite hf; auto.
    - eexists; split; eauto.
      rewrite FMF.add_neq_o; auto.
  Qed.

  Lemma add_edge_adds_edge :
    forall x y cm,
      TC.G.rel (TC.G.add_edge x y cm) x y.
  Proof.
    intros x y cm; red; unfold TC.G.add_edge.
    eexists; split.
    - rewrite FMF.add_eq_o; eauto.
    - apply FS.add_1; auto.
  Qed.

  Lemma trans_add_edge_preserves_cm_complete_invar :
    forall cm es x y,
      closure_map_complete_wrt_edges cm es
      -> closure_map_complete_wrt_edges (TC.trans_add_edge x y cm) (es ++ [(x, y)]).
  Proof.
    intros cm es x y hc.
    red. intros x' y' hi.
    apply TC.add_edge_incl_trans.
    apply in_app_or in hi; destruct hi as [hi | hi].
    - apply hc in hi.
      apply add_edge_preserves_old_edges; auto.
    - apply in_singleton_eq in hi; inv hi.
      apply add_edge_adds_edge.
  Qed.
  
  Lemma fold_trans_add_edge_list_keeps_old_edges :
    forall suf pre cm,
      closure_map_complete_wrt_edges cm pre
      -> closure_map_complete_wrt_edges (fold_left (TC.trans_add_edge_list liftEdge) suf cm) (pre ++ suf).
  Proof.
    intros suf; induction suf as [| (x, y) suf IH]; intros pre cm hc; rew_anr; sis; auto.
    rewrite cons_app_singleton; rewrite app_assoc; apply IH.
    unfold TC.trans_add_edge_list; sis.
    unfold TC.trans_add_edge'.
    apply trans_add_edge_preserves_cm_complete_invar; auto.
  Qed.

  Lemma transClos_holds_orig_edges :
    forall es x y,
      In (x, y) es
      -> TC.G.rel (transClos es) x y.
  Proof.
    intros es x y hi.
    unfold transClos, TC.trans_clos_list.
    apply fold_trans_add_edge_list_keeps_old_edges with (pre := []); auto.
    red; intros x' y' hc; inv hc.
  Qed.
  
  Lemma transClos_complete :
    forall g s d,
      frame_multistep g s d
      -> TC.G.rel (transClos (epsilonEdges g)) s d.
  Proof.
    intros g s d hf; induction hf.
    - apply transClos_holds_orig_edges.
      apply epsilonEdges__step_edges_complete; auto.
    - eapply TC.transitive_trans_clos_list; eauto.
  Qed.
  
  (* After performing the transitive closure,
     we keep only the "stable" edges *)

  Definition stable (fr : suffix_frame) : bool :=
    match fr with
    | SF None []             => true
    | SF _        (T _ :: _) => true
    | _                      => false
    end.

  Lemma stable_compat_bool :
    compat_bool eq stable.
  Proof.
    repeat red; intros; subst; auto.
  Qed.

  Lemma stable_config__stable_true :
    forall fr frs,
      stable_config (fr, frs)
      -> stable fr = true.
  Proof.
    intros fr frs hs; inv hs; auto.
    sis; dm; tc.
  Qed.

  Definition keepStableNodes (s : FS.t) : list suffix_frame :=
    FS.elements (FS.filter stable s).

  Lemma keepStableNodes_stable :
    forall fr frs,
      In fr (keepStableNodes frs)
      -> stable fr = true.
  Proof.
    intros fr frs hi.
    unfold keepStableNodes in hi.
    apply in_elements_iff_in_FS in hi.
    eapply FS.filter_2; eauto.
    apply stable_compat_bool.
  Qed.

  (* A closure graph is a map where each key K is a suffix frame 
     (i.e., grammar location), and each value V is a list of frames 
     that are epsilon-reachable from K *)
  Definition closure_map := FM.t (list suffix_frame).

  Definition keepStableEdges (g : TC.G.graph) : closure_map :=
    FM.map keepStableNodes g.
  
  Definition mkClosureMap (g : grammar) : closure_map :=
    keepStableEdges (transClos (epsilonEdges g)).

  Definition destFrames (fr : suffix_frame) (cm : closure_map) : list suffix_frame :=
    match FM.find fr cm with
    | Some frs => frs
    | None     => []
    end.

  (* mkClosureMap spec and correctness proofs *)

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
    split.
    - (* lemma about keepStableEdges *)
      assert (hex : exists ds',
                 FM.MapsTo s ds' (transClos (epsilonEdges g))
                 /\ FS.In d ds').
      { apply FMF.map_mapsto_iff in hm.
        destruct hm as [ds' [? hm]]; subst; eauto.
        eexists; split; eauto.
        unfold keepStableNodes in hi.
        eapply in_elements_iff_in_FS in hi.
        apply FSF.filter_iff in hi.
        - destruct hi; auto.
        - repeat red; intros; subst; auto. }
      destruct hex as [ds' [hm' hi']].
      apply FMF.find_mapsto_iff in hm'.
      apply transClos_result_sound; red; eauto.
    - apply FMF.map_mapsto_iff in hm.
      destruct hm as [ds' [he hm]]; subst.
      eapply keepStableNodes_stable; eauto.
  Qed.

  Lemma mkClosureMap_complete :
    forall g,
      closure_map_complete g (mkClosureMap g).
  Proof.
    intros g s d hf hs.
    unfold mkClosureMap.
    apply transClos_complete in hf.
    red in hf.
    destruct hf as [ds [hf hi]].
    exists (FS.elements (FS.filter stable ds)); split.
    - apply FMF.map_mapsto_iff.
      exists ds; split; auto.
      apply FMF.find_mapsto_iff; auto.
    - apply in_elements_iff_in_FS.
      apply FS.filter_3; auto.
      apply stable_compat_bool.
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
