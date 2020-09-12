Require Import FMaps List FSets Program.Wf.
Require Import GallStar.GrammarAnalysis.
Require Import GallStar.Lex.
Require Import GallStar.Orders.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module SllPredictionFn (Import D : Defs.T).

  Module Export GA := GrammarAnalysisFn D.

  (* Now for the parts that correspond to the LL prediction module *)

  Definition simReturn (cm : closure_map) (sp : subparser) : option (list subparser) :=
    match sp with
    | Sp pred (SF (Some x) [], []) =>
      let dsts := destFrames (SF (Some x) []) cm in
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

  Lemma simReturn_stack_shape :
    forall cm sp sps',
      simReturn cm sp = Some sps'
      -> exists x, stack sp = (SF (Some x) [], []).
  Proof.
    intros cm sp sps' hr; unfold simReturn in hr; dms; inv hr; sis; eauto.
  Qed.
  
  Fixpoint sllc (g  : grammar)
                (pm : production_map)
                (hc : production_map_correct pm g)
                (cm : closure_map)
                (av : NtSet.t)
                (sp : subparser)
                (a  : Acc lex_nat_pair (meas g av sp))
    : closure_result :=
    match simReturn cm sp with
    | Some sps' => inr sps'
    | None      =>
      match cstep g pm av sp as r return cstep g pm av sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hin =>
                                  sllc g pm hc cm av' sp'
                                       (acc_after_step _ _ _ hc hs hin a))
          in  aggrClosureResults crs
      end eq_refl
    end.

  Lemma sllc_unfold :
    forall g pm (hc : production_map_correct pm g) cm av sp a,
      sllc g pm hc cm av sp a =
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match cstep g pm av sp as r return cstep g pm av sp = r -> _ with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK av' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hin =>
                                    sllc g pm hc cm av' sp'
                                          (acc_after_step _ _ _ hc hs hin a))
            in  aggrClosureResults crs
        end eq_refl
      end.
  Proof.
    intros g pm hc cm av sp a; destruct a; auto. 
  Qed.

  Lemma sllc_cases' :
    forall (g   : grammar)
           (pm  : production_map)
           (hc  : production_map_correct pm g)
           (cm  : closure_map)
           (av  : NtSet.t)
           (sp  : subparser)
           (a   : Acc lex_nat_pair (meas g av sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result)
           (heq : cstep g pm av sp = sr),
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sr as r return cstep g pm av sp = r -> closure_result with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK av' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hin => sllc g pm hc cm av' sp'
                                                       (acc_after_step _ _ _ hc hs hin a))
            in  aggrClosureResults crs
        end heq
      end = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : cstep g pm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc g pm hc cm av' sp'
                                       (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((sr = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list subparser)
                            (av'  : NtSet.t)
                            (hs   : cstep g pm av sp = CstepK av' sps')
                            (crs  : list closure_result),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc g pm hc cm av' sp'
                                             (acc_after_step _ _ _ hc hs hi a))
                     /\ aggrClosureResults crs = inr sps)
         end.
  Proof.
    intros g pm hc cm av sp a sr cr heq.
    dms; tc; intros heq'; try solve [inv heq'; eauto | eauto 10].
  Qed.
  
  Lemma sllc_cases :
    forall (g  : grammar)
           (pm  : production_map)
           (hc  : production_map_correct pm g)
           (cm : closure_map)
           (sp : subparser)
           (av : NtSet.t)
           (a  : Acc lex_nat_pair (meas g av sp))
           (cr : closure_result),
      sllc g pm hc cm av sp a = cr
      -> match cr with
         | inl e => 
           cstep g pm av sp = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : cstep g pm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc g pm hc cm av' sp'
                                   (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((cstep g pm av sp = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list subparser)
                            (av'  : NtSet.t)
                            (hs   : cstep g pm av sp = CstepK av' sps')
                            (crs  : list closure_result),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc g pm hc cm av' sp'
                                             (acc_after_step _ _ _ hc hs hi a))
                     /\ aggrClosureResults crs = inr sps)
                  end.
  Proof.
    intros g pm hc cm av sp a cr hs; subst.
    rewrite sllc_unfold.
    eapply sllc_cases'; eauto.
  Qed.

  Lemma sllc_success_cases :
    forall g pm (hc : production_map_correct pm g) cm av sp a sps,
      sllc g pm hc cm av sp a = inr sps
      -> simReturn cm sp = Some sps
         \/ simReturn cm sp = None
            /\ ((cstep g pm av sp = CstepDone /\ sps = [sp])
                \/ exists (sps' : list subparser)
                          (av'  : NtSet.t)
                          (hs   : cstep g pm av sp = CstepK av' sps')
                          (crs  : list closure_result),
                   crs = dmap sps' (fun sp' hi => 
                                      sllc g pm hc cm av' sp'
                                           (acc_after_step _ _ _ hc hs hi a))
                   /\ aggrClosureResults crs = inr sps).
  Proof.
    intros ? ? ? ? ? ? ? sps; apply sllc_cases with (cr := inr sps); auto.
  Qed.

  Lemma sllc_error_cases :
    forall g pm (hc : production_map_correct pm g) cm sp av a e,
      sllc g pm hc cm av sp a = inl e
      -> cstep g pm av sp = CstepError e
         \/ exists (sps : list subparser)
                   (av' : NtSet.t)
                   (hs  : cstep g pm av sp = CstepK av' sps)
                   (crs : list closure_result),
          crs = dmap sps (fun sp' hi => 
                            sllc g pm hc cm av' sp' (acc_after_step _ _ _ hc hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros g pm hc cm sp av a e hs; apply sllc_cases with (cr := inl e); auto.
  Qed.

    Lemma sllc_preserves_prediction' :
    forall g pm (hc : production_map_correct pm g) cm pair (a : Acc lex_nat_pair pair) av sp sp' sps' a',
      pair = meas g av sp
      -> sllc g pm hc cm av sp a' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros g pm hc cm pair a.
    induction a as [pair hlt IH]; intros av sp sp' sps' a' heq hs hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs heq] | [sps'' [av' [hs [crs [heq heq']]]]]]]]; subst.
    - eapply simReturn_preserves_prediction; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - (* lemma *)
      eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      + apply cstep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply cstep_meas_lt; eauto.
  Qed.

  Lemma sllc_preserves_prediction :
    forall g pm (hc : production_map_correct pm g) cm av sp sp' sps' (a : Acc lex_nat_pair (meas g av sp)),
      sllc g pm hc cm av sp a = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply sllc_preserves_prediction'; eauto.
  Qed.
  
  Definition sllClosure (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (cm : closure_map) (sps : list subparser) :
    sum prediction_error (list subparser) :=
    aggrClosureResults (map (fun sp => sllc g pm hc cm (allNts g) sp (lex_nat_pair_wf _)) sps).

  Lemma sllClosure_preserves_prediction :
    forall g pm (hc : production_map_correct pm g) cm sps sp' sps',
      sllClosure g pm hc cm sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp' = prediction sp.
  Proof.
    intros g pm hpc cm sps sp' sps' hc hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    apply in_map_iff in hi'; destruct hi' as [sp [hspc hi''']].
    eexists; split; eauto.
    eapply sllc_preserves_prediction; eauto.
  Qed.

  (* SLL prediction *)
  (* Goal : replace FMapWeakList with FMapAVL *)

  Module Subparser_as_UOT <: UsualOrderedType.

    Module L := List_as_UOT SF_as_UOT.
    Module P := Pair_as_UOT Gamma_as_UOT L.

    Definition t := subparser.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt (x y : subparser) : Prop :=
      match x, y with
      | Sp pred (fr, frs), Sp pred' (fr', frs') =>
        P.lt (pred, fr :: frs) (pred', fr' :: frs')
      end.

    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros [p (f, fs)] [p' (f', fs')] [p'' (f'', fs'')];
        apply P.lt_trans.
    Qed.

    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros [p (f, fs)] [p' (f', fs')] hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    Definition compare (x y : subparser) : Compare lt eq x y.
      refine (match x, y with
              | Sp pred (fr, frs), Sp pred' (fr', frs') =>
                match P.compare (pred, fr :: frs) (pred', fr' :: frs') with
                | LT hl => LT _
                | GT he => GT _
                | EQ hl => EQ _
                end
              end); red; tc.
    Defined.

    Definition eq_dec (x y : subparser) : {x = y} + {x <> y}.
      refine (match x, y with
              | Sp pred (fr, frs), Sp pred' (fr', frs') =>
                match P.eq_dec (pred, fr :: frs) (pred', fr' :: frs') with
                | left he  => left _
                | right hn => right _
                end
              end); tc.
    Defined.

  End Subparser_as_UOT.
  
  Definition cache_key := (list subparser * terminal)%type.

  Module CacheKey_as_UOT <: UsualOrderedType.

    Module L := List_as_UOT Subparser_as_UOT.
    Module P := Pair_as_UOT L T_as_UOT.

    Definition t := cache_key.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    (* Try flipping the order of the pair,
       in case that leads to fail fast behavior *)
    Definition lt (x y : cache_key) : Prop :=
      P.lt x y.

    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros (sps, a) (sps', a') (sps'', a''); apply P.lt_trans.
    Qed.

    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros (sps, a) (sps', a') hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    Definition compare : forall x y : cache_key, Compare lt eq x y :=
      P.compare.

    Definition eq_dec : forall x y : cache_key, {x = y} + {x <> y} :=
      P.eq_dec.

  End CacheKey_as_UOT.

  (*Lemma cache_key_eq_dec : 
    forall k k' : cache_key,
      {k = k'} + {k <> k'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Defined.*)
(*
  Module MDT_CacheKey.
    Definition t := cache_key.
    Definition eq_dec := cache_key_eq_dec.
  End MDT_CacheKey.
  Module CacheKey_as_DT := Make_UDT(MDT_CacheKey).
  Module Cache := FMapWeakList.Make CacheKey_as_DT.
  Module CacheFacts := WFacts_fun CacheKey_as_DT Cache.
 *)

  Module Cache      := FMapAVL.Make CacheKey_as_UOT.
  Module CacheFacts := FMapFacts.Facts Cache.
  
  (* A cache is a finite map with (list subparser * terminal) keys 
     and (list subparser) values *)
  Definition cache : Type := Cache.t (list subparser).

  Definition empty_cache : cache := Cache.empty (list subparser).
  
  Definition sllTarget g pm (hc : production_map_correct pm g) cm (a : terminal) (sps : list subparser) : sum prediction_error (list subparser) :=
    match move a sps with
    | inl e    => inl e
    | inr sps' =>
      match sllClosure g pm hc cm sps' with
      | inl e => inl e
      | inr sps'' => inr sps''
      end
    end.

  Lemma sllTarget_preserves_prediction :
    forall g pm (hc : production_map_correct pm g) cm sps a sp' sps',
      sllTarget g pm hc cm a sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp = prediction sp'.
  Proof.
    intros g pm hpc cm sps a sp' sps'' hs hi.
    unfold sllTarget in hs.
    destruct (move _ _)         as [? | sps' ] eqn:hm; tc.
    destruct (sllClosure _ _ _) as [? | ?    ] eqn:hc; tc; inv hs.
    eapply sllClosure_preserves_prediction in hc; eauto.
    destruct hc as [sp'' [hi'' heq]]; rewrite heq.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [? [? ?]]; eauto.
  Qed.

  Definition cache_stores_target_results g pm (hc : production_map_correct pm g) cm ca :=
    forall sps a sps',
      Cache.find (sps, a) ca = Some sps'
      -> sllTarget g pm hc cm a sps = inr sps'.
  
  Lemma sllTarget_add_preserves_cache_invar :
    forall gr pm (hc : production_map_correct pm gr) cm ca sps a sps',
      cache_stores_target_results gr pm hc cm ca
      -> sllTarget gr pm hc cm a sps = inr sps'
      -> cache_stores_target_results gr pm hc cm (Cache.add (sps, a) sps' ca).
  Proof.
    intros gr pm hpc cm ca sps a sps' hc ht ka kb v hf.
    destruct (CacheKey_as_UOT.eq_dec (ka, kb) (sps, a)) as [he | hn].
    - inv he; rewrite CacheFacts.add_eq_o in hf; inv hf; auto.
    - rewrite CacheFacts.add_neq_o in hf; auto.
  Qed.
  
  Fixpoint sllPredict' (gr  : grammar)
                       (pm  : production_map)
                       (hc  : production_map_correct pm gr)
                       (cm  : closure_map)
                       (sps : list subparser)
                       (ts  : list token)
                       (ca  : cache) : prediction_result * cache :=
    match ts with
    | []            => (handleFinalSubparsers sps, ca)
    | (a, l) :: ts' =>
      match sps with
      | []          => (PredReject, ca)
      | sp' :: sps' =>
        if allPredictionsEqual sp' sps' then
          (PredSucc sp'.(prediction), ca)
        else
          match Cache.find (sp' :: sps', a) ca with 
          | Some sps'' => sllPredict' gr pm hc cm sps'' ts' ca
          | None       =>
            match sllTarget gr pm hc cm a (sp' :: sps') with
            | inl e     => (PredError e, ca)
            | inr sps'' =>
              let ca' := Cache.add (sp' :: sps', a) sps'' ca
              in  sllPredict' gr pm hc cm sps'' ts' ca'
            end
          end
      end
    end.

  Lemma sllPredict'_succ_preserves_cache_invar :
    forall gr pm (hc : production_map_correct pm gr) cm ts sps ca ys ca',
      cache_stores_target_results gr pm hc cm ca
      -> sllPredict' gr pm hc cm sps ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr pm hc cm ca'.
  Proof.
    intros gr pm hpc cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca ys ca' hc hs; sis.
    - dms; tc; inv hs; auto.
    - dm; tc; dm; try solve [inv hs; auto]; dm; eauto.
      dmeq ht; tc. apply IH in hs; auto.
      apply sllTarget_add_preserves_cache_invar; auto.
  Qed.

  Lemma sllPredict'_success_result_in_original_subparsers :
    forall g pm (hc : production_map_correct pm g) cm ts ca ca' ys sps,
      cache_stores_target_results g pm hc cm ca
      -> sllPredict' g pm hc cm sps ts ca = (PredSucc ys, ca')
      -> exists sp, In sp sps /\ sp.(prediction) = ys.
  Proof.
    intros g pm hpc cm ts. 
    induction ts as [| (a,l) ts IH]; intros ca ca' ys sps hc hp; sis.
    - injection hp; intros _ hh. 
      apply handleFinalSubparsers_succ_facts in hh.
      destruct hh as (sp' & _ & hi & heq & _); eauto. 
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall.
      + inv hp; exists sp'; split; auto; apply in_eq.
      + dmeq hf; tc.
        * apply IH in hp; auto; destruct hp as [sp'' [hi heq]]; subst.
          apply hc in hf; auto.
          eapply sllTarget_preserves_prediction; eauto.
        * dmeq ht; tc; apply IH in hp.
          -- destruct hp as [sp'' [hi ?]]; subst.
             eapply sllTarget_preserves_prediction; eauto.
          -- eapply sllTarget_add_preserves_cache_invar; eauto.
  Qed.
  
  Definition sllInitSps (pm : production_map) (x : nonterminal) : list subparser :=
    map (fun rhs => Sp rhs (SF (Some x) rhs, []))
        (rhssFor x pm).

  Lemma sllInitSps_prediction_in_rhssFor :
    forall pm x sp,
      In sp (sllInitSps pm x)
      -> In sp.(prediction) (rhssFor x pm).
  Proof.
    intros pm x sp hi; unfold sllInitSps in hi.
    apply in_map_iff in hi; firstorder; subst; auto.
  Qed. 

  Definition sllStartState (g : grammar)
                           (pm : production_map)
                           (hc : production_map_correct pm g)
                           (cm : closure_map)
                           (x : nonterminal) : sum prediction_error (list subparser) :=
    sllClosure g pm hc cm (sllInitSps pm x).

  Lemma sllStartState_sp_prediction_in_rhssFor :
    forall g pm (hc : production_map_correct pm g) cm x sp' sps',
      sllStartState g pm hc cm x = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhssFor x pm).
  Proof.
    intros g pm hc cm x sp' sps' hs hi.
    unfold sllStartState in hs.
    eapply sllClosure_preserves_prediction in hs; eauto.
    destruct hs as [sp [hi' heq]]; rewrite heq.
    apply sllInitSps_prediction_in_rhssFor; auto.
  Qed.

  Definition sllPredict (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (cm : closure_map) (x : nonterminal)
             (ts : list token) (c : cache) : prediction_result * cache :=
    match sllStartState g pm hc cm x with
    | inl msg => (PredError msg, c)
    | inr sps => sllPredict' g pm hc cm sps ts c
    end.

  Lemma sllPredict_succ_in_rhssFor :
    forall g pm hc cm x ts ca ca' ys,
      cache_stores_target_results g pm hc cm ca
      -> sllPredict g pm hc cm x ts ca = (PredSucc ys, ca')
      -> In ys (rhssFor x pm).
  Proof.
    intros g pm hpc cm x ts ca ca' ys hc hs; unfold sllPredict in hs.
    dmeq hs'; tc.
    eapply sllPredict'_success_result_in_original_subparsers in hs; eauto.
    destruct hs as [sp [hi heq]]; subst.
    eapply sllStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma sllPredict_succ_preserves_cache_invar :
    forall gr pm hc cm x ts ca ys ca',
      cache_stores_target_results gr pm hc cm ca
      -> sllPredict gr pm hc cm x ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr pm hc cm ca'.
  Proof.
    intros gr pm hpc cm x ts ca ys ca' hc hs.
    unfold sllPredict in hs; dms; tc.
    eapply sllPredict'_succ_preserves_cache_invar; eauto.
  Qed.
      
  Definition adaptivePredict g pm (hc : production_map_correct pm g) cm x stk ts c : prediction_result * cache :=
    let sll_res := sllPredict g pm hc cm x ts c in
    match sll_res with
    | (PredAmbig _, _) => (llPredict hc x stk ts, c)
    | _ => sll_res
    end.
  
  Lemma adaptivePredict_succ_in_rhssFor :
    forall g pm hc cm x ss ts ca ca' ys,
      cache_stores_target_results g pm hc cm ca
      -> adaptivePredict g pm hc cm x ss ts ca = (PredSucc ys, ca')
      -> In ys (rhssFor x pm).
  Proof.
    intros g pm hpc cm x ss ts ca ca' ys hc ha.
    unfold adaptivePredict in ha; dmeqs h; tc; inv ha.
    - eapply sllPredict_succ_in_rhssFor; eauto.
    - eapply llPredict_succ_in_rhssFor; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_in_grammar :
    forall g pm hc cm x ss ts ca ca' ys,
      cache_stores_target_results g pm hc cm ca
      -> adaptivePredict g pm hc cm x ss ts ca = (PredSucc ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g pm hpc cm x ss ts ca ca' ys hc ha.
    eapply rhssFor_in_iff; eauto.
    eapply adaptivePredict_succ_in_rhssFor; eauto.
  Qed.

  Lemma adaptivePredict_ambig_in_grammar :
    forall g pm hc cm x ss ts ca ca' ys,
      cache_stores_target_results g pm hc cm ca
      -> adaptivePredict g pm hc cm x ss ts ca = (PredAmbig ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g pm hpc cm x ss ts ca ca' ys hc ha.
    unfold adaptivePredict in ha; dms; tc; inv ha.
    eapply llPredict_ambig_in_grammar; eauto.
  Qed.

  Lemma adaptivePredict_succ_preserves_cache_invar :
    forall gr pm hc cm x ss ts ca ys ca',
      cache_stores_target_results gr pm hc cm ca
      -> adaptivePredict gr pm hc cm x ss ts ca = (PredSucc ys, ca')
      -> cache_stores_target_results gr pm hc cm ca'.
  Proof.
    intros gr pm hpc cm x ss ts ca ys ca' hc ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
    eapply sllPredict_succ_preserves_cache_invar; eauto.
  Qed.

  Lemma adaptivePredict_ambig_preserves_cache_invar :
    forall gr pm hc cm x ss ts ca ys ca',
      cache_stores_target_results gr pm hc cm ca
      -> adaptivePredict gr pm hc cm x ss ts ca = (PredAmbig ys, ca')
      -> cache_stores_target_results gr pm hc cm ca'.
    intros gr pm hpc cm x ss ts ca ys ca' hc ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
  Qed.
  
End SllPredictionFn.
