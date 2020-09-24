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

  Lemma simReturn_push_invar :
    forall pm cm sp sps',
      simReturn cm sp = Some sps'
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm [pred (fr, frs)] sps' hr sp' hi; sis; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [[o suf] [heq hi]]; subst. 
    repeat red; auto.
  Qed.
  
  Fixpoint sllc (pm : production_map)
                (cm : closure_map)
                (vi : NtSet.t)
                (sp : subparser)
                (hk : sp_pushes_from_keyset pm sp)
                (a  : Acc lex_nat_pair (meas pm vi sp))
    : closure_result :=
    match simReturn cm sp with
    | Some sps' => inr sps'
    | None      =>
      match cstep pm vi sp as r return cstep pm vi sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK vi' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hi =>
                                  sllc pm cm vi' sp'
                                       (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                       (acc_after_step _ _ _ _ _ _ hk hs hi a))
          in  aggrClosureResults crs
      end eq_refl
    end.

  Lemma sllc_unfold :
    forall pm cm vi sp hk a,
      sllc pm cm vi sp hk a =
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match cstep pm vi sp as r return cstep pm vi sp = r -> _ with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi =>
                                    sllc pm cm vi' sp'
                                         (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                          (acc_after_step _ _ _ _ _ _ hk hs hi a))
            in  aggrClosureResults crs
        end eq_refl
      end.
  Proof.
    intros pm cm vi sp hk a; destruct a; auto.
  Qed.

  Lemma sllc_cases' :
    forall (pm  : production_map)
           (cm  : closure_map)
           (vi  : NtSet.t)
           (sp  : subparser)
           (hk  : sp_pushes_from_keyset pm sp)
           (a   : Acc lex_nat_pair (meas pm vi sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result)
           (heq : cstep pm vi sp = sr),
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sr as r return cstep pm vi sp = r -> closure_result with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi => sllc pm cm vi' sp'
                                                     (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                                       (acc_after_step _ _ _ _ _ _ hk hs hi a))
            in  aggrClosureResults crs
        end heq
      end = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep pm vi sp = CstepK vi' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc pm cm vi' sp'
                                      (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                       (acc_after_step _ _ _ _ _ _ hk hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((sr = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list subparser)
                            (vi'  : NtSet.t)
                            (hs   : cstep pm vi sp = CstepK vi' sps')
                            (crs  : list closure_result),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc pm cm vi' sp'
                                             (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                             (acc_after_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggrClosureResults crs = inr sps)
         end.
  Proof.
    intros pm cm vi sp hk a sr cr heq.
    dms; tc; intros heq'; try solve [inv heq'; eauto | eauto 10].
  Qed.
  
  Lemma sllc_cases :
    forall (pm : production_map)
           (cm : closure_map)
           (sp : subparser)
           (vi : NtSet.t)
           (hk : sp_pushes_from_keyset pm sp)
           (a  : Acc lex_nat_pair (meas pm vi sp))
           (cr : closure_result),
      sllc pm cm vi sp hk a = cr
      -> match cr with
         | inl e => 
           cstep pm vi sp = CstepError e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep pm vi sp = CstepK vi' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 sllc pm cm vi' sp'
                                      (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                   (acc_after_step _ _ _ _ _ _ hk hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((cstep pm vi sp = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list subparser)
                            (vi'  : NtSet.t)
                            (hs   : cstep pm vi sp = CstepK vi' sps')
                            (crs  : list closure_result),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc pm cm vi' sp'
                                             (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                             (acc_after_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggrClosureResults crs = inr sps)
                  end.
  Proof.
    intros pm cm vi sp hk a cr hs; subst.
    rewrite sllc_unfold.
    eapply sllc_cases'; eauto.
  Qed.

  Lemma sllc_success_cases :
    forall pm cm vi sp hk a sps,
      sllc pm cm vi sp hk a = inr sps
      -> simReturn cm sp = Some sps
         \/ simReturn cm sp = None
            /\ ((cstep pm vi sp = CstepDone /\ sps = [sp])
                \/ exists (sps' : list subparser)
                          (vi'  : NtSet.t)
                          (hs   : cstep pm vi sp = CstepK vi' sps')
                          (crs  : list closure_result),
                   crs = dmap sps' (fun sp' hi => 
                                      sllc pm cm vi' sp'
                                           (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                           (acc_after_step _ _ _ _ _ _ hk hs hi a))
                   /\ aggrClosureResults crs = inr sps).
  Proof.
    intros ? ? ? ? ? ? sps ?; apply sllc_cases with (cr := inr sps); auto.
  Qed.

  Lemma sllc_error_cases :
    forall pm cm sp vi hk a e,
      sllc pm cm vi sp hk a = inl e
      -> cstep pm vi sp = CstepError e
         \/ exists (sps : list subparser)
                   (vi' : NtSet.t)
                   (hs  : cstep pm vi sp = CstepK vi' sps)
                   (crs : list closure_result),
          crs = dmap sps (fun sp' hi => 
                            sllc pm cm vi' sp'
                                 (cstep_preserves_pfk _ _ _ _ _ _ hk hs hi)
                                 (acc_after_step _ _ _ _ _ _ hk hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros pm cm sp vi hk a e hs; apply sllc_cases with (cr := inl e); auto.
  Qed.

    Lemma sllc_preserves_prediction' :
    forall pm cm pair (a : Acc lex_nat_pair pair) vi sp sp' sps' hk a',
      pair = meas pm vi sp
      -> sllc pm cm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros pm cm pair a.
    induction a as [pair hlt IH]; intros vi sp sp' sps' hk a' heq hs hi; subst.
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
    forall pm cm vi sp sp' sps' hk (a : Acc lex_nat_pair (meas pm vi sp)),
      sllc pm cm vi sp hk a = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply sllc_preserves_prediction'; eauto.
  Qed.

  Lemma sllc_preserves_push_invar' :
    forall pm cm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sps',
      pair = meas pm vi sp
      -> sllc pm cm vi sp hk ha' = inr sps'
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sps'' heq hc; subst.
    pose proof hc as hc'; apply sllc_success_cases in hc.
    destruct hc as [hr | [hr [[hc heq] | [sps' [vi' [hc [crs [heq heq']]]]]]]]; subst; intros sp''' hi.
    - eapply simReturn_push_invar; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      eapply cstep_meas_lt; eauto.
  Qed.

  Lemma sllc_preserves_push_invar :
    forall pm cm vi sp sps' hk ha,
      sllc pm cm vi sp hk ha = inr sps'
      -> sp_pushes_from_keyset pm sp
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros; eapply sllc_preserves_push_invar'; eauto.
  Qed.

  Definition sllClosure (pm  : production_map)
                        (cm  : closure_map)
                        (sps : list subparser)
                        (hk  : all_sp_pushes_from_keyset pm sps) :
                        sum prediction_error (list subparser) :=
    aggrClosureResults (dmap sps (fun sp hi =>
                                    sllc pm cm NtSet.empty sp
                                         (pfk_list__pfk_mem _ _ sp hk hi)
                                         (lex_nat_pair_wf _))).

  Lemma sllClosure_preserves_prediction :
    forall pm cm sps hk sp' sps',
      sllClosure pm cm sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp' = prediction sp.
  Proof.
    intros pm cm sps hk sp' sps' hc hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi''' [_ hs]]].
    eexists; split; eauto.
    eapply sllc_preserves_prediction; eauto.
  Qed.

  Lemma sllClosure_preserves_push_invar :
    forall pm cm sps hk sps',
      sllClosure pm cm sps hk = inr sps'
      -> all_sp_pushes_from_keyset pm sps
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm sps hk sps'' hc ha sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eapply sllc_preserves_push_invar; eauto.
  Qed.

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

  Module Cache      := FMapAVL.Make CacheKey_as_UOT.
  Module CacheFacts := FMapFacts.Facts Cache.
  
  (* A cache is a finite map with (list subparser * terminal) keys 
     and (list subparser) values *)
  Definition cache : Type := Cache.t (list subparser).

  Definition empty_cache : cache := Cache.empty (list subparser).
  
  Definition sllTarget (pm  : production_map)
                       (cm  : closure_map)
                       (a   : terminal)
                       (sps : list subparser)
                       (hk  : all_sp_pushes_from_keyset pm sps) :
                       sum prediction_error (list subparser) :=
    match move a sps as m return move a sps = m -> _ with
    | inl e    => fun _ => inl e
    | inr sps' =>
      fun hm =>
        match sllClosure pm cm sps' (move_preserves_pfk pm a sps sps' hk hm) with
        | inl e     => inl e
        | inr sps'' => inr sps''
        end
    end eq_refl.

  Lemma sllTarget_cases' :
    forall pm cm a sps hk mr (heq : move a sps = mr) tr,
      match mr as m return move a sps = m -> _ with
      | inl e    => fun _ => inl e
      | inr sps' =>
        fun hm =>
          match sllClosure pm cm sps' (move_preserves_pfk pm a sps sps' hk hm) with
          | inl e     => inl e
          | inr sps'' => inr sps''
          end
      end heq = tr
      -> match tr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ sllClosure pm cm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', move a sps = inr sps'
                            /\ sllClosure pm cm sps' hk' = inr sps''
         end.
  Proof.
    intros pm cm a sps hk mr heq tr.
    destruct mr as [e' | sps']; intros ?; subst; auto.
    destruct (sllClosure _ _ _ _) eqn:hc; eauto.
  Qed.

  Lemma sllTarget_cases :
    forall pm cm a sps hk tr,
      sllTarget pm cm a sps hk = tr
      -> match tr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ sllClosure pm cm sps' hk' = inl e) 
         | inr sps'' =>
           (exists sps' hk',
               move a sps = inr sps' /\ sllClosure pm cm sps' hk' = inr sps'')
         end.
  Proof.
    intros pm cm a sps hk tr ht; eapply sllTarget_cases'; eauto.
  Qed.

  Lemma sllTarget_preserves_prediction :
    forall pm cm a sps hk sp' sps',
      sllTarget pm cm a sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ prediction sp = prediction sp'.
  Proof.
    intros pm cm a sps hk sp' sps'' hs hi.
    apply sllTarget_cases in hs.
    destruct hs as [sps' [hk' [hm hc]]].
    eapply sllClosure_preserves_prediction in hc; eauto.
    destruct hc as [sp'' [hi'' heq]]; rewrite heq.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [? [? ?]]; eauto.
  Qed.

  Lemma sllTarget_preserves_push_invar :
    forall pm cm a sps hk sps',
      sllTarget pm cm a sps hk = inr sps'
      -> all_sp_pushes_from_keyset pm sps
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm a sps hk sps'' ht ha.
    apply sllTarget_cases in ht.
    destruct ht as [sps' [hk' [hm hc]]].
    eapply sllClosure_preserves_push_invar; eauto.
  Qed.
  
  Lemma sllTarget_invar_irrel :
    forall pm cm a sps hk hk' tr,
      sllTarget pm cm a sps hk = tr
      -> sllTarget pm cm a sps hk' = tr.
  Proof.
    intros pm cm a sps hk hk' tr ht.
    remember (sllTarget pm cm a sps hk') as tr' eqn:ht'.
    symmetry in ht'.
    apply sllTarget_cases in ht.
    apply sllTarget_cases in ht'.
    destruct tr as [e | sps'']; destruct tr' as [e' | sps'''].
    - destruct ht as [hm | [sps' [hk'' [hm hc]]]];
        destruct ht' as [hm' | [sps'' [hk''' [hm' hc']]]]; tc.
      rewrite hm in hm'; inv hm'.
      (* lemma about sllClosure *)
      admit.
    - destruct ht as [hm | [sps' [hk'' [hm hc]]]];
        destruct ht' as [sps'' [hk''' [hm' hc']]]; tc.
      rewrite hm in hm'; inv hm'.
      (* lemma about sllClosure *)
      admit.
    - destruct ht as [sps' [hk'' [hm hc]]];
        destruct ht' as [hm' | [sps''' [hk''' [hm' hc']]]]; tc.
      rewrite hm in hm'; inv hm'.
      (* lemma *)
      admit.
    - destruct ht as [sps' [hk'' [hm hc]]];
        destruct ht' as [sps'''' [ hk''' [hm' hc']]].
      rewrite hm in hm'; inv hm'.
      admit.
  Admitted.

  Definition cache_stores_target_results pm cm ca :=
    forall sps a sps',
      Cache.find (sps, a) ca = Some sps'
      -> exists hk, sllTarget pm cm a sps hk = inr sps'.
  
  Lemma sllTarget_add_preserves_cache_invar :
    forall pm cm ca sps a sps' hk,
      cache_stores_target_results pm cm ca
      -> sllTarget pm cm a sps hk = inr sps'
      -> cache_stores_target_results pm cm (Cache.add (sps, a) sps' ca).
  Proof.
    intros pm cm ca sps a sps' hk hc ht ka kb v hf.
    destruct (CacheKey_as_UOT.eq_dec (ka, kb) (sps, a)) as [he | hn].
    - inv he; rewrite CacheFacts.add_eq_o in hf; inv hf; eauto.
    - rewrite CacheFacts.add_neq_o in hf; auto.
  Qed.

  Lemma cache_lookup_preserves_push_invar :
    forall pm cm sps a ca sps',
      cache_stores_target_results pm cm ca
      -> Cache.find (sps, a) ca = Some sps'
      -> all_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm sps a ca sps' hc hf.
    apply hc in hf.
    destruct hf as [hk ht].
    eapply sllTarget_preserves_push_invar; eauto.
  Qed.
  
  Fixpoint sllPredict' (pm  : production_map)
                       (cm  : closure_map)
                       (sps : list subparser)
                       (ts  : list token)
                       (ca  : cache)
                       (hk  : all_sp_pushes_from_keyset pm sps)
                       (hc  : cache_stores_target_results pm cm ca) :
                       prediction_result * cache :=
    match ts with
    | []            => (handleFinalSubparsers sps, ca)
    | (a, l) :: ts' =>
      match sps with
      | []          => (PredReject, ca)
      | sp' :: sps' =>
        if allPredictionsEqual sp' sps' then
          (PredSucc sp'.(prediction), ca)
        else
          match Cache.find (sps, a) ca as f
                return Cache.find (sps, a) ca = f -> _ with 
          | Some sps'' =>
            fun hf =>
               sllPredict' pm cm sps'' ts' ca
                          (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc
          | None =>
            fun _ =>
              match sllTarget pm cm a sps hk as t
                    return sllTarget pm cm a sps hk = t -> _ with
              | inl e     => fun _ => (PredError e, ca)
              | inr sps'' =>
                fun ht => 
                  let ca' := Cache.add (sps, a) sps'' ca
                  in  sllPredict' pm cm sps'' ts' ca'
                                  (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                                  (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
              end eq_refl
          end eq_refl
      end
    end.

  Lemma sllPredict'_cont_cases :
    forall pm cm sps a ts' ca hk hc fr tr pr
           (heq : Cache.find (sps, a) ca = fr)
           (heq' : sllTarget pm cm a sps hk = tr),
      match fr as f return Cache.find (sps, a) ca = f -> _ with 
      | Some sps'' =>
        fun hf =>
          sllPredict' pm cm sps'' ts' ca
                      (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc
      | None =>
        fun _ =>
          match tr as t return sllTarget pm cm a sps hk = t -> _ with
          | inl e     => fun _ => (PredError e, ca)
          | inr sps'' =>
            fun ht => 
              let ca' := Cache.add (sps, a) sps'' ca
              in  sllPredict' pm cm sps'' ts' ca'
                              (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
          end heq'
      end heq = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' pm cm sps'' ts' ca
                           (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc = (PredSucc ys, ca'))
           \/ (exists sps'' (ht : sllTarget pm cm a sps hk = inr sps''),
                  sllPredict' pm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' pm cm sps'' ts' ca
                           (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc = (PredAmbig ys, ca'))
           \/ (exists sps'' (ht : sllTarget pm cm a sps hk = inr sps''),
                  sllPredict' pm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' pm cm sps'' ts' ca
                           (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc = (PredReject, ca'))
           \/ (exists sps'' (ht : sllTarget pm cm a sps hk = inr sps''),
                  sllPredict' pm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredReject, ca'))
         | (PredError e, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' pm cm sps'' ts' ca
                           (cache_lookup_preserves_push_invar _ _ _ _ _ _ hc hf) hc = (PredError e, ca'))
           \/ sllTarget pm cm a sps hk = inl e
           \/ (exists sps'' (ht : sllTarget pm cm a sps hk = inr sps''),
                  sllPredict' pm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_push_invar _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredError e, ca'))
         end.
  Proof.
    intros pm cm sps a ts' ca hk hc fr tr pr heq heq';
      dms; intros heq''; inv heq''; eauto.
  Qed.

  Lemma sllPredict'_succ_preserves_cache_invar :
    forall pm cm ts sps ca hk hc ys ca',
      sllPredict' pm cm sps ts ca hk hc = (PredSucc ys, ca')
      -> cache_stores_target_results pm cm ca'.
  Proof.
    intros pm cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca hk hc ys ca' hs; sis.
    - dms; tc; inv hs; auto.
    - dm; tc; dm; try solve [inv hs; auto].
      apply sllPredict'_cont_cases in hs.
      destruct hs as [[sps'' [hf hs]] | [sps'' [ht hs]]]; eauto.
  Qed.

  Lemma sllPredict'_success_result_in_original_subparsers :
    forall pm cm ts sps ca hk hc ys ca',
      sllPredict' pm cm sps ts ca hk hc = (PredSucc ys, ca')
      -> exists sp, In sp sps /\ sp.(prediction) = ys.
  Proof.
    intros pm cm ts. 
    induction ts as [| (a,l) ts IH]; intros sps ca hk hc ys ca' hp; sis.
    - injection hp; intros _ hh. 
      apply handleFinalSubparsers_succ_facts in hh.
      destruct hh as (sp' & _ & hi & heq & _); eauto.
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall.
      + inv hp; exists sp'; split; auto; apply in_eq.
      + apply sllPredict'_cont_cases in hp.
        destruct hp as [[sps'' [hf hp]] | [sps'' [ht hp]]].
        * apply IH in hp; auto; destruct hp as [sp'' [hi heq]]; subst.
          apply hc in hf; destruct hf as [hk' ht].
          eapply sllTarget_preserves_prediction; eauto.
        * apply IH in hp.
          destruct hp as [sp'' [hi ?]]; subst.
          eapply sllTarget_preserves_prediction; eauto.
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

  Lemma sllInitSps_push_invar :
    forall pm x,
      all_sp_pushes_from_keyset pm (sllInitSps pm x).
  Proof.
    intros pm x sp hi.
    apply in_map_iff in hi; destruct hi as [? [heq hi]]; subst.
    repeat red; auto.
  Qed.

  Definition sllStartState (pm : production_map)
                           (cm : closure_map)
                           (x  : nonterminal) :
                           sum prediction_error (list subparser) :=
    sllClosure pm cm (sllInitSps pm x) (sllInitSps_push_invar pm x).

  Lemma sllStartState_sp_prediction_in_rhssFor :
    forall pm cm x sp' sps',
      sllStartState pm cm x = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhssFor x pm).
  Proof.
    intros pm cm x sp' sps' hs hi.
    unfold sllStartState in hs.
    eapply sllClosure_preserves_prediction in hs; eauto.
    destruct hs as [sp [hi' heq]]; rewrite heq.
    apply sllInitSps_prediction_in_rhssFor; auto.
  Qed.

  Lemma sllStartState_push_invar :
    forall pm cm x sps,
      sllStartState pm cm x = inr sps
      -> all_sp_pushes_from_keyset pm sps.
  Proof.
    intros pm cm x sps hs sp hi.
    eapply sllClosure_preserves_push_invar; eauto.
    apply sllInitSps_push_invar.
  Qed.
  
  Definition sllPredict (pm : production_map)
                        (cm : closure_map)
                        (x  : nonterminal)
                        (ts : list token)
                        (ca : cache)
                        (hc : cache_stores_target_results pm cm ca) :
                        prediction_result * cache :=
    match sllStartState pm cm x as s return sllStartState pm cm x = s -> _ with
    | inl msg => fun _  => (PredError msg, ca)
    | inr sps => fun hs => sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc
    end eq_refl.

  Lemma sllPredict_cases' :
    forall pm cm x ts ca hc cr pr (heq : sllStartState pm cm x = cr),
      match cr as s return sllStartState pm cm x = s -> _ with
      | inl msg => fun _  => (PredError msg, ca)
      | inr sps => fun hs => sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc
      end heq = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredReject, ca'))
         | (PredError e, ca') =>
           sllStartState pm cm x = inl e
           \/ (exists sps (hs : sllStartState pm cm x = inr sps),
                  sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredError e, ca'))
         end.
  Proof.
    intros pm cm x ts ca hc cr pr heq; dms; intros heq'; inv heq'; eauto.
  Qed.

  Lemma sllPredict_cases :
    forall pm cm x ts ca hc pr,
      sllPredict pm cm x ts ca hc = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps (hs : sllStartState pm cm x = inr sps),
               sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredReject, ca'))
         | (PredError e, ca') =>
           sllStartState pm cm x = inl e
           \/ (exists sps (hs : sllStartState pm cm x = inr sps),
                  sllPredict' pm cm sps ts ca (sllStartState_push_invar _ _ _ _ hs) hc = (PredError e, ca'))
         end.
  Proof.
    intros; eapply sllPredict_cases'; eauto.
  Qed.

  Lemma sllPredict_succ_in_rhssFor :
    forall pm cm x ts ca hc ys ca',
      sllPredict pm cm x ts ca hc = (PredSucc ys, ca')
      -> In ys (rhssFor x pm).
  Proof.
    intros pm cm x ts ca hc ys ca' hs.
    apply sllPredict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sllPredict'_success_result_in_original_subparsers in hp; eauto.
    destruct hp as [sp [hi heq]]; subst.
    eapply sllStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma sllPredict_succ_preserves_cache_invar :
    forall pm cm x ts ca hc ys ca',
      sllPredict pm cm x ts ca hc = (PredSucc ys, ca')
      -> cache_stores_target_results pm cm ca'.
  Proof.
    intros pm cm x ts ca hc ys ca' hs.
    apply sllPredict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sllPredict'_succ_preserves_cache_invar; eauto.
  Qed.
      
  Definition adaptivePredict (pm  : production_map)
                             (cm  : closure_map)
                             (o   : option nonterminal)
                             (x   : nonterminal)
                             (suf : list symbol)
                             (frs : list suffix_frame)
                             (ts  : list token)
                             (ca  : cache)
                             (hc  : cache_stores_target_results pm cm ca)
                             (hk  : stack_pushes_from_keyset pm (SF o (NT x :: suf), frs)):
                             prediction_result * cache :=
    let sll_res := sllPredict pm cm x ts ca hc
    in  match sll_res with
        | (PredAmbig _, _) => (llPredict pm o x suf frs ts hk, ca)
        | _                => sll_res
        end.
  
  Lemma adaptivePredict_succ_in_rhssFor :
    forall pm cm o x suf frs ts ca hc hk ys ca',
      adaptivePredict pm cm o x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> In ys (rhssFor x pm).
  Proof.
    intros pm cm o x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs h; tc; inv ha.
    - eapply sllPredict_succ_in_rhssFor; eauto.
    - eapply llPredict_succ_in_rhssFor; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_in_grammar :
    forall g pm cm o x suf frs ts ca hc hk ys ca',
      production_map_correct pm g
      -> adaptivePredict pm cm o x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g pm cm o x suf frs ts ca hc hk ys ca' hp ha.
    eapply rhssFor_in_iff; eauto.
    eapply adaptivePredict_succ_in_rhssFor; eauto.
  Qed.

  Lemma adaptivePredict_ambig_in_grammar :
    forall g pm cm o x suf frs ts ca hc hk ys ca',
      production_map_correct pm g
      -> adaptivePredict pm cm o x suf frs ts ca hc hk = (PredAmbig ys, ca')
      -> In (x, ys) g.
  Proof.
    intros g pm cm o x suf frs ts ca hc hk ys ca' hp ha.
    unfold adaptivePredict in ha; dms; tc; inv ha.
    eapply llPredict_ambig_in_grammar; eauto.
  Qed.

  Lemma adaptivePredict_succ_preserves_cache_invar :
    forall pm cm o x suf frs ts ca hc hk ys ca',
      adaptivePredict pm cm o x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> cache_stores_target_results pm cm ca'.
  Proof.
    intros pm cm o x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
    eapply sllPredict_succ_preserves_cache_invar; eauto.
  Qed.

  Lemma adaptivePredict_ambig_preserves_cache_invar :
    forall pm cm o x suf frs ts ca hc hk ys ca',
      adaptivePredict pm cm o x suf frs ts ca hc hk = (PredAmbig ys, ca')
      -> cache_stores_target_results pm cm ca'.
  Proof.
    intros pm cm o x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
  Qed.
  
End SllPredictionFn.
