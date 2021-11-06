Require Import FMaps List FSets Program.Wf.
Require Import CoStar.GrammarAnalysis.
Require Import CoStar.Lex.
Require Import CoStar.Orders.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module SllPredictionFn (Import D : Defs.T).

  Module Export GA := GrammarAnalysisFn D.

  (* move operation *)

  Definition sllMoveSp (a : terminal) (sp : sll_subparser) : subparser_move_result :=
      match sp with
      | SllSp pred stk =>
        match stk with
        | (SllFr _ [], [])            => MoveReject
        | (SllFr _ [], _ :: _)        => MoveError SpInvalidState
        | (SllFr _ (NT _ :: _), _)    => MoveError SpInvalidState
        | (SllFr o (T a' :: suf), frs) =>
          if t_eq_dec a' a then
            MoveSucc (SllSp pred (SllFr o suf, frs))
          else
            MoveReject
        end
      end.

  Lemma sllMoveSp_preserves_prediction :
    forall t sp sp',
      sllMoveSp t sp = MoveSucc sp'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros t sp sp' hm; unfold sllMoveSp in hm.
    dms; tc; subst; inv hm; auto.
  Qed.

  Lemma sllMoveSp_preserves_lhss_invar :
    forall rm a sp sp',
      sll_sp_pushes_from_keyset rm sp
      -> sllMoveSp a sp = MoveSucc sp'
      -> sll_sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm a sp sp' hk hm.
    unfold sllMoveSp in hm; dms; tc; inv hm; sis.
    red; red in hk; sis.
    eapply consume_preserves_keyset_invar; eauto.
  Qed.

  Lemma aggrMoveResults_succ_all_sll_sps_step :
    forall t sp sps sp' sps',
      In sp sps
      -> sllMoveSp t sp = MoveSucc sp'
      -> aggrMoveResults (map (sllMoveSp t) sps) = inr sps'
      -> In sp' sps'.
  Proof.
    intros t sp sps. 
    induction sps as [| hd tl IH]; intros sp' sps' hi hm ha; inv hi; sis.
    - dms; tc. 
      inv hm; inv ha.
      apply in_eq.
    - dms; tc.
      inv ha.
      apply in_cons; auto.
  Qed.

  Definition sllMove (a : terminal) (sps : list sll_subparser) : move_result sll_subparser :=
    aggrMoveResults (map (sllMoveSp a) sps).

  Lemma sllMove_preserves_prediction :
    forall t sp' sps sps',
      sllMove t sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros t sp' sps sps' hm hi.
    unfold move in hm.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    eapply in_map_iff in hm; destruct hm as [sp [hmsp hi']].
    eexists; split; eauto.
    eapply sllMoveSp_preserves_prediction; eauto.
  Qed.

  Lemma sllMove_preserves_pki :
    forall rm a sps sps',
      all_sll_sp_pushes_from_keyset rm sps
      -> sllMove a sps = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm a sps sps' hk hm sp' hi'.
    eapply aggrMoveResults_map_backwards in hm; eauto.
    destruct hm as [sp [hi hm]].
    eapply sllMoveSp_preserves_lhss_invar; eauto.
  Qed.

  (* closure operation *)

  Definition simReturn (cm : closure_map) (sp : sll_subparser) : option (list sll_subparser) :=
    match sp with
    | SllSp pred (SllFr (Some x) [], []) =>
      let dsts := destFrames (SllFr (Some x) []) cm in
      let sps' := map (fun d => SllSp pred (d, [])) dsts
      in  Some sps'
    | _ => None
    end.

  Lemma simReturn_preserves_prediction :
    forall cm sp sp' sps',
      simReturn cm sp = Some sps'
      -> In sp' sps'
      -> sll_pred sp' = sll_pred sp.
  Proof.
    intros cm [pred (fr, frs)] sp' sps' hs hi; sis; dms; tc; inv hs.
    apply in_map_iff in hi; destruct hi as [? [? ?]]; subst; auto.
  Qed.

  Lemma simReturn_stack_shape :
    forall cm sp sps',
      simReturn cm sp = Some sps'
      -> exists x, sp.(sll_stk) = (SllFr (Some x) [], []).
  Proof.
    intros cm sp sps' hr; unfold simReturn in hr; dms; inv hr; sis; eauto.
  Qed.

  Lemma simReturn_pki :
    forall pm cm sp sps',
      simReturn cm sp = Some sps'
      -> all_sll_sp_pushes_from_keyset pm sps'.
  Proof.
    intros pm cm [pred (fr, frs)] sps' hr sp' hi; sis; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [[o suf] [heq hi]]; subst. 
    repeat red; auto.
  Qed.

  Definition sllCstep (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) : 
    subparser_closure_step_result :=
    match sp with
    | SllSp pred (fr, frs) =>
      match fr, frs with
      (* return to caller frame *)
      | SllFr o [], SllFr o_cr (NT x :: suf_cr) :: frs_tl =>
        let stk':= (SllFr o_cr suf_cr, frs_tl) 
        in  CstepK (NtSet.remove x vi) [SllSp pred stk']
      (* done case -- top stack symbol is a terminal *)
      | SllFr _ (T _ :: _), _ => CstepDone
      (* push case *)
      | SllFr o (NT x :: suf), _ =>
        if NtSet.mem x vi then
          (* Unreachable for a left-recursive grammar *)
          match NM.find x rm with
          | Some _ => CstepError (SpLeftRecursion x)
          | None   => CstepK NtSet.empty []
          end
        else
          let sps' := map (fun rhs => SllSp pred (SllFr (Some x) rhs, fr :: frs))
                          (rhssFor x rm)
          in  CstepK (NtSet.add x vi) sps'
      | _, _ => CstepError SpInvalidState
      end
    end.
  
  Lemma sllCstep_preserves_prediction :
    forall rm sp sp' sps' vi vi',
      sllCstep rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> sp.(sll_pred) = sp'.(sll_pred).
  Proof.
    intros rm sp sp' sps' vi vi' hs hi.
    unfold sllCstep in hs; dms; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; auto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; auto.
  Qed.

  Lemma sllCstep_preserves_pki :
    forall rm vi sp vi' sp' sps',
      sll_sp_pushes_from_keyset rm sp
      -> sllCstep rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> sll_sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm vi sp vi' sp' sps' hk hs hi.
    unfold sllCstep in hs; dms; tc; inv hs; red; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      red; repeat red in hk; sis.
      eapply return_preserves_keyset_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply push_preserves_keyset_invar; eauto.
      eapply rhssFor_keySet; eauto.
  Qed.

  Definition sll_meas (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) : nat * nat :=
    match sp with
    | SllSp _ sk => meas rm vi (sllStackSuffixes sk)
    end.

  Lemma sllCstep_meas_lt :
    forall (rm     : rhs_map)
           (sp sp' : sll_subparser)
           (sps'   : list sll_subparser)
           (vi vi' : NtSet.t),
      sll_sp_pushes_from_keyset rm sp
      -> sllCstep rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros rm sp sp' sps' vi vi' ha hs hi.
    unfold sllCstep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - red; repeat red in ha; sis.
      apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; sis.
      eapply meas_lt_after_push; eauto.
      + apply not_mem_iff; auto.
      + eapply rhssFor_keySet; eauto.
      + eapply rhssFor_allRhss; eauto.
  Defined.

  Lemma acc_after_sll_step :
    forall rm sp sp' sps' vi vi',
      sll_sp_pushes_from_keyset rm sp
      -> sllCstep rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (sll_meas rm vi sp)
      -> Acc lex_nat_pair (sll_meas rm vi' sp').
  Proof.
    intros rm sp sp' sps' vi vi' hk heq hi ha.
    eapply Acc_inv; eauto.
    eapply sllCstep_meas_lt; eauto.
  Defined.
  
  Fixpoint sllc (rm : rhs_map)
                (cm : closure_map)
                (vi : NtSet.t)
                (sp : sll_subparser)
                (hk : sll_sp_pushes_from_keyset rm sp)
                (a  : Acc lex_nat_pair (sll_meas rm vi sp))
    : closure_result sll_subparser :=
    match simReturn cm sp with
    | Some sps' => inr sps'
    | None      =>
      match sllCstep rm vi sp as r return sllCstep rm vi sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK vi' sps' => 
        fun hs => 
          let crs := dmap sps' (fun sp' hi =>
                                  sllc rm cm vi' sp'
                                       (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
          in  aggrClosureResults crs
      end eq_refl
    end.

  Lemma sllc_unfold :
    forall rm cm vi sp hk a,
      sllc rm cm vi sp hk a =
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sllCstep rm vi sp as r return sllCstep rm vi sp = r -> _ with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi =>
                                    sllc rm cm vi' sp'
                                         (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                          (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
            in  aggrClosureResults crs
        end eq_refl
      end.
  Proof.
    intros rm cm vi sp hk a; destruct a; auto.
  Qed.

  Lemma sllc_cases' :
    forall (rm  : rhs_map)
           (cm  : closure_map)
           (vi  : NtSet.t)
           (sp  : sll_subparser)
           (hk  : sll_sp_pushes_from_keyset rm sp)
           (a   : Acc lex_nat_pair (sll_meas rm vi sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result sll_subparser)
           (heq : sllCstep rm vi sp = sr),
      match simReturn cm sp with
      | Some sps' => inr sps'
      | None      =>
        match sr as r return sllCstep rm vi sp = r -> closure_result sll_subparser with
        | CstepDone       => fun _  => inr [sp]
        | CstepError e    => fun _  => inl e
        | CstepK vi' sps' => 
          fun hs => 
            let crs := dmap sps' (fun sp' hi => sllc rm cm vi' sp'
                                                     (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
            in  aggrClosureResults crs
        end heq
      end = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list sll_subparser)
                     (vi' : NtSet.t)
                     (hs  : sllCstep rm vi sp = CstepK vi' sps)
                     (crs : list (closure_result sll_subparser)),
               crs = dmap sps (fun sp' hi => 
                                 sllc rm cm vi' sp'
                                      (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                       (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((sr = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list sll_subparser)
                            (vi'  : NtSet.t)
                            (hs   : sllCstep rm vi sp = CstepK vi' sps')
                            (crs  : list (closure_result sll_subparser)),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc rm cm vi' sp'
                                             (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                             (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggrClosureResults crs = inr sps)
         end.
  Proof.
    intros rm cm vi sp hk a sr cr heq.
    dms; tc; intros heq'; try solve [inv heq'; eauto | eauto 10].
  Qed.
  
  Lemma sllc_cases :
    forall (rm : rhs_map)
           (cm : closure_map)
           (sp : sll_subparser)
           (vi : NtSet.t)
           (hk : sll_sp_pushes_from_keyset rm sp)
           (a  : Acc lex_nat_pair (sll_meas rm vi sp))
           (cr : closure_result sll_subparser),
      sllc rm cm vi sp hk a = cr
      -> match cr with
         | inl e => 
           sllCstep rm vi sp = CstepError e
           \/ exists (sps : list sll_subparser)
                     (vi' : NtSet.t)
                     (hs  : sllCstep rm vi sp = CstepK vi' sps)
                     (crs : list (closure_result sll_subparser)),
               crs = dmap sps (fun sp' hi => 
                                 sllc rm cm vi' sp'
                                      (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                   (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           simReturn cm sp = Some sps
           \/ simReturn cm sp = None
              /\ ((sllCstep rm vi sp = CstepDone /\ sps = [sp])
                  \/ exists (sps' : list sll_subparser)
                            (vi'  : NtSet.t)
                            (hs   : sllCstep rm vi sp = CstepK vi' sps')
                            (crs  : list (closure_result sll_subparser)),
                     crs = dmap sps' (fun sp' hi => 
                                        sllc rm cm vi' sp'
                                             (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                             (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                     /\ aggrClosureResults crs = inr sps)
                  end.
  Proof.
    intros rm cm vi sp hk a cr hs; subst.
    rewrite sllc_unfold.
    eapply sllc_cases'; eauto.
  Qed.

  Lemma sllc_success_cases :
    forall rm cm vi sp hk a sps,
      sllc rm cm vi sp hk a = inr sps
      -> simReturn cm sp = Some sps
         \/ simReturn cm sp = None
            /\ ((sllCstep rm vi sp = CstepDone /\ sps = [sp])
                \/ exists (sps' : list sll_subparser)
                          (vi'  : NtSet.t)
                          (hs   : sllCstep rm vi sp = CstepK vi' sps')
                          (crs  : list (closure_result sll_subparser)),
                   crs = dmap sps' (fun sp' hi => 
                                      sllc rm cm vi' sp'
                                           (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                           (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
                   /\ aggrClosureResults crs = inr sps).
  Proof.
    intros ? ? ? ? ? ? sps ?; apply sllc_cases with (cr := inr sps); auto.
  Qed.

  Lemma sllc_error_cases :
    forall rm cm sp vi hk a e,
      sllc rm cm vi sp hk a = inl e
      -> sllCstep rm vi sp = CstepError e
         \/ exists (sps : list sll_subparser)
                   (vi' : NtSet.t)
                   (hs  : sllCstep rm vi sp = CstepK vi' sps)
                   (crs : list (closure_result sll_subparser)),
          crs = dmap sps (fun sp' hi => 
                            sllc rm cm vi' sp'
                                 (sllCstep_preserves_pki _ _ _ _ _ _ hk hs hi)
                                 (acc_after_sll_step _ _ _ _ _ _ hk hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros rm cm sp vi hk a e hs; apply sllc_cases with (cr := inl e); auto.
  Qed.

  Lemma sllc_preserves_prediction' :
    forall rm cm pair (a : Acc lex_nat_pair pair) vi sp sp' sps' hk a',
      pair = sll_meas rm vi sp
      -> sllc rm cm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros rm cm pair a.
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
      + apply sllCstep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply sllCstep_meas_lt; eauto.
  Qed.

  Lemma sllc_preserves_prediction :
    forall rm cm vi sp sp' sps' hk (a : Acc lex_nat_pair (sll_meas rm vi sp)),
      sllc rm cm vi sp hk a = inr sps'
      -> In sp' sps'
      -> sp'.(sll_pred) = sp.(sll_pred).
  Proof.
    intros; eapply sllc_preserves_prediction'; eauto.
  Qed.

  Lemma sllc_preserves_pki' :
    forall rm cm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sps',
      pair = sll_meas rm vi sp
      -> sllc rm cm vi sp hk ha' = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sps'' heq hc; subst.
    pose proof hc as hc'; apply sllc_success_cases in hc.
    destruct hc as [hr | [hr [[hc heq] | [sps' [vi' [hc [crs [heq heq']]]]]]]]; subst; intros sp''' hi.
    - eapply simReturn_pki; eauto. 
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      eapply sllCstep_meas_lt; eauto.
  Qed.

  Lemma sllc_preserves_pki :
    forall rm cm vi sp sps' hk ha,
      sllc rm cm vi sp hk ha = inr sps'
      -> sll_sp_pushes_from_keyset rm sp
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros; eapply sllc_preserves_pki'; eauto.
  Qed.

  Definition sllClosure (rm  : rhs_map)
                        (cm  : closure_map)
                        (sps : list sll_subparser)
                        (hk  : all_sll_sp_pushes_from_keyset rm sps) :
                        sum prediction_error (list sll_subparser) :=
    aggrClosureResults (dmap sps (fun sp hi =>
                                    sllc rm cm NtSet.empty sp
                                         (sll_pki_list__pki_mem _ _ sp hk hi)
                                         (lex_nat_pair_wf _))).

  Lemma sllClosure_preserves_prediction :
    forall rm cm sps hk sp' sps',
      sllClosure rm cm sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sll_pred sp' = sll_pred sp.
  Proof.
    intros rm cm sps hk sp' sps' hc hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi''' [_ hs]]].
    eexists; split; eauto.
    eapply sllc_preserves_prediction; eauto.
  Qed.

  Lemma sllClosure_preserves_pki :
    forall rm cm sps hk sps',
      sllClosure rm cm sps hk = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm sps hk sps'' hc ha sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eapply sllc_preserves_pki; eauto.
  Qed.

  Module SLL_Subparser_as_UOT <: UsualOrderedType.

    Module L := List_as_UOT SllFr_as_UOT.
    Module P := Pair_as_UOT Gamma_as_UOT L.

    Definition t := sll_subparser.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt (x y : sll_subparser) : Prop :=
      match x, y with
      | SllSp pred (fr, frs), SllSp pred' (fr', frs') =>
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

    Definition compare (x y : sll_subparser) : Compare lt eq x y.
      refine (match x, y with
              | SllSp pred (fr, frs), SllSp pred' (fr', frs') =>
                match P.compare (pred, fr :: frs) (pred', fr' :: frs') with
                | LT hl => LT _
                | GT he => GT _
                | EQ hl => EQ _
                end
              end); red; tc.
    Defined.

    Definition eq_dec (x y : sll_subparser) : {x = y} + {x <> y}.
      refine (match x, y with
              | SllSp pred (fr, frs), SllSp pred' (fr', frs') =>
                match P.eq_dec (pred, fr :: frs) (pred', fr' :: frs') with
                | left he  => left _
                | right hn => right _
                end
              end); tc.
    Defined.

  End SLL_Subparser_as_UOT.

  Module SllSpSet := FSetList.Make SLL_Subparser_as_UOT.

  Definition setify (sps : list sll_subparser) : SllSpSet.t :=
    fold_right SllSpSet.add SllSpSet.empty sps.
  
  Definition cache_key := (list sll_subparser * terminal)%type.

  Module CacheKey_as_UOT <: UsualOrderedType.

    Module L := List_as_UOT SLL_Subparser_as_UOT.
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
  Definition cache : Type := Cache.t (list sll_subparser).

  Definition empty_cache : cache := Cache.empty (list sll_subparser).
  
  Definition sllTarget (rm   : rhs_map)
                       (cm   : closure_map)
                       (a    : terminal)
                       (sps  : list sll_subparser)
                       (hk   : all_sll_sp_pushes_from_keyset rm sps) :
                       sum prediction_error (list sll_subparser) :=
    match sllMove a sps as m return sllMove a sps = m -> _ with
    | inl e    => fun _ => inl e
    | inr sps' =>
      fun hm =>
        match sllClosure rm cm sps' (sllMove_preserves_pki rm a sps sps' hk hm) with
        | inl e     => inl e
        | inr sps'' => inr sps''
        end
    end eq_refl.

  Lemma sllTarget_cases' :
    forall rm cm a sps hk mr (heq : sllMove a sps = mr) tr,
      match mr as m return sllMove a sps = m -> _ with
      | inl e    => fun _ => inl e
      | inr sps' =>
        fun hm =>
          match sllClosure rm cm sps' (sllMove_preserves_pki rm a sps sps' hk hm) with
          | inl e     => inl e
          | inr sps'' => inr sps''
          end
      end heq = tr
      -> match tr with
         | inl e =>
           sllMove a sps = inl e
           \/ (exists sps' hk',
                  sllMove a sps = inr sps' /\ sllClosure rm cm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', sllMove a sps = inr sps'
                            /\ sllClosure rm cm sps' hk' = inr sps''
         end.
  Proof.
    intros rm cm a sps hk mr heq tr.
    destruct mr as [e' | sps']; intros ?; subst; auto.
    destruct (sllClosure _ _ _ _) eqn:hc; eauto.
  Qed.

  Lemma sllTarget_cases :
    forall rm cm a sps hk tr,
      sllTarget rm cm a sps hk = tr
      -> match tr with
         | inl e =>
           sllMove a sps = inl e
           \/ (exists sps' hk',
                  sllMove a sps = inr sps' /\ sllClosure rm cm sps' hk' = inl e) 
         | inr sps'' =>
           (exists sps' hk',
               sllMove a sps = inr sps' /\ sllClosure rm cm sps' hk' = inr sps'')
         end.
  Proof.
    intros rm cm a sps hk tr ht; eapply sllTarget_cases'; eauto.
  Qed.

  Lemma sllTarget_preserves_prediction :
    forall rm cm a sps hk sp' sps',
      sllTarget rm cm a sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sll_pred sp = sll_pred sp'.
  Proof.
    intros rm cm a sps hk sp' sps'' hs hi.
    apply sllTarget_cases in hs.
    destruct hs as [sps' [hk' [hm hc]]].
    eapply sllClosure_preserves_prediction in hc; eauto.
    destruct hc as [sp'' [hi'' heq]]; rewrite heq.
    eapply sllMove_preserves_prediction in hm; eauto.
    destruct hm as [? [? ?]]; eauto.
  Qed.

  Lemma sllTarget_preserves_pki :
    forall rm cm a sps hk sps',
      sllTarget rm cm a sps hk = inr sps'
      -> all_sll_sp_pushes_from_keyset rm sps
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm a sps hk sps'' ht ha.
    apply sllTarget_cases in ht.
    destruct ht as [sps' [hk' [hm hc]]].
    eapply sllClosure_preserves_pki; eauto.
  Qed.

  Definition cache_stores_target_results rm cm ca :=
    forall sps a sps',
      Cache.find (sps, a) ca = Some sps'
      -> exists hk, sllTarget rm cm a sps hk = inr sps'.
  
  Lemma sllTarget_add_preserves_cache_invar :
    forall rm cm ca sps a sps' hk,
      cache_stores_target_results rm cm ca
      -> sllTarget rm cm a sps hk = inr sps'
      -> cache_stores_target_results rm cm (Cache.add (sps, a) sps' ca).
  Proof.
    intros rm cm ca sps a sps' hk hc ht ka kb v hf.
    destruct (CacheKey_as_UOT.eq_dec (ka, kb) (sps, a)) as [he | hn].
    - inv he; rewrite CacheFacts.add_eq_o in hf; inv hf; eauto.
    - rewrite CacheFacts.add_neq_o in hf; auto.
  Qed.

  Lemma cache_lookup_preserves_pki :
    forall rm cm sps a ca sps',
      cache_stores_target_results rm cm ca
      -> Cache.find (sps, a) ca = Some sps'
      -> all_sll_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm cm sps a ca sps' hc hf.
    apply hc in hf.
    destruct hf as [hk ht].
    eapply sllTarget_preserves_pki; eauto.
  Qed.

  Definition sllFinalConfig (sp : sll_subparser) : bool :=
    match sp with
    | SllSp _ (SllFr None [], []) => true
    | _ => false
    end.

  Lemma sllFinalConfig_empty_stack :
    forall sp pred stk,
      sp = SllSp pred stk
      -> sllFinalConfig sp = true
      -> stk = (SllFr None [], []).
  Proof.
    intros sp pred stk ? hf; subst; unfold sllFinalConfig in hf; dms; tc.
  Qed.

  Definition sllHandleFinalSubparsers (sps : list sll_subparser) : prediction_result :=
    match filter sllFinalConfig sps with
    | []         => PredReject
    | sp :: sps' => 
      if allPredictionsEqual beqGamma sll_pred sp sps' then
        PredSucc sp.(sll_pred)
      else
        PredAmbig sp.(sll_pred)
    end.

  Lemma sllHandleFinalSubparsers_succ_facts :
    forall sps rhs,
      sllHandleFinalSubparsers sps = PredSucc rhs
      -> exists sp o,
        In sp sps
        /\ sp.(sll_pred) = rhs
        /\ sp.(sll_stk) = (SllFr o [], []).
  Proof.
    intros sps rhs hh.
    unfold sllHandleFinalSubparsers in hh.
    destruct (filter _ _) as [| sp sps'] eqn:hf; tc.
    destruct (allPredictionsEqual _ _ _ _); tc; inv hh.
    assert (hin : In sp (filter sllFinalConfig sps)).
    { rewrite hf; apply in_eq. }
    apply filter_In in hin.
    destruct hin as [hin ht]; subst.
    unfold sllFinalConfig in ht.
    destruct sp as [pred ([o suf], frs)]; dms; tc.
    repeat eexists; eauto.
  Qed.

  Lemma sllHandleFinalSubparsers_ambig_from_subparsers :
    forall sps gamma,
      sllHandleFinalSubparsers sps = PredAmbig gamma
      -> exists sp, In sp sps /\ sp.(sll_pred) = gamma.
  Proof.
    intros sps gamma hh.
    unfold sllHandleFinalSubparsers in hh.
    dmeqs h; tc; inv hh.
    eexists; split; eauto.
    eapply filter_cons_in; eauto.
  Qed.
  
  Fixpoint sllPredict' (rm  : rhs_map)
                       (cm  : closure_map)
                       (sps : list sll_subparser)
                       (ts  : list token)
                       (ca  : cache)
                       (hk  : all_sll_sp_pushes_from_keyset rm sps)
                       (hc  : cache_stores_target_results rm cm ca) :
                       prediction_result * cache :=
    match ts with
    | []            => (sllHandleFinalSubparsers sps, ca)
    | @existT _ _ a _ :: ts' =>
      match sps with
      | []          => (PredReject, ca)
      | sp' :: sps' =>
        if allPredictionsEqual beqGamma sll_pred sp' sps' then
          (PredSucc sp'.(sll_pred), ca)
        else
          match Cache.find (sps, a) ca as f
                return Cache.find (sps, a) ca = f -> _ with 
          | Some sps'' =>
            fun hf =>
               sllPredict' rm cm sps'' ts' ca
                          (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc
          | None =>
            fun _ =>
              match sllTarget rm cm a sps hk as t
                    return sllTarget rm cm a sps hk = t -> _ with
              | inl e     => fun _ => (PredError e, ca)
              | inr sps'' =>
                fun ht => 
                  let ca' := Cache.add (sps, a) sps'' ca
                  in  sllPredict' rm cm sps'' ts' ca'
                                  (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                                  (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
              end eq_refl
          end eq_refl
      end
    end.

  Lemma sllPredict'_cont_cases :
    forall rm cm sps a ts' ca hk hc fr tr pr
           (heq : Cache.find (sps, a) ca = fr)
           (heq' : sllTarget rm cm a sps hk = tr),
      match fr as f return Cache.find (sps, a) ca = f -> _ with 
      | Some sps'' =>
        fun hf =>
          sllPredict' rm cm sps'' ts' ca
                      (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc
      | None =>
        fun _ =>
          match tr as t return sllTarget rm cm a sps hk = t -> _ with
          | inl e     => fun _ => (PredError e, ca)
          | inr sps'' =>
            fun ht => 
              let ca' := Cache.add (sps, a) sps'' ca
              in  sllPredict' rm cm sps'' ts' ca'
                              (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht)
          end heq'
      end heq = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (PredSucc ys, ca'))
           \/ (exists sps'' (ht : sllTarget rm cm a sps hk = inr sps''),
                  sllPredict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (PredAmbig ys, ca'))
           \/ (exists sps'' (ht : sllTarget rm cm a sps hk = inr sps''),
                  sllPredict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (PredReject, ca'))
           \/ (exists sps'' (ht : sllTarget rm cm a sps hk = inr sps''),
                  sllPredict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredReject, ca'))
         | (PredError e, ca') =>
           (exists sps'' (hf : Cache.find (sps, a) ca = Some sps''),
               sllPredict' rm cm sps'' ts' ca
                           (cache_lookup_preserves_pki _ _ _ _ _ _ hc hf) hc = (PredError e, ca'))
           \/ sllTarget rm cm a sps hk = inl e
           \/ (exists sps'' (ht : sllTarget rm cm a sps hk = inr sps''),
                  sllPredict' rm cm sps'' ts' (Cache.add (sps, a) sps'' ca)
                              (sllTarget_preserves_pki _ _ _ _ _ _ ht hk)
                              (sllTarget_add_preserves_cache_invar _ _ _ _ _ _ _ hc ht) = (PredError e, ca'))
         end.
  Proof.
    intros rm cm sps a ts' ca hk hc fr tr pr heq heq';
      dms; intros heq''; inv heq''; eauto.
  Qed.

  Lemma sllPredict'_succ_preserves_cache_invar :
    forall rm cm ts sps ca hk hc ys ca',
      sllPredict' rm cm sps ts ca hk hc = (PredSucc ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros rm cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca hk hc ys ca' hs; sis.
    - dms; tc; inv hs; auto.
    - dm; tc; dm; try solve [inv hs; auto].
      apply sllPredict'_cont_cases in hs.
      destruct hs as [[sps'' [hf hs]] | [sps'' [ht hs]]]; eauto.
  Qed.

  Lemma sllPredict'_success_result_in_original_subparsers :
    forall rm cm ts sps ca hk hc ys ca',
      sllPredict' rm cm sps ts ca hk hc = (PredSucc ys, ca')
      -> exists sp, In sp sps /\ sp.(sll_pred) = ys.
  Proof.
    intros rm cm ts. 
    induction ts as [| (a,l) ts IH]; intros sps ca hk hc ys ca' hp; sis.
    - injection hp; intros _ hh. 
      apply sllHandleFinalSubparsers_succ_facts in hh.
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
  
  Definition sllInitSps (rm : rhs_map) (x : nonterminal) : list sll_subparser :=
    map (fun rhs => SllSp rhs (SllFr (Some x) rhs, []))
        (rhssFor x rm).

  Lemma sllInitSps_prediction_in_rhssFor :
    forall rm x sp,
      In sp (sllInitSps rm x)
      -> In sp.(sll_pred) (rhssFor x rm).
  Proof.
    intros rm x sp hi; unfold sllInitSps in hi.
    apply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  Lemma sllInitSps_pki :
    forall rm x,
      all_sll_sp_pushes_from_keyset rm (sllInitSps rm x).
  Proof.
    intros rm x sp hi.
    apply in_map_iff in hi; destruct hi as [? [heq hi]]; subst.
    repeat red; auto.
  Qed.

  Definition sllStartState (rm : rhs_map)
                           (cm : closure_map)
                           (x  : nonterminal) :
                           sum prediction_error (list sll_subparser) :=
    sllClosure rm cm (sllInitSps rm x) (sllInitSps_pki rm x).

  Lemma sllStartState_sp_prediction_in_rhssFor :
    forall rm cm x sp' sps',
      sllStartState rm cm x = inr sps'
      -> In sp' sps'
      -> In sp'.(sll_pred) (rhssFor x rm).
  Proof.
    intros rm cm x sp' sps' hs hi.
    unfold sllStartState in hs.
    eapply sllClosure_preserves_prediction in hs; eauto.
    destruct hs as [sp [hi' heq]]; rewrite heq.
    apply sllInitSps_prediction_in_rhssFor; auto.
  Qed.

  Lemma sllStartState_pki :
    forall rm cm x sps,
      sllStartState rm cm x = inr sps
      -> all_sll_sp_pushes_from_keyset rm sps.
  Proof.
    intros rm cm x sps hs sp hi.
    eapply sllClosure_preserves_pki; eauto.
    apply sllInitSps_pki.
  Qed.
  
  Definition sllPredict (rm : rhs_map)
                        (cm : closure_map)
                        (x  : nonterminal)
                        (ts : list token)
                        (ca : cache)
                        (hc : cache_stores_target_results rm cm ca) :
                        prediction_result * cache :=
    match sllStartState rm cm x as s return sllStartState rm cm x = s -> _ with
    | inl msg => fun _  => (PredError msg, ca)
    | inr sps => fun hs => sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc
    end eq_refl.

  Lemma sllPredict_cases' :
    forall rm cm x ts ca hc cr pr (heq : sllStartState rm cm x = cr),
      match cr as s return sllStartState rm cm x = s -> _ with
      | inl msg => fun _  => (PredError msg, ca)
      | inr sps => fun hs => sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc
      end heq = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredReject, ca'))
         | (PredError e, ca') =>
           sllStartState rm cm x = inl e
           \/ (exists sps (hs : sllStartState rm cm x = inr sps),
                  sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredError e, ca'))
         end.
  Proof.
    intros rm cm x ts ca hc cr pr heq; dms; intros heq'; inv heq'; eauto.
  Qed.

  Lemma sllPredict_cases :
    forall rm cm x ts ca hc pr,
      sllPredict rm cm x ts ca hc = pr
      -> match pr with
         | (PredSucc ys, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredSucc ys, ca'))
         | (PredAmbig ys, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredAmbig ys, ca'))
         | (PredReject, ca') =>
           (exists sps (hs : sllStartState rm cm x = inr sps),
               sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredReject, ca'))
         | (PredError e, ca') =>
           sllStartState rm cm x = inl e
           \/ (exists sps (hs : sllStartState rm cm x = inr sps),
                  sllPredict' rm cm sps ts ca (sllStartState_pki _ _ _ _ hs) hc = (PredError e, ca'))
         end.
  Proof.
    intros; eapply sllPredict_cases'; eauto.
  Qed.

  Lemma sllPredict_succ_in_rhssFor :
    forall rm cm x ts ca hc ys ca',
      sllPredict rm cm x ts ca hc = (PredSucc ys, ca')
      -> In ys (rhssFor x rm).
  Proof.
    intros rm cm x ts ca hc ys ca' hs.
    apply sllPredict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sllPredict'_success_result_in_original_subparsers in hp; eauto.
    destruct hp as [sp [hi heq]]; subst.
    eapply sllStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma sllPredict_succ_preserves_cache_invar :
    forall rm cm x ts ca hc ys ca',
      sllPredict rm cm x ts ca hc = (PredSucc ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros rm cm x ts ca hc ys ca' hs.
    apply sllPredict_cases in hs.
    destruct hs as [sps [hs hp]].
    eapply sllPredict'_succ_preserves_cache_invar; eauto.
  Qed.
      
  Definition adaptivePredict
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (cm  : closure_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (ts  : list token)
             (ca  : cache)
             (hc  : cache_stores_target_results rm cm ca)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) :
    prediction_result * cache :=
    let sll_res := sllPredict rm cm x ts ca hc
    in  match sll_res with
        | (PredAmbig _, _) => (llPredict g hw rm pre vs x suf frs ts hk, ca)
        | _                => sll_res
        end.
  
  Lemma adaptivePredict_succ_in_rhssFor :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptivePredict g hw rm cm pre vs x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> In ys (rhssFor x rm).
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs h; tc; inv ha.
    - eapply sllPredict_succ_in_rhssFor; eauto.
    - eapply llPredict_succ_in_rhssFor; eauto.
  Qed.
  
  Lemma adaptivePredict_succ_in_grammar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      rhs_map_correct rm g
      -> adaptivePredict g hw rm cm pre vs x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> PM.In (x, ys) g.
  Proof.
    intros.
    eapply rhssFor_in_iff; eauto.
    eapply adaptivePredict_succ_in_rhssFor; eauto.
  Qed.

  Lemma adaptivePredict_ambig_in_grammar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      rhs_map_correct rm g
      -> adaptivePredict g hw rm cm pre vs x suf frs ts ca hc hk = (PredAmbig ys, ca')
      -> PM.In (x, ys) g.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' hp ha.
    unfold adaptivePredict in ha; dms; tc; inv ha.
    eapply llPredict_ambig_in_grammar; eauto.
  Qed.

  Lemma adaptivePredict_succ_preserves_cache_invar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptivePredict g hw rm cm pre vs x suf frs ts ca hc hk = (PredSucc ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
    eapply sllPredict_succ_preserves_cache_invar; eauto.
  Qed.

  Lemma adaptivePredict_ambig_preserves_cache_invar :
    forall g hw rm cm pre vs x suf frs ts ca hc hk ys ca',
      adaptivePredict g hw rm cm pre vs x suf frs ts ca hc hk = (PredAmbig ys, ca')
      -> cache_stores_target_results rm cm ca'.
  Proof.
    intros g hw rm cm pre vs x suf frs ts ca hc hk ys ca' ha.
    unfold adaptivePredict in ha; dmeqs H; inv ha; auto.
  Qed.
  
End SllPredictionFn. 
