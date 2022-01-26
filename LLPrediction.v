Require Import Arith Bool FMaps List MSets Omega PeanoNat Program.Wf String.
Require Import CoStar.Defs.
Require Import CoStar.Lex.
Require Import CoStar.Tactics.
Require Import CoStar.Termination.
Require Import CoStar.Utils.
Import ListNotations.
Open Scope list_scope.

(* Key functions defined in this module:

   move
   LLclosure
   LLtarget
   LLpredict'
   initSps
   startState
   LLpredict
   
*)

Module LLPredictionFn (Import D : Defs.T).

  Module Export Term := TerminationFn D.

  (* Error values that the prediction mechanism can return *)
  Inductive prediction_error :=
  | SpInvalidState  : prediction_error
  | SpLeftRecursion : nonterminal -> prediction_error.

  Definition showPredictionError (e : prediction_error) : string :=
    match e with
    | SpInvalidState    => "SpInvalidState"
    | SpLeftRecursion x => "SpLeftRecursion " ++ showNT x
    end.
  
  (* "move" operation *)

  Inductive subparser_move_result {A : Type} : Type :=
  | MoveSucc   : A -> subparser_move_result 
  | MoveReject : subparser_move_result 
  | MoveError  : prediction_error -> subparser_move_result.

  Lemma inv_MoveSucc_eq :
    forall (sp sp' : subparser),
      MoveSucc sp = MoveSucc sp' -> sp = sp'.
  Proof.
    intros sp sp' heq; inv heq; auto.
  Qed.
  
  Definition moveSp (t  : token) (sp : subparser) : subparser_move_result :=
    match t with
    | @existT _ _ a' v' =>
      match sp with
      | Sp pred stk =>
        match stk with
        (* stack is exhausted *)
        | (Fr _ _ [], [])         => MoveReject
        (* impossible case *)
        | (Fr _ _ [], _ :: _)     => MoveError SpInvalidState
        (* impossible case *)
        | (Fr _ _ (NT _ :: _), _) => MoveError SpInvalidState
        (* try to consume a token *)
        | (Fr pre v (T a :: suf), frs) =>
          if t_eq_dec a' a then
            MoveSucc (Sp pred (Fr (T a' :: pre) (v', v) suf, frs))
          else
            MoveReject
        end
      end
    end.

  Lemma moveSp_preserves_prediction :
    forall t sp sp',
      moveSp t sp = MoveSucc sp'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros t sp sp' hm; unfold moveSp in hm.
    dms; tc; subst; inv hm; auto.
  Qed.

  Lemma moveSp_succ_step :
    forall sp sp' pre a v v' suf frs pred,
      sp = Sp pred (Fr pre v (T a :: suf), frs)
      -> sp' = Sp pred (Fr (T a :: pre) (v', v) suf, frs)
      -> moveSp (@existT _ _ a v') sp = MoveSucc sp'.
  Proof.
    intros; subst; unfold moveSp; dms; tc.
  Qed.
  
  Lemma moveSp_preserves_pki :
    forall rm a sp sp',
      sp_pushes_from_keyset rm sp
      -> moveSp a sp = MoveSucc sp'
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros rm a sp sp' hk hm.
    unfold moveSp in hm; dms; tc; inv hm; sis.
    red; red in hk; sis.
    eapply consume_preserves_keyset_invar; eauto.
  Qed.
  
  Definition move_result (A : Type) := sum prediction_error (list A).

  (* consider refactoring to short-circuit in case of error *)
  Fixpoint aggrMoveResults {A : Type} (rs : list (@subparser_move_result A)) : (move_result A) :=
    match rs with
    | []       => inr []
    | r :: rs' =>
      match (r, aggrMoveResults rs') with
      | (MoveError e, _)       => inl e
      | (_, inl e)             => inl e
      | (MoveSucc sp, inr sps) => inr (sp :: sps)
      | (MoveReject, inr sps)  => inr sps
      end
    end.

  Lemma aggrMoveResults_succ_in_input :
    forall (A   : Type)
           (rs  : list (@subparser_move_result A))
           (sp  : A)
           (sps : list A),
      aggrMoveResults rs = inr sps
      -> In sp sps
      -> In (MoveSucc sp) rs.
  Proof.
    intros A rs sp.
    induction rs as [| r rs' IH]; intros sps ha hi; sis.
    - inv ha; inv hi.
    - destruct r as [sp' | | e];
        destruct (aggrMoveResults rs') as [e' | sps']; tc; inv ha.
      + inv hi; firstorder.
      + firstorder.
  Qed.

  Lemma aggrMoveResults_error_in_input :
    forall (A : Type)
           (smrs : list (@subparser_move_result A))
           (e    : prediction_error),
      aggrMoveResults smrs = inl e
      -> In (MoveError e) smrs.
  Proof.
    intros A smrs e ha.
    induction smrs as [| smr smrs' IH]; sis; tc.
    destruct smr as [sp' | | e'];
      destruct (aggrMoveResults smrs') as [e'' | sps']; tc; inv ha; eauto.
  Qed.

  Lemma aggrMoveResults_map_backwards :
    forall A (f : A -> subparser_move_result) (sp' : A) sps sps',
      aggrMoveResults (map f sps) = inr sps'
      -> In sp' sps'
      -> exists sp,
          In sp sps
          /\ f sp = MoveSucc sp'.
  Proof.
    intros A f sp' sps; induction sps as [| sp sps IH]; intros sps' ha hi.
    - inv ha; inv hi.
    - simpl in ha.
      dmeq hf; tc.
      + dmeq ha'; tc.
        inv ha.
        destruct hi as [hh | ht]; subst.
        * eexists; split; [apply in_eq | auto].
        * apply IH in ht; auto.
          destruct ht as [sp'' [hi heq]].
          eexists; split; [apply in_cons; eauto | auto].
      + dmeq ha'; tc.
        inv ha.
        apply IH in hi; auto.
        destruct hi as [sp'' [hi heq]].
        eexists; split; [apply in_cons; eauto | auto].
  Qed.
  
  Definition move (t : token) (sps : list subparser) : (move_result subparser) :=
    aggrMoveResults (map (moveSp t) sps).

  Lemma move_unfold :
    forall t sps,
      move t sps = aggrMoveResults (map (moveSp t) sps).
  Proof. 
    auto. 
  Qed.

  Lemma move_preserves_prediction :
    forall t sp' sps sps',
      move t sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
  Proof.
    intros t sp' sps sps' hm hi.
    unfold move in hm.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    eapply in_map_iff in hm; destruct hm as [sp [hmsp hi']].
    eexists; split; eauto.
    eapply moveSp_preserves_prediction; eauto.
  Qed.

  Lemma aggrMoveResults_succ_all_sps_step :
    forall t sp sps sp' sps',
      In sp sps
      -> moveSp t sp = MoveSucc sp'
      -> aggrMoveResults (map (moveSp t) sps) = inr sps'
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

  Lemma move_maps_moveSp :
    forall t sp sp' sps sps',
      In sp sps
      -> moveSp t sp = MoveSucc sp'
      -> move t sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros t sp sp' sps sps' hi hm hm'.
    eapply aggrMoveResults_succ_all_sps_step; eauto.
  Qed.

  Lemma move_succ_all_sps_step :
    forall sp sp' pred pre v a suf v' frs sps sps',
      sp = Sp pred (Fr pre v (T a :: suf), frs)
      -> sp' = Sp pred (Fr (T a :: pre) (v', v) suf, frs)
      -> In sp sps
      -> move (@existT _ _ a v') sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros; subst.
    eapply move_maps_moveSp; eauto.
    eapply moveSp_succ_step; eauto.
  Qed.

  Lemma move_preserves_pki :
    forall rm a sps sps',
      all_sp_pushes_from_keyset rm sps
      -> move a sps = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros rm a sps sps' hk hm sp' hi'.
    eapply aggrMoveResults_map_backwards in hm; eauto.
    destruct hm as [sp [hi hm]].
    eapply moveSp_preserves_pki; eauto.
  Qed.

  (* "closure" operation *)

  Inductive subparser_closure_step_result {A : Type} :=
  | CstepDone   : subparser_closure_step_result
  | CstepK      : NtSet.t -> list A -> subparser_closure_step_result
  | CstepError  : prediction_error -> subparser_closure_step_result.

  Definition cstep
             (gr : grammar)
             (hw : grammar_wf gr)
             (rm : rhs_map)
             (vi : NtSet.t)
             (sp : subparser) : 
    subparser_closure_step_result :=
    match sp with
    | Sp pred (fr, frs) =>
      match fr with
      (* return case *)
      | Fr pre vs [] =>
        match frs with
        (* stack is exhausted *)
        | [] => CstepDone
        (* return to caller frame *)
        | Fr pre_cr vs_cr (NT x :: suf_cr) :: frs' =>
          let pre' := rev pre in
          let vs'  := revTuple pre vs in
          match findPredicateAndAction (x, pre') gr hw with
          (* check semantic predicate and reduce *)
          | Some (p, f) =>
            if p vs' then
              let stk' := (Fr (NT x :: pre_cr) (f vs', vs_cr) suf_cr, frs')
              in  CstepK (NtSet.remove x vi) [Sp pred stk']
            else
              (* failed semantic predicate *)
              CstepK NtSet.empty []
          | None =>
            (* impossible case *)
            CstepError SpInvalidState
          end
        | _ => CstepError SpInvalidState
        end
      (* consume case *)
      | Fr _ _ (T _ :: _) => CstepDone
      (* push case *)
      | Fr pre v (NT x :: suf) =>
        if NtSet.mem x vi then
          (* unreachable for a left-recursive grammar *)
          match NM.find x rm with
          | Some _ => CstepError (SpLeftRecursion x)
          | None   => CstepK NtSet.empty []
          end
        else
          let sps' := map (fun rhs => Sp pred (Fr [] tt rhs, fr :: frs))
                          (rhssFor x rm)
          in  CstepK (NtSet.add x vi) sps' 
      end
    end.
  
  Lemma cstep_preserves_prediction :
    forall g hw rm sp sp' sps' vi vi',
      cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g hw rm sp sp' sps' vi vi' hs hi.
    unfold cstep in hs; dms; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; auto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; auto.
  Qed.

  Lemma cstep_preserves_pki :
    forall g hw rm sp sp' sps' vi vi',
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> sp_pushes_from_keyset rm sp'.
  Proof.
    intros g hw rm sp sp' sps' vi vi' hk hs hi; red in hk.
    unfold cstep in hs; dms; tc; inv hs; red; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      red; red in hk; sis.
      eapply return_preserves_keyset_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      red; red in hk; sis.
      eapply push_preserves_keyset_invar; eauto.
      eapply rhssFor_keySet; eauto.
  Qed.

  Definition closure_result (A : Type) := sum prediction_error (list A).

  (* consider refactoring to short-circuit in case of error *)
  Fixpoint aggrClosureResults {A B} (crs : list (sum A (list B))) : sum A (list B) :=
    match crs with
    | [] => inr []
    | cr :: crs' =>
      match (cr, aggrClosureResults crs') with
      | (inl e, _)          => inl e
      | (inr _, inl e)      => inl e
      | (inr sps, inr sps') => inr (sps ++ sps')
      end
    end.

  Lemma aggrClosureResults_succ_in_input:
    forall (A : Type)
           (crs : list (closure_result A)) 
           (sp  : A)
           (sps : list A),
      aggrClosureResults crs = inr sps 
      -> In sp sps 
      -> exists sps',
          In (inr sps') crs
          /\ In sp sps'.
  Proof.
    intros A crs; induction crs as [| cr crs IH]; intros sp sps ha hi; simpl in ha.
    - inv ha; inv hi.
    - destruct cr as [e | sps'];
        destruct (aggrClosureResults crs) as [e' | sps'']; tc; inv ha.
      apply in_app_or in hi.
      destruct hi as [hi' | hi''].
      + eexists; split; eauto.
        apply in_eq.
      + apply IH in hi''; auto.
        destruct hi'' as [sps [hi hi']].
        eexists; split; eauto.
        apply in_cons; auto.
  Qed.

  Lemma aggrClosureResults_error_in_input:
    forall (A : Type)
           (crs : list (closure_result A)) 
           (e   : prediction_error),
      aggrClosureResults crs = inl e
      -> In (inl e) crs.
  Proof.
    intros A crs e ha; induction crs as [| cr crs IH]; sis; tc.
    destruct cr as [e' | sps].
    - inv ha; auto.
    - destruct (aggrClosureResults crs) as [e' | sps']; tc; auto.
  Qed.

  Lemma aggrClosureResults_map_succ_elt_succ :
    forall A (sp : A) (f : A -> closure_result A) (sps : list A) sps'',
      In sp sps
      -> aggrClosureResults (map f sps) = inr sps''
      -> exists sps',
          f sp = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros A sp f sps; induction sps as [| hd tl IH]; intros sps'' hi ha.
    - inv hi.
    - destruct hi as [hh | ht]; subst; sis.
      + dms; tc; inv ha; eexists; split; eauto.
        intros; apply in_or_app; auto.
      + destruct (f hd)                 as [? | sps ]; tc.
        destruct (aggrClosureResults _) as [? | sps']; tc; inv ha.
        apply IH with (sps'' := sps') in ht; auto.
        destruct ht as [sp' [heq hall]]; eexists; split; eauto.
        intros; apply in_or_app; auto.
  Qed.

  Lemma aggrClosureResults_map_backwards :
    forall A sp'' (f : A -> closure_result A) (sps sps'' : list A),
      aggrClosureResults (map f sps) = inr sps''
      -> In sp'' sps''
      -> exists sp sps',
          In sp sps
          /\ f sp = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros A sp'' f sps; induction sps as [| sp sps IH]; intros sps'' ha hi.
    - sis; inv ha; inv hi.
    - simpl in ha.
      destruct (f sp) as [? | hd_sps] eqn:hf; tc.
      destruct (aggrClosureResults _) as [? | tl_sps] eqn:ha'; tc.
      inv ha.
      apply in_app_or in hi; destruct hi as [hhd | htl].
      + exists sp; exists hd_sps; repeat split; auto.
        apply in_eq.
      + apply IH in htl; auto.
        destruct htl as [sp' [sps' [? [? ?]]]]; subst.
        exists sp'; exists sps'; repeat split; auto.
        apply in_cons; auto.
  Qed.

  Lemma aggrClosureResults_dmap_succ_elt_succ :
    forall A sp (sps : list A) (f : forall sp, In sp sps -> closure_result A) sps'',
      In sp sps
      -> aggrClosureResults (dmap sps f) = inr sps''
      -> exists hi sps',
          f sp hi = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros A sp sps; induction sps as [| hd tl IH]; intros f sps'' hi ha.
    - inv hi.
    - destruct hi as [hh | ht]; subst.
      + simpl in ha.
        dmeq hsp; tc.
        dmeq hag; tc.
        inv ha.
        repeat eexists; eauto.
        intros sp' hi; apply in_or_app; auto.
      + simpl in ha.
        dmeq hsp; tc.
        dmeq hag; tc.
        inv ha.
        unfold eq_rect_r in hag; simpl in hag.
        apply IH in hag; auto.
        destruct hag as [hi [sps' [heq hall]]].
        repeat eexists; eauto.
        intros sp' hi'.
        apply in_or_app; auto.
  Qed.

  Lemma aggrClosureResults_dmap_backwards :
    forall A (sp'' : A) (sps : list A) f (sps'' : list A),
      @aggrClosureResults prediction_error _ (dmap sps f) = inr sps''
      -> In sp'' sps''
      -> exists sp hi sps',
          In sp sps
          /\ f sp hi = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros A sp'' sps f; induction sps as [| sp sps IH]; intros sps'' ha hi.
    - inv ha; inv hi.
    - simpl in ha.
      dmeq hf; tc.
      dmeq ha'; tc.
      inv ha.
      apply in_app_or in hi.
      destruct hi as [hh | ht].
      + repeat eexists; eauto.
        apply in_eq.
      + apply IH in ha'; auto.
        destruct ha' as [sp' [hi [sps' [hi' [heq hi'']]]]].
        unfold eq_rect_r in heq; simpl in heq.
        repeat eexists; eauto.
        apply in_cons; auto.
  Qed.

  Definition ll_meas (rm : rhs_map) (vi : NtSet.t) (sp : subparser) : nat * nat :=
    match sp with
    | Sp _ sk => meas rm vi (stackSuffixes sk)
    end.

  Lemma cstep_meas_lt :
    forall (g      : grammar)
           (hw     : grammar_wf g)
           (rm     : rhs_map)
           (sp sp' : subparser)
           (sps'   : list subparser)
           (vi vi' : NtSet.t),
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> lex_nat_pair (ll_meas rm vi' sp') (ll_meas rm vi sp).
  Proof.
    intros g hw rm sp sp' sps' vi vi' ha hs hi. 
    unfold cstep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; sis; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      eapply meas_lt_after_push; sis; eauto.
      + apply not_mem_iff; auto.
      + eapply rhssFor_keySet; eauto.
      + eapply rhssFor_allRhss; eauto. 
  Defined.

  Lemma acc_after_step :
    forall g hw rm sp sp' sps' vi vi',
      sp_pushes_from_keyset rm sp
      -> cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (ll_meas rm vi sp)
      -> Acc lex_nat_pair (ll_meas rm vi' sp').
  Proof.
    intros g hw rm sp sp' sps' vi vi' hk heq hi ha.
    eapply Acc_inv; eauto.
    eapply cstep_meas_lt; eauto.
  Defined.

  Fixpoint llc
           (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (ha : Acc lex_nat_pair (ll_meas rm vi sp)) : closure_result subparser :=
    match cstep g hw rm vi sp as r return cstep g hw rm vi sp = r -> _ with
    | CstepDone       => fun _  => inr [sp]
    | CstepError e    => fun _  => inl e
    | CstepK vi' sps' => 
      fun hs => 
        let crs := dmap sps' (fun sp' hi =>
                                llc g hw rm vi' sp'
                                    (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                    (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
        in  aggrClosureResults crs
    end eq_refl.

  Lemma llc_unfold :
    forall g hw rm vi sp hk ha,
      llc g hw rm vi sp hk ha =
      match cstep g hw rm vi sp as r return cstep g hw rm vi sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK vi' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hi =>
                           llc g hw rm vi' sp'
                               (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                               (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          in  aggrClosureResults crs
      end eq_refl.
  Proof.
    intros g hw rm vi sp hk ha; destruct ha; auto.
  Qed.

  Lemma llc_cases' :
    forall (g   : grammar)
           (hw  : grammar_wf g)
           (rm  : rhs_map)
           (vi  : NtSet.t)
           (sp  : subparser)
           (hk  : sp_pushes_from_keyset rm sp)
           (ha  : Acc lex_nat_pair (ll_meas rm vi sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result subparser)
           (heq : cstep g hw rm vi sp = sr),
      match sr as r return cstep g hw rm vi sp = r -> closure_result subparser with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK vi' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hi => llc g hw rm vi' sp'
                                            (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                            (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          in  aggrClosureResults crs
      end heq = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep g hw rm vi sp = CstepK vi' sps)
                     (crs : list (closure_result subparser)),
               crs = dmap sps (fun sp' hi => 
                                 llc g hw rm vi' sp'
                                     (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                     (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggrClosureResults crs = inl e
         | inr sps => 
           (sr = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (vi'  : NtSet.t)
                     (hs   : cstep g hw rm vi sp = CstepK vi' sps')
                     (crs  : list (closure_result subparser)),
               crs = dmap sps' (fun sp' hi => 
                                  llc g hw rm vi' sp'
                                      (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                      (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggrClosureResults crs = inr sps
         end.
  Proof.
    intros g hw rm vi sp hk ha sr cr heq.
    destruct sr as [| sps | e];
    destruct cr as [e' | sps']; intros heq'; tc;
    try solve [inv heq'; eauto | eauto 8].
  Qed.

  Lemma llc_cases :
    forall (g  : grammar)
           (hw : grammar_wf g)
           (rm : rhs_map)
           (vi : NtSet.t)
           (sp : subparser)
           (hk : sp_pushes_from_keyset rm sp)
           (ha : Acc lex_nat_pair (ll_meas rm vi sp))
           (cr : closure_result subparser),
      llc g hw rm vi sp hk ha = cr
      -> match cr with
         | inl e => 
           cstep g hw rm vi sp = CstepError e
           \/ exists (sps : list subparser)
                     (vi' : NtSet.t)
                     (hs  : cstep g hw rm vi sp = CstepK vi' sps)
                     (crs : list (closure_result subparser)),
               crs = dmap sps (fun sp' hi => 
                                 llc g hw rm vi' sp'
                                     (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                     (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           (cstep g hw rm vi sp = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (vi'  : NtSet.t)
                     (hs   : cstep g hw rm vi sp = CstepK vi' sps')
                     (crs  : list (closure_result subparser)),
               crs = dmap sps' (fun sp' hi => 
                                  llc g hw rm vi' sp'
                                      (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                      (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
               /\ aggrClosureResults crs = inr sps
         end.
  Proof.
    intros g hw rm vi sp hk ha cr hs; subst.
    rewrite llc_unfold.
    eapply llc_cases'; eauto.
  Qed.

  Lemma llc_success_cases :
    forall g hw rm vi sp hk ha sps,
      llc g hw rm vi sp hk ha = inr sps
      -> (cstep g hw rm vi sp = CstepDone /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (vi'  : NtSet.t)
                   (hs   : cstep g hw rm vi sp = CstepK vi' sps')
                   (crs  : list (closure_result subparser)),
          crs = dmap sps' (fun sp' hi => 
                             llc g hw rm vi' sp'
                                 (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                 (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          /\ aggrClosureResults crs = inr sps.
  Proof.
    intros g hw rm vi sp hk ha sps hs; apply llc_cases with (cr := inr sps); auto.
  Qed.

  Lemma llc_error_cases :
    forall g hw rm vi sp hk ha e,
      llc g hw rm vi sp hk ha = inl e
      -> cstep g hw rm vi sp = CstepError e
         \/ exists (sps : list subparser)
                   (vi' : NtSet.t)
                   (hs  : cstep g hw rm vi sp = CstepK vi' sps)
                   (crs : list (closure_result subparser)),
          crs = dmap sps (fun sp' hi => 
                            llc g hw rm vi' sp'
                                (cstep_preserves_pki _ _ _ _ _ _ _ _ hk hs hi)
                                (acc_after_step _ _ _ _ _ _ _ _ hk hs hi ha))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros g hw rm vi sp hk ha e hs; apply llc_cases with (cr := inl e); auto.
  Qed.

  Lemma llc_preserves_prediction' :
    forall g hw rm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sp' sps',
      pair = ll_meas rm vi sp
      -> llc g hw rm vi sp hk ha' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros g hw rm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sp' sps' heq hs hi; subst.
    pose proof hs as hs'; apply llc_success_cases in hs.
    destruct hs as [[hs heq] | [sps'' [av' [hs [crs [heq heq']]]]]]; subst.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      + apply cstep_preserves_prediction with (sp' := sp'') in hs; auto.
        rewrite hs; auto.
      + eapply cstep_meas_lt; eauto.
  Qed.

  Lemma llc_preserves_prediction :
    forall g hw rm vi sp sp' sps' hk ha,
      llc g hw rm vi sp hk ha = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply llc_preserves_prediction'; eauto.
  Qed.

  Lemma llc_preserves_pki' :
    forall g hw rm pair (ha : Acc lex_nat_pair pair) vi sp hk ha' sps',
      pair = ll_meas rm vi sp
      -> llc g hw rm vi sp hk ha' = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm pair a.
    induction a as [pair hlt IH].
    intros vi sp hk ha' sps'' heq hc; subst.
    pose proof hc as hc'; apply llc_success_cases in hc.
    destruct hc as [[hc heq] | [sps' [vi' [hc [crs [heq heq']]]]]]; subst; intros sp''' hi.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in heq'; eauto.
      destruct heq' as [sps [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi''' [_ heq]]].
      eapply IH in heq; subst; eauto.
      eapply cstep_meas_lt; eauto.
  Qed.

  Lemma llc_preserves_pki :
    forall g hw rm vi sp hk ha sps sps',
      all_sp_pushes_from_keyset rm sps
      -> llc g hw rm vi sp hk ha = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros; eapply llc_preserves_pki'; eauto.
  Qed.
  
  Definition llClosure
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (sps : list subparser)
             (hk  : all_sp_pushes_from_keyset rm sps) :
    sum prediction_error (list subparser) :=
    aggrClosureResults (dmap sps (fun sp hi =>
                                    llc g hw rm NtSet.empty sp
                                        (pki_list__pki_mem _ _ sp hk hi)
                                        (lex_nat_pair_wf _))).

  Lemma llClosure_preserves_prediction :
    forall g hw rm sps (hk : all_sp_pushes_from_keyset rm sps) sps' sp',
      llClosure g hw rm sps hk = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
  Proof.
    intros g hw rm sps hk sps' sp' hl hi.
    eapply aggrClosureResults_succ_in_input in hl; eauto.
    destruct hl as [sps'' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eexists; split; eauto.
    eapply llc_preserves_prediction; eauto.
  Qed.

  Lemma llClosure_preserves_pki :
    forall g hw rm sps sps' (hk : all_sp_pushes_from_keyset rm sps),
      llClosure g hw rm sps hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'. 
  Proof.
    intros g hw rm sps spss' hk hc sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps' [hi' hi'']].
    eapply dmap_in with (l := sps) in hi'; eauto; sis.
    destruct hi' as [sp [? [hi''' hspc]]].
    eapply llc_preserves_pki; eauto.
  Qed.
    
  Definition llTarget g hw rm a sps
                      (hk : all_sp_pushes_from_keyset rm sps) :
                      sum prediction_error (list subparser) :=
    match move a sps as m return move a sps = m -> _ with
    | inl e    => fun _ => inl e
    | inr sps' =>
      fun hm =>
        match llClosure g hw rm sps' (move_preserves_pki _ _ _ _ hk hm) with
        | inl e     => inl e
        | inr sps'' => inr sps''
        end
    end eq_refl.

  Lemma llTarget_cases' :
    forall g hw rm a sps mr hk (heq : move a sps = mr) cr,
      match mr as mr' return move a sps = mr' -> move_result subparser with
      | inl e    => fun _ => inl e
      | inr sps' =>
        fun hm =>
          match llClosure g hw rm sps' (move_preserves_pki _ _ _ _ hk hm) with
          | inl e     => inl e
          | inr sps'' => inr sps''
          end
      end heq = cr
      -> match cr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ llClosure g hw rm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', move a sps = inr sps' /\ llClosure g hw rm sps' hk' = inr sps''
         end.
  Proof.
    intros g hw rm a sps mr hk heq cr.
    destruct mr as [e' | sps']; destruct cr as [e'' | sps'']; intros heq'; tc.
    - inv heq'; auto.
    - destruct (llClosure _ _ _) eqn:hc; inv heq'; eauto.
    - destruct (llClosure _ _ _) eqn:hc; inv heq'; eauto.
  Qed.

  Lemma llTarget_cases :
    forall g hw rm a sps hk cr,
      llTarget g hw rm a sps hk = cr
      -> match cr with
         | inl e =>
           move a sps = inl e
           \/ (exists sps' hk',
                  move a sps = inr sps' /\ llClosure g hw rm sps' hk' = inl e) 
         | inr sps'' =>
           exists sps' hk', move a sps = inr sps' /\ llClosure g hw rm sps' hk' = inr sps''
         end.
  Proof.
    intros; eapply llTarget_cases'; eauto.
  Qed.

  Lemma llTarget_destruct :
    forall g hw rm a sps hk,
      (exists e, llTarget g hw rm a sps hk = inl e)
      \/ (exists sps', llTarget g hw rm a sps hk = inr sps').
  Proof.
    intros g hw rm a sps hk.
    remember (llTarget g hw rm a sps hk) as tr eqn:heq.
    destruct tr; eauto.
  Qed.    
  
  Lemma llTarget_succ_case :
    forall g hw rm a sps hk sps'',
      llTarget g hw rm a sps hk = inr sps''
      -> (exists sps' hk',
             move a sps = inr sps'
             /\ llClosure g hw rm sps' hk' = inr sps'').
  Proof.
    intros g hw rm a sps hk sps'' ht; apply llTarget_cases in ht; auto.
  Qed.

  Lemma llTarget_preserves_pki :
    forall g hw rm a sps sps' hk,
      llTarget g hw rm a sps hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm a sps sps'' hk ht.
    apply llTarget_succ_case in ht.
    destruct ht as [sps' [hk' [hmhc]]].
    eapply llClosure_preserves_pki; eauto.
  Qed.

  (* LL prediction *)

  Inductive prediction_result :=
  | PredSucc   : list symbol      -> prediction_result
  | PredAmbig  : list symbol      -> prediction_result
  | PredReject :                     prediction_result
  | PredError  : prediction_error -> prediction_result.

  Definition finalConfig (sp : subparser) : bool :=
    match sp with
    | Sp _ (Fr _ _ [], []) => true
    | _ => false
    end.

  Lemma finalConfig_empty_stack :
    forall sp pred stk,
      sp = Sp pred stk
      -> finalConfig sp = true
      -> exists pre v, stk = (Fr pre v [], []).
  Proof.
    intros sp pred stk ? hf; subst; unfold finalConfig in hf; dms; tc; eauto.
  Qed.

  Definition allPredictionsEqual {A B} (beq : B -> B -> bool) (f : A -> B) (x : A) (xs : list A) : bool :=
    allEqual _ beq (f x) (map f xs). 

  Lemma allPredictionsEqual_inv_cons :
    forall A B beq (f : A -> B) sp' sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> allPredictionsEqual beq f sp' (sp :: sps) = true
      -> f sp' = f sp
         /\ allPredictionsEqual beq f sp' sps = true.
  Proof.
    unfold allPredictionsEqual; intros.
    apply allEqual_inv_cons; auto.
  Qed.

  Lemma allPredictionsEqual_in_tl :
    forall A B beq (f : A -> B) sp sp' sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> allPredictionsEqual beq f sp sps = true
      -> In sp' sps
      -> f sp' = f sp. 
  Proof.
    unfold allPredictionsEqual; intros.
    eapply allEqual_in_tl; eauto.
    apply in_map_iff; eauto.
  Qed.

  Lemma allPredictionsEqual_false_exists_diff_rhs :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> allPredictionsEqual beq f sp sps = false
      -> exists sp',
        In sp' sps
        /\ f sp' <> f sp. 
  Proof.
    unfold allPredictionsEqual; intros A B beq f sp sps hd ha. 
    apply allEqual_false_exists_diff_rhs in ha; auto.
    destruct ha as [ys [hi hn]].
    apply in_map_iff in hi.
    destruct hi as [sp' [heq hi]]; subst; eauto.
  Qed.

  (* propositional spec for allPredictionsEqual *)
  Definition all_predictions_equal {A B : Type} (f : A -> B) sp sps :=
    forall sp', In sp' sps -> f sp' = f sp.

  Lemma ape_tail :
    forall A B (f : A -> B) sp sp' sps,
      all_predictions_equal f sp (sp' :: sps)
      -> all_predictions_equal f sp sps.
  Proof.
    firstorder.
  Qed.

  Lemma ape_cons_head_eq :
    forall A B (f : A -> B) sp sps,
      all_predictions_equal f sp sps
      -> all_predictions_equal f sp (sp :: sps).
  Proof.
    intros A B f sp sps ha sp' hi; firstorder; subst; auto.
  Qed.
  
  Lemma allPredictionsEqual_prop :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> allPredictionsEqual beq f sp sps = true
      -> all_predictions_equal f sp sps.
  Proof.
    intros A B beq f sp sps hd ha sp' hi. 
    unfold allPredictionsEqual, allEqual in ha.
    eapply forallb_forall with (x := f sp') in ha; eauto.
    - firstorder. 
    - apply in_map_iff; eauto.
  Qed.

  Lemma ape_false__allPredictionsEqual_false :
    forall A B beq (f : A -> B) sp sps,
      (forall (x x' : B), beq x x' = true <-> x = x')
      -> ~ all_predictions_equal f sp sps
      -> allPredictionsEqual beq f sp sps = false.
  Proof.
    intros A B beq f sp sps hd hn; unfold not in hn.
    destruct (allPredictionsEqual _ _ sp sps) eqn:ha; auto.
    exfalso; apply hn; eapply allPredictionsEqual_prop; auto.
  Qed.

  Lemma all_predictions_equal_filter :
    forall A B sp sps sps' f (f' : A -> B),
      all_predictions_equal f' sp sps
      -> filter f sps = sps'
      -> all_predictions_equal f' sp sps'.
  Proof.
    intros A B sp sps sps' f f' ha hf sp' hi; subst.
    apply filter_In in hi; firstorder.
  Qed.

  Lemma llTarget_preserves_ape:
    forall g hw rm a x sps sps' (hk : all_sp_pushes_from_keyset rm sps),
    all_predictions_equal prediction x sps
    -> llTarget g hw rm a sps hk = inr sps'
    -> all_predictions_equal prediction x sps'.
  Proof.
    intros g hw rm a x sps sps'' hk ha hl sp'' hi''.
    red in ha.
    (* lemma about llTarget preserving prediction *)
    apply llTarget_succ_case in hl.
    destruct hl as [sps' [hk' [hm hc]]].
    eapply llClosure_preserves_prediction in hc; eauto.
    destruct hc as [sp' [hi' heq']]; rewrite heq'.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [sp [hi heq]]; rewrite heq; firstorder.
  Qed.
      
  Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
    match filter finalConfig sps with
    | []         => PredReject
    | sp :: sps' => 
      if allPredictionsEqual beqGamma prediction sp sps' then
        PredSucc sp.(prediction)
      else
        PredAmbig sp.(prediction)
    end.

  Lemma handleFinalSubparsers_succ_facts :
    forall sps rhs,
      handleFinalSubparsers sps = PredSucc rhs
      -> exists sp pre v,
        In sp sps
        /\ sp.(prediction) = rhs
        /\ sp.(stack) = (Fr pre v [], []).
  Proof.
    intros sps rhs hh.
    unfold handleFinalSubparsers in hh.
    destruct (filter _ _) as [| sp sps'] eqn:hf; tc.
    destruct (allPredictionsEqual _ _); tc; inv hh.
    assert (hin : In sp (filter finalConfig sps)).
    { rewrite hf; apply in_eq. }
    apply filter_In in hin.
    destruct hin as [hin ht]; subst.
    unfold finalConfig in ht.
    destruct sp as [pred ([o suf], frs)]; dms; tc.
    repeat eexists; eauto.
  Qed.

  Lemma handleFinalSubparsers_ambig_from_subparsers :
    forall sps gamma,
      handleFinalSubparsers sps = PredAmbig gamma
      -> exists sp, In sp sps /\ sp.(prediction) = gamma.
  Proof.
    intros sps gamma hh.
    unfold handleFinalSubparsers in hh.
    dmeqs h; tc; inv hh.
    eexists; split; eauto.
    eapply filter_cons_in; eauto.
  Qed.

  Fixpoint llPredict'
           (g   : grammar)
           (hw  : grammar_wf g)
           (rm  : rhs_map)
           (sps : list subparser)
           (ts  : list token)
           (hk  : all_sp_pushes_from_keyset rm sps) : prediction_result :=
    match ts with
    | []            => handleFinalSubparsers sps
    | t :: ts' =>
      match sps with
      | []          => PredReject
      | sp' :: sps' =>
        if allPredictionsEqual beqGamma prediction sp' sps' then
          PredSucc sp'.(prediction)
        else
          match llTarget g hw rm t sps hk as t' return llTarget g hw rm t sps hk = t' -> _ with
          | inl e     => fun _ => PredError e
          | inr sps'' =>
            fun ht =>
              llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk ht)
          end eq_refl
      end
    end.

  Lemma llPredict'_cont_cases :
    forall g hw rm a sps hk ts' pr t (heq : llTarget g hw rm a sps hk = t),
      match t as t' return llTarget g hw rm a sps hk = t' -> _ with
      | inl e     => fun _ => PredError e
      | inr sps'' =>
        fun ht =>
          llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk ht)
      end heq = pr
      -> match pr with
         | PredSucc ys =>
           (exists sps'' (heq' : llTarget g hw rm a sps hk = inr sps''),
               llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk heq') = PredSucc ys)
         | PredAmbig ys =>
           (exists sps'' (heq' : llTarget g hw rm a sps hk = inr sps''),
               llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk heq') = PredAmbig ys)
         | PredReject =>
           (exists sps'' (heq' : llTarget g hw rm a sps hk = inr sps''),
               llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk heq') = PredReject)         
         | PredError e =>
           llTarget g hw rm a sps hk = inl e
           \/ (exists sps'' (heq' : llTarget g hw rm a sps hk = inr sps''),
               llPredict' g hw rm sps'' ts' (llTarget_preserves_pki _ _ _ _ _ _ hk heq') = PredError e)
         end.
  Proof.
    intros g hw rm a sps hk ts' pr t heq; dms; intros heq'; inv heq'; eauto.
  Qed.

  Lemma llPredict'_success_result_in_original_subparsers :
    forall g hw rm ts gamma sps hk ,
      llPredict' g hw rm sps ts hk = PredSucc gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g hw rm ts gamma.
    induction ts as [| (a, l) ts IH]; intros sps hk hl; sis.
    - apply handleFinalSubparsers_succ_facts in hl.
      destruct hl as [sp [pre [v [hi [heq heq']]]]]; eauto.
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall; subst.
      + inv hl; exists sp'; split; auto.
        apply in_eq.
      + apply llPredict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        pose proof ht as ht'.
        apply llTarget_succ_case in ht'.
        destruct ht' as [sps''' [hk' [hm hc]]].
        apply IH in hl; destruct hl as [? [hi heq]]; subst.
        eapply llClosure_preserves_prediction in hc; eauto.
        destruct hc as [? [? heq]]; rewrite heq.
        eapply move_preserves_prediction in hm; eauto.
        destruct hm as [? [? ?]]; eauto.
  Qed.

  Lemma llPredict'_ambig_result_in_original_subparsers :
    forall g hw rm ts gamma sps hk,
      llPredict' g hw rm sps ts hk  = PredAmbig gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g hw rm ts gamma.
    induction ts as [| (a, l) ts IH]; intros sps hk hl; sis.
    - apply handleFinalSubparsers_ambig_from_subparsers in hl; auto. 
    - destruct sps as [| sp' sps'] eqn:hs; tc; dmeq hall; subst.
      + inv hl.
      + apply llPredict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        pose proof ht as ht'.
        apply llTarget_succ_case in ht'.
        destruct ht' as [sps''' [hk' [hm hc]]].
        apply IH in hl; destruct hl as [? [hi heq]]; subst.
        eapply llClosure_preserves_prediction in hc; eauto.
        destruct hc as [? [? heq]]; rewrite heq.
        eapply move_preserves_prediction in hm; eauto.
        destruct hm as [? [? ?]]; eauto.
  Qed.

  (* to do : this lemma is an example of why some invariants
     aren't required when it's assumed that llPredict' succeeds.
    There might be other places where I can remove these 
    hypotheses. *)
  Lemma llPredict'_succ__eq_all_predictions_equal :
    forall g hw rm sp ys ts sps hk,
(*      no_left_recursion g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps *)
      all_predictions_equal prediction sp sps
      -> llPredict' g hw rm sps ts hk = PredSucc ys
      -> ys = prediction sp.
  Proof.
    intros g hw rm sp ys ts; induction ts as [| (a, l) ts IH];
      intros sps hk ha hl; sis.
    - unfold handleFinalSubparsers in hl.
      destruct (filter _ _) as [| sp' sps'] eqn:hf; tc.
      dm; tc; inv hl.
      eapply all_predictions_equal_filter in hf; eauto.
      red in hf; firstorder.
    - destruct sps as [| sp' sps']; tc.
      destruct (allPredictionsEqual _ _ sp' sps').
      + inv hl; apply ha; apply in_eq.
      + apply llPredict'_cont_cases in hl.
        destruct hl as [sps'' [ht hl]].
        apply IH in hl; auto.
        eapply llTarget_preserves_ape; eauto.
  Qed.

  Lemma all_predictions_equal__llPredict'_neq_ambig :
    forall g hw rm sp ys ts sps hk,
      all_predictions_equal prediction sp sps
      -> llPredict' g hw rm sps ts hk <> PredAmbig ys.
  Proof.
    intros g hw rm sp ys ts; induction ts as [| (a, l) ts IH]; intros sps hk ha hl; sis.
    - (* lemma *)
      unfold handleFinalSubparsers in hl.
      destruct (filter _ _) as [| sp' sps'] eqn:hf; tc.
      destruct (allPredictionsEqual _ _) eqn:ha'; tc; inv hl.
      apply allPredictionsEqual_false_exists_diff_rhs in ha'.
      destruct ha' as [sp'' [hi hneq]].
      apply hneq. apply eq_trans with (y := prediction sp).
      + apply ha.
        eapply filter_In; rewrite hf; apply in_cons; auto.
      + symmetry; apply ha.
        eapply filter_In; rewrite hf; apply in_eq.
      + apply beqGamma_eq_iff.
    - destruct sps as [| sp' sps']; tc.
      destruct (allPredictionsEqual _ _); tc.
      apply llPredict'_cont_cases in hl.
      destruct hl as [sps'' [ht hl]].
      apply IH in hl; auto.
      eapply llTarget_preserves_ape; eauto.
  Qed. 

  Definition llInitSps
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame) : list subparser :=
    let cr := Fr pre vs (NT x :: suf)
    in  map (fun rhs => Sp rhs (Fr [] tt rhs, cr :: frs))
            (rhssFor x rm).

  Lemma llInitSps_prediction_in_rhssFor :
    forall rm pre vs x suf frs sp,
      In sp (llInitSps rm pre vs x suf frs)
      -> In sp.(prediction) (rhssFor x rm).
  Proof.
    intros rm pre vs x suf frs sp hi; unfold llInitSps in hi.
    eapply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  Lemma llInitSps_result_incl_all_rhss :
    forall g rm pre vs x suf rhs frs,
      rhs_map_correct rm g
      -> PM.In (x, rhs) g
      -> In (Sp rhs (Fr [] tt rhs, Fr pre vs (NT x :: suf) :: frs)) 
            (llInitSps rm pre vs x suf frs).
  Proof.
    intros g rm pre vs x suf rhs frs hc hi.
    apply in_map_iff; exists rhs; split; auto.
    eapply rhssFor_in_iff; eauto.
  Qed.

  Lemma llInitSps_preserves_pki :
    forall rm pre vs x suf frs,
      stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)
      -> all_sp_pushes_from_keyset rm (llInitSps rm pre vs x suf frs).
  Proof.
    intros rm pre vs x suf frs hk sp hi.
    unfold llInitSps in hi.
    apply in_map_iff in hi. 
    destruct hi as [ys [heq hi]]; subst.
    red in hk; sis.
    eapply push_preserves_keyset_invar; eauto.
    eapply rhssFor_keySet; eauto.
  Qed.
    
  Definition llStartState
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) :
    sum prediction_error (list subparser) :=
    llClosure g hw rm (llInitSps rm pre vs x suf frs) (llInitSps_preserves_pki _ _ _ _ _ _ hk).
  
  Lemma llStartState_sp_prediction_in_rhssFor :
    forall g hw rm pre vs x suf frs hk sp' sps',
      llStartState g hw rm pre vs x suf frs hk = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhssFor x rm).
  Proof.
    intros g hw rm pre vs x suf frs hk sp' sps' hf hi. 
    unfold llStartState in hf.
    eapply llClosure_preserves_prediction in hf; eauto.
    destruct hf as [sp [hin heq]]; rewrite heq.
    eapply llInitSps_prediction_in_rhssFor; eauto.
  Qed.

  Lemma llStartState_preserves_pki :
    forall g hw rm pre vs x suf frs hk sps',
      llStartState g hw rm  pre vs x suf frs hk = inr sps'
      -> all_sp_pushes_from_keyset rm sps'.
  Proof.
    intros g hw rm pre vs x suf frs hk sps' hl. 
    eapply llClosure_preserves_pki; eauto.
  Qed.
  
  Definition llPredict
             (g   : grammar)
             (hw  : grammar_wf g)
             (rm  : rhs_map)
             (pre : list symbol)
             (vs  : symbols_semty pre)
             (x   : nonterminal)
             (suf : list symbol)
             (frs : list parser_frame)
             (ts  : list token)
             (hk  : stack_pushes_from_keyset rm (Fr pre vs (NT x :: suf), frs)) : prediction_result :=
    match llStartState g hw rm pre vs x suf frs hk as s return llStartState g hw rm pre vs x suf frs hk = s -> _ with
    | inl msg => fun _   => PredError msg
    | inr sps => fun heq => llPredict' g hw rm sps ts
                                       (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq)
    end eq_refl.

  Lemma llPredict_cases' :
    forall g hw rm pre vs x suf frs ts hk cr (heq : llStartState g hw rm pre vs x suf frs hk = cr) pr,
      match cr as s return llStartState g hw rm pre vs x suf frs hk = s -> _ with
      | inl msg => fun _   => PredError msg
      | inr sps => fun heq => llPredict' g hw rm sps ts
                                         (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq)
      end heq = pr
      -> match pr with
         | PredSucc ys =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredSucc ys)
         | PredAmbig ys =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredAmbig ys)
         | PredReject =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk= inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredReject)
         | PredError e =>
           llStartState g hw rm pre vs x suf frs hk = inl e
           \/ (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
                  llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredError e)
         end.
  Proof.
    intros g hw rm pre vs x suf frs ts hk cr heq pr. 
    dms; intros heq'; inv heq'; eauto.
  Qed.

  Lemma llPredict_cases :
    forall g hw rm pre vs x suf frs ts hk pr,
      llPredict g hw rm pre vs x suf frs ts hk = pr
      -> match pr with
         | PredSucc ys =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredSucc ys)
         | PredAmbig ys =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredAmbig ys)
         | PredReject =>
           (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
               llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredReject)
         | PredError e =>
           llStartState g hw rm pre vs x suf frs hk = inl e
           \/ (exists sps (heq : llStartState g hw rm pre vs x suf frs hk = inr sps),
                  llPredict' g hw rm sps ts (llStartState_preserves_pki _ _ _ _ _ _ _ _ _ _ heq) = PredError e)
         end.
  Proof.
    intros; eapply llPredict_cases'; eauto.
  Qed.

  Lemma llPredict_succ_in_rhssFor :
    forall g hw rm pre vs x suf frs ts hk gamma,
      llPredict g hw rm pre vs x suf frs ts hk = PredSucc gamma
      -> In gamma (rhssFor x rm).
  Proof.
    intros g hw rm pre vs x suf frs ts hk gamma hp.
    apply llPredict_cases in hp.
    destruct hp as [sps [heq hp]].
    apply llPredict'_success_result_in_original_subparsers in hp.
    destruct hp as [sp [hin heq']]; subst.
    eapply llStartState_sp_prediction_in_rhssFor; eauto.
  Qed.
  
  Lemma llPredict_ambig_in_rhssFor :
    forall g hw rm pre vs x suf frs ts hk gamma,
      llPredict g hw rm pre vs x suf frs ts hk = PredAmbig gamma
      -> In gamma (rhssFor x rm).
  Proof.
    intros g hw rm pre vs x suf frs ts hk gamma hp.
    apply llPredict_cases in hp.
    destruct hp as [sps [heq hp]].
    apply llPredict'_ambig_result_in_original_subparsers in hp.
    destruct hp as [sp [hin heq']]; subst.
    eapply llStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma llPredict_succ_in_grammar :
    forall g hw rm pre vs x suf frs ts hk ys,
      rhs_map_correct rm g
      -> llPredict g hw rm pre vs x suf frs ts hk = PredSucc ys
      -> PM.In (x, ys) g.
  Proof.
    intros; eapply rhssFor_in_iff; eauto.
    eapply llPredict_succ_in_rhssFor; eauto.
  Qed.

  Lemma llPredict_ambig_in_grammar :
    forall g hw rm pre vs x suf frs ts hk ys,
      rhs_map_correct rm g
      -> llPredict g hw rm pre vs x suf frs ts hk = PredAmbig ys
      -> PM.In (x, ys) g.
  Proof.
    intros; eapply rhssFor_in_iff; eauto.
    eapply llPredict_ambig_in_rhssFor; eauto.
  Qed.

  (* A WELL-FORMEDNESS PREDICATE OVER A SUFFIX STACK *)

  (* The stack predicate is defined in terms of the following
   predicate over a list of locations *)

  Inductive frames_wf (g : grammar) : list parser_frame -> Prop :=
  | WF_empty :
      frames_wf g []
  | WF_bottom_init :
      forall (x : nonterminal),
        frames_wf g [Fr [] tt [NT x]]
  | WF_bottom_final :
      forall (x : nonterminal) (v : nt_semty x),
        frames_wf g [Fr [NT x] (v, tt) []]
  | WF_upper :
      forall x pre pre' vs vs' suf suf' frs,
        PM.In (x, rev pre' ++ suf') g
        -> frames_wf g (                    Fr pre vs (NT x :: suf) :: frs)
        -> frames_wf g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs).

  Hint Constructors frames_wf : core.

  (* invert a frames_wf judgment *)
  Ltac inv_fwf hw  hi hw' :=
    inversion hw as [ | ? | ? ? | ? ? ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac wf_upper_nil := eapply WF_upper with (pre' := []); sis; eauto.

  Lemma return_preserves_frames_wf_invar :
    forall g frs x pre pre' vs vs' suf (f : symbols_semty (rev pre') -> nt_semty x),
      frames_wf g (Fr pre' vs' [] :: Fr pre vs (NT x :: suf) :: frs)
      -> frames_wf g (Fr (NT x :: pre) (f (revTuple _ vs'), vs) suf :: frs).
  Proof.
    intros g frs x pre pre' vs vs' suf f hw; sis.
    inv_fwf hw hi hw'; rew_anr.
    inv_fwf hw' hi' hw''.
    - destruct vs; auto.
    - rewrite app_cons_group_l in hi'; auto.
  Qed.

  Lemma push_preserves_frames_wf_invar :
    forall g pre vs x suf frs rhs, 
      PM.In (x, rhs) g
      -> frames_wf g (Fr pre vs (NT x :: suf) :: frs)
      -> frames_wf g (Fr [] tt rhs :: Fr pre vs (NT x :: suf) :: frs).
  Proof.
    intros g pre vs x suf frs rhs hi hw.
    constructor; auto.
  Qed.

  Lemma consume_preserves_frames_wf_invar :
    forall g pre vs a suf vs' frs,
      frames_wf g (Fr pre vs (T a :: suf) :: frs)
      -> frames_wf g (Fr (T a :: pre) vs' suf :: frs).
  Proof.
    intros g pre vs a suf vs' frs hw; sis.
    inv_fwf hw hi hw'.
    rewrite app_cons_group_l in hi; auto.
  Qed.

  (* The parser stack well-formedness predicate *)
  Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_wf g (fr :: frs)
    end.

  (* Lift the predicate to a list of subparsers *)
  Definition all_stacks_wf (g : grammar) (sps: list subparser) : Prop :=
    forall sp, In sp sps -> stack_wf g sp.(stack).

(*
  Definition frame_wf (g : grammar) (fr : parser_frame) :=
    match fr with
    | Fr x pre vs suf => PM.In (x, rev pre ++ suf) g
    end.
  
  Definition frames_wf (g : grammar) (frs : list parser_frame): Prop :=
    Forall (fun fr =>
              match fr with
              | Fr x pre vs suf => PM.In (x, rev pre ++ suf) g
              end) frs.
 *)

  (* The stack well-formedness predicate *)
(*  Definition stack_wf (g : grammar) (stk : parser_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_wf g (reconstr (fr :: frs))
    end.

  (* Lift the predicate to a list of subparsers *)
  Definition all_stacks_wf (g : grammar) (sps: list subparser) : Prop :=
    forall sp, In sp sps -> stack_wf g sp.(stack).
 *)

  Lemma cstep_preserves_stack_wf_invar :
    forall g hw rm sp sp' sps' vi vi',
      rhs_map_correct rm g
      -> stack_wf g sp.(stack)
      -> cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> stack_wf g sp'.(stack).
  Proof.
    intros g hw rm sp sp' sps' vi vi' hc hw' hs hi.
    unfold cstep in hs; dms; tc; sis; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_frames_wf_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_frames_wf_invar; auto.
      eapply rhssFor_in_iff; eauto.
  Qed.

  Lemma llInitSps_preserves_stack_wf_invar :
    forall g rm fr pre vs x suf frs,
      rhs_map_correct rm g
      -> fr = Fr pre vs (NT x :: suf)
      -> stack_wf g (fr, frs)
      -> all_stacks_wf g (llInitSps rm pre vs x suf frs).
  Proof.
    intros g rm fr pre vs x suf frs hc ? hw sp hi; subst; unfold llInitSps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [? hi]]; subst; sis.
    apply push_preserves_frames_wf_invar; eauto.
    eapply rhssFor_in_iff; eauto.
  Qed.    

  (* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

  (* Auxiliary definition *)
    Inductive frames_repr_nullable_path (g : grammar) : list parser_frame -> Prop :=
  | FR_direct :
      forall x pre pre' vs vs' suf suf',
        PM.In (x, rev pre' ++ suf') g
        -> nullable_gamma g (rev pre')
        -> frames_repr_nullable_path g [Fr pre' vs' suf' ; Fr pre vs (NT x :: suf)]
  | FR_indirect :
      forall x pre pre' vs vs' suf suf' frs,
        PM.In (x, rev pre' ++ suf') g
        -> nullable_gamma g (rev pre')
        -> frames_repr_nullable_path g (                    Fr pre vs (NT x :: suf) :: frs)
        -> frames_repr_nullable_path g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs).

  Hint Constructors frames_repr_nullable_path : core.

  Ltac inv_frnp hf hi hn hf' :=
    inversion hf as [? ? ? ? ? ? ? hi hn | ? ? ? ? ? ? ? ? hi hn hf']; subst; clear hf.

  Lemma frnp_inv_two_head_frames :
    forall g fr fr' fr'' frs,
      frames_repr_nullable_path g (fr'' :: fr' :: frs ++ [fr])
      -> frames_repr_nullable_path g (fr' :: frs ++ [fr]).
  Proof.
    intros g fr fr'' fr''' frs hf.
    destruct frs as [| fr' frs]; sis; inv hf; auto.
  Qed.

  Lemma frnp_second_frame_nt_head :
    forall g fr fr' frs,
      frames_repr_nullable_path g (fr' :: fr :: frs)
      -> exists pre vs x suf,
        fr = Fr pre vs (NT x :: suf).
  Proof.
    intros g fr fr' frs hf; inv hf; eauto.
  Qed.

  Lemma frnp_shift_head_frame :
    forall g pre vs suf suf' vs' frs,
      nullable_gamma g suf
      -> frames_repr_nullable_path g (Fr pre vs (suf ++ suf') :: frs)
      -> frames_repr_nullable_path g (Fr (rev suf ++ pre) vs' suf' :: frs).
  Proof.
    intros g pre vs suf suf' vs' frs hn hf; destruct frs as [| fr frs]; inv_frnp hf hi hn' hf'.
    - rewrite app_assoc in hi; constructor.
      + rewrite rev_app_distr.
        rewrite rev_involutive; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive.
        apply nullable_app; auto.
    - rewrite app_assoc in hi; constructor; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive; auto.
      + rewrite rev_app_distr.
        rewrite rev_involutive.
        apply nullable_app; auto.
  Qed.

  Lemma frnp_grammar_nullable_path :
    forall g frs fr fr_cr x y pre pre' vs vs' suf suf',
      fr       = Fr pre' vs' (NT y :: suf')
      -> fr_cr = Fr pre vs (NT x :: suf)
      -> frames_repr_nullable_path g (fr :: frs ++ [fr_cr])
      -> nullable_path g (NT x) (NT y).
  Proof.
    intros g frs.
    induction frs as [| fr' frs IH];
      intros fr fr_cr x y pre pre' vs vs' suf suf' ? ? hf; subst; sis.
    - inv_frnp hf hi hn hf'.
      + eapply DirectPath; eauto.
      + inv hf'.
    - pose proof hf as hf'; apply frnp_second_frame_nt_head in hf'.
      destruct hf' as [pre'' [vs'' [y'' [suf'' ?]]]]; subst. 
      apply nullable_path_trans with (y := NT y'').
      + apply frnp_inv_two_head_frames in hf; eauto.
      + inv_frnp hf hi hn hf'; eauto.
  Qed.
      
  Lemma frnp_caller_nt_nullable :
    forall g x pre pre' vs vs' suf suf' frs,
      frames_repr_nullable_path g (Fr pre' vs' suf' :: Fr pre vs (NT x :: suf) :: frs)
      -> nullable_gamma g suf'
      -> nullable_sym g (NT x).
  Proof.
    intros g x pre pre' vs vs' suf suf' frs hf hng. 
    inv_frnp hf hi hn hf'.
    - econstructor; eauto.
      apply nullable_app; auto.
    - econstructor; eauto.
      apply nullable_app; auto.
  Qed.

  (* The invariant itself *)
  Definition unavailable_nts_are_open_calls g vi stk : Prop :=
    match stk with
    | (fr, frs) =>
      forall (x : nonterminal),
        NtSet.In x (allNts g)
        -> NtSet.In x vi
        -> exists frs_pre fr_cr frs_suf pre vs suf,
            frs = frs_pre ++ fr_cr :: frs_suf
            /\ fr_cr = Fr pre vs (NT x :: suf)
            /\ frames_repr_nullable_path g (fr :: frs_pre ++ [fr_cr])
    end.

  (* Lift the invariant to a subparser *)
  Definition unavailable_nts_invar g vi sp :=
    match sp with
    | Sp _ stk => unavailable_nts_are_open_calls g vi stk
    end.

  (* Lift the invariant to a list of subparsers *)
  Definition sps_unavailable_nts_invar g vi sps : Prop :=
    forall sp, In sp sps -> unavailable_nts_invar g vi sp.

  Lemma return_preserves_unavailable_nts_invar :
    forall g vi pr fr cr cr' x pre pre' vs vs' vs'' suf frs,
      fr     = Fr pre' vs' []
      -> cr  = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) vs'' suf
      -> unavailable_nts_invar g vi (Sp pr (fr, cr :: frs))
      -> unavailable_nts_invar g (NtSet.remove x vi) (Sp pr (cr', frs)). 
  Proof.
    intros g vi pr fr cr cr' x' pre pre' vs vs' vs'' suf frs ? ? ? hu; subst. 
    intros x hi hn.
    assert (hn' : NtSet.In x vi) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & heq & ? & hf); subst; sis.
    destruct frs_pre as [| fr' frs_pre]; inv heq.
    - ND.fsetdec. 
    - pose proof hf as hf'.
      apply frnp_inv_two_head_frames in hf.
      eapply frnp_shift_head_frame with (suf := [NT x']) in hf; eauto 9.
      constructor; auto.
      apply frnp_caller_nt_nullable in hf'; auto.
  Qed.

  Lemma push_preserves_unavailable_nts_invar :
    forall g cr ce vi pr pre vs x suf rhs frs,
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> PM.In (x, rhs) g
      -> unavailable_nts_invar g vi (Sp pr (cr, frs))
      -> unavailable_nts_invar g (NtSet.add x vi) (Sp pr (ce, cr :: frs)).
  Proof.
    intros g cr ce vi pr pre vs x' suf rhs frs ? ? hi hu; subst. 
    intros x hi' hn.
    destruct (NF.eq_dec x' x); subst.
    - exists []; repeat eexists; eauto; sis.
      eapply FR_direct with (pre' := []); sis; auto.
    - assert (hn' : NtSet.In x vi) by ND.fsetdec.
      apply hu in hn'; simpl in hn'; clear hu; auto.
      destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & ? & hf); subst; sis.
      exists (Fr pre vs (NT x' :: suf) :: frs_pre); repeat eexists; sis; eauto.
  Qed.

  Lemma cstep_preserves_unavailable_nts_invar :
    forall g hw rm sp sp' sps' vi vi',
      rhs_map_correct rm g
      -> unavailable_nts_invar g vi sp
      -> cstep g hw rm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> unavailable_nts_invar g vi' sp'.
  Proof.
    intros g hw rm sp sp' sps' vi vi' hc hu hs hi.
    unfold cstep in hs; dmeqs h; inv hs; tc; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply return_preserves_unavailable_nts_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply push_preserves_unavailable_nts_invar; eauto.
      eapply rhssFor_in_iff; eauto.
  Qed.

  Lemma unavailable_nts_empty :
    forall g pred stk,
      unavailable_nts_invar g NtSet.empty (Sp pred stk).
  Proof.
    intros g pred (fr, frs); repeat red; intros; ND.fsetdec.
  Qed.
  
End LLPredictionFn.
