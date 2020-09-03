Require Import Arith Bool FMaps List MSets Omega PeanoNat Program.Wf String.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

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

  Record subparser := Sp { prediction : list symbol
                         ; stack      : suffix_stack }.

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

  Inductive subparser_move_result :=
  | MoveSucc   : subparser -> subparser_move_result
  | MoveReject : subparser_move_result
  | MoveError  : prediction_error -> subparser_move_result.

  Definition moveSp (a : terminal) (sp : subparser) : subparser_move_result :=
    match sp with
    | Sp pred stk =>
      match stk with
      | (SF _ [], [])            => MoveReject
      | (SF _ [], _ :: _)        => MoveError SpInvalidState
      | (SF _ (NT _ :: _), _)    => MoveError SpInvalidState
      | (SF o (T a' :: suf), frs) =>
        if t_eq_dec a' a then
          MoveSucc (Sp pred (SF o suf, frs))
        else
          MoveReject
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
    forall sp sp' pred o a suf frs,
      sp = Sp pred (SF o (T a :: suf), frs)
      -> sp' = Sp pred (SF o suf, frs)
      -> moveSp a sp = MoveSucc sp'.
  Proof.
    intros; subst; unfold moveSp; dms; tc.
  Qed.

  Definition move_result := sum prediction_error (list subparser).

  (* consider refactoring to short-circuit in case of error *)
  Fixpoint aggrMoveResults (rs : list subparser_move_result) : move_result :=
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
    forall (rs  : list subparser_move_result)
           (sp  : subparser)
           (sps : list subparser),
      aggrMoveResults rs = inr sps
      -> In sp sps
      -> In (MoveSucc sp) rs.
  Proof.
    intros rs sp.
    induction rs as [| r rs' IH]; intros sps ha hi; sis.
    - inv ha; inv hi.
    - destruct r as [sp' | | e];
        destruct (aggrMoveResults rs') as [e' | sps']; tc; inv ha.
      + inv hi; firstorder.
      + firstorder.
  Qed.

  Lemma aggrMoveResults_error_in_input :
    forall (smrs : list subparser_move_result)
           (e    : prediction_error),
      aggrMoveResults smrs = inl e
      -> In (MoveError e) smrs.
  Proof.
    intros smrs e ha.
    induction smrs as [| smr smrs' IH]; sis; tc.
    destruct smr as [sp' | | e'];
      destruct (aggrMoveResults smrs') as [e'' | sps']; tc; inv ha; eauto.
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

  Lemma aggrMoveResults_map_backwards :
    forall (f : subparser -> subparser_move_result) sp' sps sps',
      aggrMoveResults (map f sps) = inr sps'
      -> In sp' sps'
      -> exists sp,
          In sp sps
          /\ f sp = MoveSucc sp'.
  Proof.
    intros f sp' sps; induction sps as [| sp sps IH]; intros sps' ha hi.
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

  Definition move (a : terminal) (sps : list subparser) : move_result :=
    aggrMoveResults (map (moveSp a) sps).

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
    forall sp sp' pred o a suf frs sps sps',
      sp = Sp pred (SF o (T a :: suf), frs)
      -> sp' = Sp pred (SF o suf, frs)
      -> In sp sps
      -> move a sps = inr sps'
      -> In sp' sps'.
  Proof.
    intros sp sp' pred o a suf frs sps sps' ? ? hi hm; subst.
    eapply move_maps_moveSp; eauto.
    eapply moveSp_succ_step; eauto.
  Qed.

  (* "closure" operation *)

  Inductive subparser_closure_step_result :=
  | CstepDone  : subparser_closure_step_result
  | CstepK     : NtSet.t -> list subparser -> subparser_closure_step_result
  | CstepError : prediction_error -> subparser_closure_step_result.

  (* to do : it might be possible to get rid of the g arg *)
  Definition cstep (g : grammar) (pm : production_map) (av : NtSet.t) (sp : subparser) : 
    subparser_closure_step_result :=
    match sp with
    | Sp pred (fr, frs) =>
      match fr with
      | SF o [] =>
        match frs with
        | []                   => CstepDone
        | SF _ [] :: _         => CstepError SpInvalidState
        | SF _ (T _ :: _) :: _ => CstepError SpInvalidState
        | SF o_cr (NT x :: suf_cr) :: frs_tl =>
          let stk':= (SF o_cr suf_cr, frs_tl) 
          in  CstepK (NtSet.add x av) [Sp pred stk'] 
        end
      | SF _ (T _ :: _)    => CstepDone
      | SF _ (NT x :: suf) =>
        if NtSet.mem x av then
          let sps' := map (fun rhs => Sp pred 
                                         (SF (Some x) rhs, fr :: frs))
                          (rhssFor x pm)
          in  CstepK (NtSet.remove x av) sps' 
        else if NtSet.mem x (allNts g) then
               CstepError (SpLeftRecursion x)
             else
               CstepK NtSet.empty [] 
      end
    end.
  
  Lemma cstep_preserves_prediction :
    forall g pm sp sp' sps' av av',
      cstep g pm av sp = CstepK av' sps'
      -> In sp' sps'
      -> sp.(prediction) = sp'.(prediction).
  Proof.
    intros g pm sp sp' sps' av av' hs hi.
    unfold cstep in hs; dms; tc; inv hs.
    - apply in_singleton_eq in hi; subst; auto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst; auto.
    - inv hi.
  Qed.

  Definition closure_result := sum prediction_error (list subparser).

  (* consider refactoring to short-circuit in case of error *)
  Fixpoint aggrClosureResults (crs : list closure_result) : closure_result :=
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
    forall (crs : list closure_result) 
           (sp  : subparser)
           (sps : list subparser),
      aggrClosureResults crs = inr sps 
      -> In sp sps 
      -> exists sps',
          In (inr sps') crs
          /\ In sp sps'.
  Proof.
    intros crs; induction crs as [| cr crs IH]; intros sp sps ha hi; simpl in ha.
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
    forall (crs : list closure_result) 
           (e   : prediction_error),
      aggrClosureResults crs = inl e
      -> In (inl e) crs.
  Proof.
    intros crs e ha; induction crs as [| cr crs IH]; sis; tc.
    destruct cr as [e' | sps].
    - inv ha; auto.
    - destruct (aggrClosureResults crs) as [e' | sps']; tc; auto.
  Qed.

  Lemma aggrClosureResults_map_succ_elt_succ :
    forall sp (f : subparser -> closure_result) (sps : list subparser) sps'',
      In sp sps
      -> aggrClosureResults (map f sps) = inr sps''
      -> exists sps',
          f sp = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros sp f sps; induction sps as [| hd tl IH]; intros sps'' hi ha.
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
    forall sp'' (f : subparser -> closure_result) (sps sps'' : list subparser),
      aggrClosureResults (map f sps) = inr sps''
      -> In sp'' sps''
      -> exists sp sps',
          In sp sps
          /\ f sp = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros sp'' f sps; induction sps as [| sp sps IH]; intros sps'' ha hi.
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
    forall sp (sps : list subparser) (f : forall sp, In sp sps -> closure_result) sps'',
      In sp sps
      -> aggrClosureResults (dmap sps f) = inr sps''
      -> exists hi sps',
          f sp hi = inr sps'
          /\ forall sp', In sp' sps' -> In sp' sps''.
  Proof.
    intros sp sps; induction sps as [| hd tl IH]; intros f sps'' hi ha.
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
    forall sp'' (sps : list subparser) f sps'',
      aggrClosureResults (dmap sps f) = inr sps''
      -> In sp'' sps''
      -> exists sp hi sps',
          In sp sps
          /\ f sp hi = inr sps'
          /\ In sp'' sps'.
  Proof.
    intros sp'' sps f; induction sps as [| sp sps IH]; intros sps'' ha hi.
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

  Definition meas (g : grammar) (av : NtSet.t) (sp : subparser) : nat * nat :=
    match sp with
    | Sp _ stk =>
      let m := maxRhsLength g in
      let e := NtSet.cardinal av               
      in  (stackScore stk (1 + m) e, stackHeight stk)
    end.

  Lemma meas_lt_after_return :
    forall g sp sp' av av' pred o o' suf' x frs,
      sp = Sp pred (SF o [], SF o' (NT x :: suf') :: frs)
      -> sp' = Sp pred (SF o' suf', frs)
      -> av' = NtSet.add x av
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g sp sp' av av' pred o o' suf' x frs ? ? ?; subst.
    pose proof (stackScore_le_after_return' suf' o o' x) as hle.
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq]; sis.
    - apply pair_fst_lt; eauto.
    - rewrite heq; apply pair_snd_lt; auto.
  Defined.

  Lemma meas_lt_after_push :
    forall g sp sp' fr fr' av av' pred o o' suf x rhs frs,
      sp     = Sp pred (fr, frs)
      -> sp' = Sp pred (fr', fr :: frs)
      -> fr  = SF o (NT x :: suf)
      -> fr' = SF o' rhs
      -> av' = NtSet.remove x av
      -> NtSet.In x av
      -> In (x, rhs) g
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g sp sp' fr fr' av av' pred o o' suf x rhs frs ? ? ? ? ? hi hi'; subst.
    apply pair_fst_lt.
    eapply stackScore_lt_after_push; sis; eauto.
  Defined.

  Lemma cstep_meas_lt :
    forall (g      : grammar)
           (pm     : production_map)
           (sp sp' : subparser)
           (sps'   : list subparser)
           (av av' : NtSet.t),
      production_map_correct pm g
      -> cstep g pm av sp = CstepK av' sps'
      -> In sp' sps'
      -> lex_nat_pair (meas g av' sp') (meas g av sp).
  Proof.
    intros g pm sp sp' sps' av av' hc hs hi. 
    unfold cstep in hs; dmeqs h; tc; inv hs; try solve [inv hi].
    - apply in_singleton_eq in hi; subst.
      eapply meas_lt_after_return; eauto.
    - apply in_map_iff in hi.
      destruct hi as [rhs [heq hi]]; subst.
      eapply meas_lt_after_push; eauto.
      + apply NF.mem_iff; auto.
      + eapply rhssFor_in_iff; eauto. 
  Defined.

  Lemma acc_after_step :
    forall g pm sp sp' sps' av av',
      production_map_correct pm g
      -> cstep g pm av sp = CstepK av' sps'
      -> In sp' sps'
      -> Acc lex_nat_pair (meas g av sp)
      -> Acc lex_nat_pair (meas g av' sp').
  Proof.
    intros g pm sp sp' sps' av av' hc heq hi ha.
    eapply Acc_inv; eauto.
    eapply cstep_meas_lt; eauto.
  Defined.

  Fixpoint llc (g  : grammar)
               (pm : production_map)
               (hc : production_map_correct pm g)
               (av : NtSet.t)
               (sp : subparser)
               (a  : Acc lex_nat_pair (meas g av sp)) : closure_result :=
    match cstep g pm av sp as r return cstep g pm av sp = r -> _ with
    | CstepDone       => fun _  => inr [sp]
    | CstepError e    => fun _  => inl e
    | CstepK av' sps' => 
      fun hs => 
        let crs := dmap sps' (fun sp' hin =>
                                llc hc av' sp'
                                    (acc_after_step _ _ _ hc hs hin a))
        in  aggrClosureResults crs
    end eq_refl.

  Lemma llc_unfold :
    forall g pm hc sp av a,
      llc hc av sp a =
      match cstep g pm av sp as r return cstep g pm av sp = r -> _ with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hin =>
                           llc hc av' sp' (acc_after_step _ _ _ hc hs hin a))
          in  aggrClosureResults crs
      end eq_refl.
  Proof.
    intros g pm hc sp av a; destruct a; auto.
  Qed.

  Lemma llc_cases' :
    forall (g   : grammar)
           (pm  : production_map)
           (hc  : production_map_correct pm g)
           (sp  : subparser)
           (av  : NtSet.t)
           (a   : Acc lex_nat_pair (meas g av sp))
           (sr  : subparser_closure_step_result)
           (cr  : closure_result)
           (heq : cstep g pm av sp = sr),
      match sr as r return cstep g pm av sp = r -> closure_result with
      | CstepDone       => fun _  => inr [sp]
      | CstepError e    => fun _  => inl e
      | CstepK av' sps' => 
        fun hs => 
          let crs := 
              dmap sps' (fun sp' hin => llc hc av' sp' (acc_after_step _ _ _ hc hs hin a))
          in  aggrClosureResults crs
      end heq = cr
      -> match cr with
         | inl e => 
           sr = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : cstep g pm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps => 
           (sr = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (av'  : NtSet.t)
                     (hs   : cstep g pm av sp = CstepK av' sps')
                     (crs  : list closure_result),
               crs = dmap sps' (fun sp' hi => 
                                  llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inr sps
         end.
  Proof.
    intros g pm hc sp av a sr cr heq.
    destruct sr as [| sps | e];
    destruct cr as [e' | sps']; intros heq'; tc;
    try solve [inv heq'; eauto | eauto 8].
  Qed.

  Lemma llc_cases :
    forall (g  : grammar)
           (pm : production_map)
           (hc : production_map_correct pm g)
           (sp : subparser)
           (av : NtSet.t)
           (a  : Acc lex_nat_pair (meas g av sp))
           (cr : closure_result),
      llc hc av sp a = cr
      -> match cr with
         | inl e => 
           cstep g pm av sp = CstepError e
           \/ exists (sps : list subparser)
                     (av' : NtSet.t)
                     (hs  : cstep g pm av sp = CstepK av' sps)
                     (crs : list closure_result),
               crs = dmap sps (fun sp' hi => 
                                 llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inl e
         | inr sps =>
           (cstep g pm av sp = CstepDone /\ sps = [sp])
           \/ exists (sps' : list subparser)
                     (av'  : NtSet.t)
                     (hs   : cstep g pm av sp = CstepK av' sps')
                     (crs  : list closure_result),
               crs = dmap sps' (fun sp' hi => 
                                  llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
               /\ aggrClosureResults crs = inr sps
         end.
  Proof.
    intros g pm sp av a cr hs; subst.
    rewrite llc_unfold.
    eapply llc_cases'; eauto.
  Qed.

  Lemma llc_success_cases :
    forall g pm hc sp av a sps,
      llc hc av sp a = inr sps
      -> (cstep g pm av sp = CstepDone /\ sps = [sp])
         \/ exists (sps' : list subparser)
                   (av'  : NtSet.t)
                   (hs   : cstep g pm av sp = CstepK av' sps')
                   (crs  : list closure_result),
          crs = dmap sps' (fun sp' hi => 
                             llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
          /\ aggrClosureResults crs = inr sps.
  Proof.
    intros g pm hc sp av a sps hs; apply llc_cases with (cr := inr sps); auto.
  Qed.

  Lemma llc_error_cases :
    forall g pm hc sp av a e,
      llc hc av sp a = inl e
      -> cstep g pm av sp = CstepError e
         \/ exists (sps : list subparser)
                   (av' : NtSet.t)
                   (hs  : cstep g pm av sp = CstepK av' sps)
                   (crs : list closure_result),
          crs = dmap sps (fun sp' hi => 
                            llc hc av' sp' (acc_after_step _ _ _ hc hs hi a))
          /\ aggrClosureResults crs = inl e.
  Proof.
    intros g pm hc sp av a e hs; apply llc_cases with (cr := inl e); auto.
  Qed.

  Lemma llc_preserves_prediction' :
    forall g pm (hc : production_map_correct pm g) pair (a : Acc lex_nat_pair pair) sp av a' sp' sps',
      pair = meas g av sp
      -> llc hc av sp a' = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros g pm hc pair a.
    induction a as [pair hlt IH].
    intros sp av a' sp' sps' heq hs hi; subst.
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
    forall g pm (hc : production_map_correct pm g) av sp sp' sps' a,
      llc hc av sp a = inr sps'
      -> In sp' sps'
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros; eapply llc_preserves_prediction'; eauto.
  Qed.

  Definition llClosure (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (sps : list subparser) :
    sum prediction_error (list subparser) :=
    aggrClosureResults (map (fun sp => llc hc (allNts g) sp (lex_nat_pair_wf _)) sps).

  Lemma llClosure_preserves_prediction :
    forall g pm (hc : production_map_correct pm g) sp' sps sps',
      llClosure hc sps = inr sps'
      -> In sp' sps'
      -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
  Proof.
    intros g pm hc sp' sps sps' hl hi.
    eapply aggrClosureResults_succ_in_input in hl; eauto.
    destruct hl as [sps'' [hi' hi'']].
    apply in_map_iff in hi'; destruct hi' as [sp [hspc hi''']].
    eexists; split; eauto.
    eapply llc_preserves_prediction; eauto.
  Qed.

  Definition llTarget g pm (hc : production_map_correct pm g) a sps : sum prediction_error (list subparser) :=
    match move a sps with
    | inl e    => inl e
    | inr sps' =>
      match llClosure hc sps' with
      | inl e     => inl e
      | inr sps'' => inr sps''
      end
    end.
  
  (* LL prediction *)

  Inductive prediction_result :=
  | PredSucc   : list symbol      -> prediction_result
  | PredAmbig  : list symbol      -> prediction_result
  | PredReject :                     prediction_result
  | PredError  : prediction_error -> prediction_result.

  Definition finalConfig (sp : subparser) : bool :=
    match sp with
    | Sp _ (SF None [], []) => true
    | _                     => false
    end.

  Lemma finalConfig_empty_stack :
    forall sp pred stk,
      sp = Sp pred stk
      -> finalConfig sp = true
      -> stk = (SF None [], []).
  Proof.
    intros sp pred stk ? hf; subst; unfold finalConfig in hf; dms; tc.
  Qed.

  Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : bool :=
    allEqual _ beqGamma sp.(prediction) (map prediction sps).

  Lemma allPredictionsEqual_inv_cons :
    forall sp' sp sps,
      allPredictionsEqual sp' (sp :: sps) = true
      -> sp'.(prediction) = sp.(prediction)
         /\ allPredictionsEqual sp' sps = true.
  Proof.
    intros sp' sp sps ha.
    unfold allPredictionsEqual in ha; unfold allEqual in ha; sis.
    apply andb_true_iff in ha; destruct ha as [hhd htl]; split; auto.
    unfold beqGamma in *; dms; tc.
  Qed.

  Lemma allPredictionsEqual_in_tl :
    forall sp sp' sps,
      allPredictionsEqual sp sps = true
      -> In sp' sps
      -> sp'.(prediction) = sp.(prediction).
  Proof.
    intros sp sp' sps ha hi; induction sps as [| sp'' sps IH]; inv hi;
      apply allPredictionsEqual_inv_cons in ha; destruct ha as [hhd htl]; auto.
  Qed.

  Lemma allPredictionsEqual_false_exists_diff_rhs :
    forall sp sps,
      allPredictionsEqual sp sps = false
      -> exists sp',
        In sp' sps
        /\ sp'.(prediction) <> sp.(prediction).
  Proof.
    intros sp sps ha; unfold allPredictionsEqual in ha.
    induction sps as [| sp' sps IH]; simpl in ha.
    - inv ha.
    - apply andb_false_iff in ha; destruct ha as [hh | ht].
      + exists sp'; split.
        * apply in_eq.
        * intros heq; symmetry in heq; apply beqGamma_eq_iff in heq; tc.
      + apply IH in ht; destruct ht as [sp'' [hi hn]].
        exists sp''; split; auto.
        apply in_cons; auto.
  Qed.

  (* propositional spec for allPredictionsEqual *)
  Definition all_predictions_equal sp sps :=
    forall sp', In sp' sps -> prediction sp' = prediction sp.

  Lemma ape_tail :
    forall sp sp' sps,
      all_predictions_equal sp (sp' :: sps)
      -> all_predictions_equal sp sps.
  Proof.
    firstorder.
  Qed.

  Lemma ape_cons_head_eq :
    forall sp sps,
      all_predictions_equal sp sps
      -> all_predictions_equal sp (sp :: sps).
  Proof.
    intros sp sps ha sp' hi; firstorder; subst; auto.
  Qed.
  
  Lemma allPredictionsEqual_prop :
    forall sp sps,
      allPredictionsEqual sp sps = true
      -> all_predictions_equal sp sps.
  Proof.
    intros sp sps ha sp' hi. 
    unfold allPredictionsEqual, allEqual in ha.
    eapply forallb_forall with (x := prediction sp') in ha; eauto.
    - symmetry; apply beqGamma_eq_iff; auto.
    - apply in_map_iff; eauto.
  Qed.

  Lemma ape_false__allPredictionsEqual_false :
    forall sp sps,
      ~ all_predictions_equal sp sps
      -> allPredictionsEqual sp sps = false.
  Proof.
    intros sp sps hn; unfold not in hn.
    destruct (allPredictionsEqual sp sps) eqn:ha; auto.
    exfalso; apply hn; apply allPredictionsEqual_prop; auto.
  Qed.

  Lemma llTarget_preserves_ape:
    forall g pm (hc : production_map_correct pm g) a x sps sps',
    all_predictions_equal x sps
    -> llTarget hc a sps = inr sps'
    -> all_predictions_equal x sps'.
  Proof.
    intros g pm hc a x sps sps'' ha hl sp'' hi''.
    red in ha.
    (* lemma about llTarget preserving prediction *)
    unfold llTarget in hl.
    destruct (move _ _) as [? | sps'] eqn:hm; tc.
    destruct (llClosure _ _) as [? | ?] eqn:hlc; tc; inv hl.
    eapply llClosure_preserves_prediction in hlc; eauto.
    destruct hlc as [sp' [hi' heq']]; rewrite heq'.
    eapply move_preserves_prediction in hm; eauto.
    destruct hm as [sp [hi heq]]; rewrite heq; firstorder.
  Qed.

  Lemma all_predictions_equal_filter :
    forall sp sps sps' f,
      all_predictions_equal sp sps
      -> filter f sps = sps'
      -> all_predictions_equal sp sps'.
  Proof.
    intros sp sps sps' f ha hf sp' hi; subst.
    apply filter_In in hi; firstorder.
  Qed.
      
  Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
    match filter finalConfig sps with
    | []         => PredReject
    | sp :: sps' => 
      if allPredictionsEqual sp sps' then
        PredSucc sp.(prediction)
      else
        PredAmbig sp.(prediction)
    end.

  Lemma handleFinalSubparsers_succ_facts :
    forall sps rhs,
      handleFinalSubparsers sps = PredSucc rhs
      -> exists sp o,
        In sp sps
        /\ sp.(prediction) = rhs
        /\ sp.(stack) = (SF o [], []).
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

  Fixpoint llPredict' (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (sps : list subparser) (ts : list token) : prediction_result :=
    match ts with
    | []            => handleFinalSubparsers sps
    | (a, _) :: ts' =>
      match sps with
      | []          => PredReject
      | sp' :: sps' =>
        if allPredictionsEqual sp' sps' then
          PredSucc sp'.(prediction)
        else
          match llTarget hc a (sp' :: sps') with
          | inl e => PredError e
          | inr sps'' => llPredict' hc sps'' ts'
          end
      end
    end.

  Lemma llPredict'_success_result_in_original_subparsers :
    forall g pm (hc : production_map_correct pm g) ts gamma sps,
      llPredict' hc sps ts = PredSucc gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g pm hpc ts gamma.
    induction ts as [| (a, l) ts IH]; intros sps hl; sis.
    - apply handleFinalSubparsers_succ_facts in hl.
      destruct hl as (sp' & _ & hi & heq & _); eauto.
    - destruct sps as [| sp sps'] eqn:hs; tc; dmeq hall.
      + inv hl; exists sp; split; auto.
        apply in_eq.
      + (* lemma *)
        unfold llTarget in hl.
        destruct (move a _) as [m | sps''] eqn:hm; tc.
        destruct (llClosure hpc sps'') as [m | sps'''] eqn:hc; tc.
        apply IH in hl; destruct hl as [? [? ?]]; subst.
        eapply llClosure_preserves_prediction in hc; eauto.
        destruct hc as [? [? heq]]; rewrite heq.
        eapply move_preserves_prediction in hm; eauto.
        destruct hm as [? [? ?]]; eauto.
  Qed.

  Lemma llPredict'_ambig_result_in_original_subparsers :
    forall g pm (hc : production_map_correct pm g) ts gamma sps,
      llPredict' hc sps ts = PredAmbig gamma
      -> exists sp, In sp sps /\ (prediction sp) = gamma.
  Proof.
    intros g pm hpc ts gamma.
    induction ts as [| (a,l) ts IH]; intros sps hl; sis.
    - apply handleFinalSubparsers_ambig_from_subparsers; auto.
    - destruct sps as [| sp sps'] eqn:hs; tc; dmeq hall.
      + inv hl.
      + (* lemma *)
        unfold llTarget in hl.
        destruct (move a _) as [m | sps''] eqn:hm; tc.
        destruct (llClosure hpc sps'') as [m | sps'''] eqn:hc; tc.
        apply IH in hl; destruct hl as [? [? ?]]; subst.
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
    forall g pm (hc : production_map_correct pm g) sp ys ts sps,
(*      no_left_recursion g
      -> all_suffix_stacks_wf g sps
      -> all_stacks_stable sps *)
      all_predictions_equal sp sps
      -> llPredict' hc sps ts = PredSucc ys
      -> ys = prediction sp.
  Proof.
    intros g pm hc sp ys ts; induction ts as [| (a, l) ts IH];
      intros sps ha hl; sis.
    - unfold handleFinalSubparsers in hl.
      destruct (filter _ _) as [| sp' sps'] eqn:hf; tc.
      dm; tc; inv hl.
      eapply all_predictions_equal_filter in hf; eauto.
      red in hf; firstorder.
    - destruct sps as [| sp' sps']; tc.
      destruct (allPredictionsEqual sp' sps').
      + inv hl; firstorder.
      + destruct (llTarget _ _ _) as [? | sps''] eqn:ht; tc.
        apply IH in hl; auto.
        eapply llTarget_preserves_ape; eauto.
  Qed.

  Lemma all_predictions_equal__llPredict'_neq_ambig :
    forall g pm (hc : production_map_correct pm g) sp ys ts sps,
      all_predictions_equal sp sps
      -> llPredict' hc sps ts <> PredAmbig ys.
  Proof.
    intros g pm hc sp ys ts; induction ts as [| (a, l) ts IH]; intros sps ha hl; sis.
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
    - destruct sps as [| sp' sps']; tc.
      destruct (allPredictionsEqual _ _); tc.
      destruct (llTarget _ _ _) as [? | sps''] eqn:ht; tc.
      apply IH in hl; auto.
      eapply llTarget_preserves_ape; eauto.
  Qed. 

  Definition llInitSps (pm : production_map) (x : nonterminal) (stk : suffix_stack) : list subparser :=
    let (fr, frs) := stk
    in  map (fun rhs => Sp rhs (SF (Some x) rhs, fr :: frs))
            (rhssFor x pm).

  Lemma llInitSps_prediction_in_rhssFor :
    forall pm x stk sp,
      In sp (llInitSps pm x stk)
      -> In sp.(prediction) (rhssFor x pm).
  Proof.
    intros pm x (fr, frs) sp hi; unfold llInitSps in hi.
    eapply in_map_iff in hi; firstorder; subst; auto.
  Qed.

  Lemma llInitSps_result_incl_all_rhss :
    forall g pm fr o x suf rhs frs,
      production_map_correct pm g
      -> fr = SF o (NT x :: suf)
      -> In (x, rhs) g
      -> In (Sp rhs (SF (Some x) rhs, fr :: frs))
            (llInitSps pm x (fr, frs)).
  Proof.
    intros g pm fr o x suf rhs frs hc ? hi; subst.
    apply in_map_iff; exists rhs; split; auto.
    eapply rhssFor_in_iff; eauto.
  Qed.

  Definition llStartState (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (x : nonterminal) (stk : suffix_stack) :
    sum prediction_error (list subparser) :=
    llClosure hc (llInitSps pm x stk).

  Lemma llStartState_sp_prediction_in_rhssFor :
    forall g pm (hc : production_map_correct pm g) x stk sp' sps',
      llStartState hc x stk = inr sps'
      -> In sp' sps'
      -> In sp'.(prediction) (rhssFor x pm).
  Proof.
    intros g pm hc x (fr, frs) sp' sps' hf hi.
    unfold llStartState in hf.
    eapply llClosure_preserves_prediction in hf; eauto.
    destruct hf as [sp [hin heq]]; rewrite heq.
    eapply llInitSps_prediction_in_rhssFor; eauto.
  Qed.

  Definition llPredict (g : grammar) (pm : production_map) (hc : production_map_correct pm g) (x : nonterminal) (stk : suffix_stack)
             (ts : list token) : prediction_result :=
    match llStartState hc x stk with
    | inl msg => PredError msg
    | inr sps => llPredict' hc sps ts
    end.

  Lemma llPredict_succ_in_rhssFor :
    forall g pm (hc : production_map_correct pm g) x stk ts gamma,
      llPredict hc x stk ts = PredSucc gamma
      -> In gamma (rhssFor x pm).
  Proof.
    intros g pm hc x stk ts gamma hp; unfold llPredict in hp.
    dmeq hs; tc.
    apply llPredict'_success_result_in_original_subparsers in hp.
    destruct hp as [sp [hin heq]]; subst.
    eapply llStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma llPredict_ambig_in_rhssFor :
    forall g pm (hc : production_map_correct pm g) x stk ts gamma,
      llPredict hc x stk ts = PredAmbig gamma
      -> In gamma (rhssFor x pm).
  Proof.
    intros g pm hc x stk ts gamma hf.
    unfold llPredict in hf.
    dmeq hs; tc.
    apply llPredict'_ambig_result_in_original_subparsers in hf.
    destruct hf as [sp [hin heq]]; subst.
    eapply llStartState_sp_prediction_in_rhssFor; eauto.
  Qed.

  Lemma llPredict_succ_in_grammar :
    forall g pm (hc : production_map_correct pm g) x stk ts ys,
      llPredict hc x stk ts = PredSucc ys
      -> In (x, ys) g.
  Proof.
    intros g pm hc x stk ts ys hp.
    eapply rhssFor_in_iff; eauto.
    eapply llPredict_succ_in_rhssFor; eauto.
  Qed.

  Lemma llPredict_ambig_in_grammar :
    forall g pm (hc : production_map_correct pm g) x stk ts ys,
      llPredict hc x stk ts = PredAmbig ys
      -> In (x, ys) g.
  Proof.
    intros g pm hc x stk ts ys hp.
    eapply rhssFor_in_iff; eauto.
    eapply llPredict_ambig_in_rhssFor; eauto.
  Qed.

  (* A WELL-FORMEDNESS PREDICATE OVER A SUFFIX STACK *)

  (* The stack predicate is defined in terms of the following
   predicate over a list of locations *)
  Inductive suffix_frames_wf (g : grammar) : list suffix_frame -> Prop :=
  | WF_bottom_init :
      forall x,
        suffix_frames_wf g [SF None [NT x]]
  | WF_bottom_final :
      suffix_frames_wf g [SF None []]
  | WF_upper :
      forall x pre' suf suf' o frs,
        In (x, pre' ++ suf') g
        -> suffix_frames_wf g (SF o (NT x :: suf) :: frs)
        -> suffix_frames_wf g (SF (Some x) suf' :: SF o (NT x :: suf) :: frs).

  Hint Constructors suffix_frames_wf : core.

  (* invert a suffix_suffix_frames_wf judgment, naming the hypotheses hi and hw' *)
  Ltac inv_suffix_frames_wf hw  hi hw' :=
    inversion hw as [ ? | | ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac wf_upper_nil := eapply WF_upper with (pre' := []); sis; eauto. 

  (* The stack well-formedness predicate *)
  Definition suffix_stack_wf (g : grammar) (stk : suffix_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      suffix_frames_wf g (fr :: frs)
    end.

  (* Lift the predicate to a list of subparsers *)
  Definition all_suffix_stacks_wf (g : grammar) (sps: list subparser) : Prop :=
    forall sp, In sp sps -> suffix_stack_wf g sp.(stack).

  Lemma return_preserves_suffix_frames_wf_invar :
    forall g o o' suf_cr x frs,
      suffix_frames_wf g (SF o [] :: SF o' (NT x :: suf_cr) :: frs)
      -> suffix_frames_wf g (SF o' suf_cr :: frs).
  Proof.
    intros g o o' suf_cr x locs hw.
    inv_suffix_frames_wf hw hi hw'.
    inv_suffix_frames_wf hw' hi' hw''; auto.
    rewrite app_cons_group_l in hi'; eauto.
  Qed.

  Lemma push_preserves_suffix_frames_wf_invar :
    forall g o suf x rhs frs,
      In (x, rhs) g
      -> suffix_frames_wf g (SF o (NT x :: suf) :: frs)
      -> suffix_frames_wf g (SF (Some x) rhs :: SF o (NT x :: suf) :: frs).
  Proof.
    intros; wf_upper_nil. 
  Qed.
       
  Lemma consume_preserves_suffix_frames_wf_invar :
    forall g o suf a frs,
      suffix_frames_wf g (SF o (T a :: suf) :: frs)
      -> suffix_frames_wf g (SF o suf :: frs).
  Proof.
    intros g o suf a frs hw.
    inv_suffix_frames_wf hw hi hw'; auto.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  Lemma cstep_preserves_suffix_stack_wf_invar :
    forall g pm sp sp' sps' av av',
      production_map_correct pm g
      -> suffix_stack_wf g sp.(stack)
      -> cstep g pm av sp = CstepK av' sps'
      -> In sp' sps'
      -> suffix_stack_wf g sp'.(stack).
  Proof.
    intros g pm sp sp' sps' av av' hc hw hs hi.
    unfold cstep in hs; dms; tc; sis; inv hs.
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_suffix_frames_wf_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_suffix_frames_wf_invar; auto.
      eapply rhssFor_in_iff; eauto.
    - inv hi.
  Qed.

  Lemma llInitSps_preserves_suffix_stack_wf_invar :
    forall g pm fr o x suf frs,
      production_map_correct pm g
      -> fr = SF o (NT x :: suf)
      -> suffix_stack_wf g (fr, frs)
      -> all_suffix_stacks_wf g (llInitSps pm x (fr, frs)).
  Proof.
    intros g pm fr o x suf frs hc ? hw sp hi; subst; unfold llInitSps in hi.
    apply in_map_iff in hi.
    destruct hi as [rhs [? hi]]; subst; sis.
    apply push_preserves_suffix_frames_wf_invar; eauto.
    eapply rhssFor_in_iff; eauto.
  Qed.    

  (* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

  (* Auxiliary definition *)
  Inductive frames_repr_nullable_path (g : grammar) : list suffix_frame -> Prop :=
  | FR_direct :
      forall x pre' suf suf' o o',
        In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> frames_repr_nullable_path g [SF o' suf' ; SF o (NT x :: suf)]
  | FR_indirect :
      forall x pre' suf suf' o o' frs,
        In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> frames_repr_nullable_path g (SF o (NT x :: suf) :: frs)
        -> frames_repr_nullable_path g (SF o' suf' :: SF o (NT x :: suf) :: frs).

  Hint Constructors frames_repr_nullable_path : core.

  Ltac inv_frnp hf hi hn hf' :=
    inversion hf as [? ? ? ? ? ? hi hn | ? ? ? ? ? ? ? hi hn hf']; subst; clear hf.

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
      -> exists o x suf,
        fr = SF o (NT x :: suf).
  Proof.
    intros g fr fr' frs hf; inv hf; eauto.
  Qed.

  Lemma frnp_shift_head_frame :
    forall g frs o pre suf,
      nullable_gamma g pre
      -> frames_repr_nullable_path g (SF o (pre ++ suf) :: frs)
      -> frames_repr_nullable_path g (SF o suf :: frs).
  Proof.
    intros g frs o pre suf hn hf; destruct frs as [| fr frs]; inv_frnp hf hi hn' hf'.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
  Qed.
  
  Lemma frnp_grammar_nullable_path :
    forall g frs fr fr_cr o o' x y suf suf',
      fr       = SF o' (NT y :: suf')
      -> fr_cr = SF o (NT x :: suf)
      -> frames_repr_nullable_path g (fr :: frs ++ [fr_cr])
      -> nullable_path g (NT x) (NT y).
  Proof.
    intros g frs.
    induction frs as [| fr' frs IH]; intros fr fr_cr o o' x z suf suf'' ? ? hf; subst; sis.
    - inv_frnp hf hi hn hf'.
      + eapply DirectPath; eauto.
      + inv hf'.
    - pose proof hf as hf'; apply frnp_second_frame_nt_head in hf'.
      destruct hf' as (? & y & suf' & ?); subst.
      apply nullable_path_trans with (y := NT y).
      + apply frnp_inv_two_head_frames in hf; eauto.
      + inv_frnp hf hi hn hf'; eauto.
  Qed.

  Lemma frnp_caller_nt_nullable :
    forall g x o o' suf suf' frs,
      frames_repr_nullable_path g (SF o' suf' :: SF o (NT x :: suf) :: frs)
      -> nullable_gamma g suf'
      -> nullable_sym g (NT x).
  Proof.
    intros g x o o' suf suf' frs hf hng.
    inv_frnp hf hi hn hf'.
    - econstructor; eauto.
      apply nullable_app; auto.
    - econstructor; eauto.
      apply nullable_app; auto.
  Qed.

  (* The invariant itself *)
  Definition unavailable_nts_are_open_calls g av stk : Prop :=
    match stk with
    | (fr, frs) =>
      forall (x : nonterminal),
        NtSet.In x (allNts g)
        -> ~ NtSet.In x av
        -> exists frs_pre fr_cr frs_suf o suf,
            frs = frs_pre ++ fr_cr :: frs_suf
            /\ fr_cr = SF o (NT x :: suf)
            /\ frames_repr_nullable_path g (fr :: frs_pre ++ [fr_cr])
    end.

  (* Lift the invariant to a subparser *)
  Definition unavailable_nts_invar g av sp :=
    match sp with
    | Sp _ stk => unavailable_nts_are_open_calls g av stk
    end.

  (* Lift the invariant to a list of subparsers *)
  Definition sps_unavailable_nts_invar g av sps : Prop :=
    forall sp, In sp sps -> unavailable_nts_invar g av sp.

  Lemma return_preserves_unavailable_nts_invar :
    forall g av pr o o' suf x fr cr cr' frs,
      fr     = SF o []
      -> cr  = SF o' (NT x :: suf)
      -> cr' = SF o' suf
      -> unavailable_nts_invar g av (Sp pr (fr, cr :: frs))
      -> unavailable_nts_invar g (NtSet.add x av) (Sp pr (cr', frs)). 
  Proof.
    intros g av pr o o' suf' x' fr cr cr' frs ? ? ? hu; subst.
    intros x hi hn.
    assert (hn' : ~ NtSet.In x av) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & suf & heq & ? & hf); subst.
    destruct frs_pre as [| fr' frs_pre]; sis; inv heq.
    - ND.fsetdec.
    - pose proof hf as hf'; apply frnp_inv_two_head_frames in hf'.
      apply frnp_shift_head_frame with (pre := [NT x']) in hf'; eauto 8.
      constructor; auto.
      apply frnp_caller_nt_nullable in hf; auto.
  Qed.

  Lemma push_preserves_unavailable_nts_invar :
    forall g cr ce av pr o o' suf x rhs frs,
      cr = SF o (NT x :: suf)
      -> ce = SF o' rhs
      -> In (x, rhs) g
      -> unavailable_nts_invar g av (Sp pr (cr, frs))
      -> unavailable_nts_invar g (NtSet.remove x av) (Sp pr (ce, cr :: frs)).
  Proof.
    intros g cr ce av pr o o' suf' x' rhs frs ? ? hi hu; subst.
    intros x hi' hn.
    destruct (NF.eq_dec x' x); subst.
    - exists []; repeat eexists; eauto; sis.
      eapply FR_direct with (pre' := []); auto.
    - assert (hn' : ~ NtSet.In x av) by ND.fsetdec.
      apply hu in hn'; simpl in hn'; clear hu; auto.
      destruct hn' as (frs_pre & fr_cr & frs_suf & ? &
                       suf & heq & heq' & hf); subst.
      exists (SF o (NT x' :: suf') :: frs_pre); repeat eexists; eauto.
      eapply FR_indirect with (pre' := []); eauto.
  Qed.

  Lemma cstep_preserves_unavailable_nts_invar :
    forall g pm sp sp' sps' av av',
      production_map_correct pm g
      -> unavailable_nts_invar g av sp
      -> cstep g pm av sp = CstepK av' sps'
      -> In sp' sps'
      -> unavailable_nts_invar g av' sp'.
  Proof.
    intros g pm sp sp' sps' av av' hc hu hs hi.
    unfold cstep in hs; dmeqs h; inv hs; tc.
    - apply in_singleton_eq in hi; subst.
      eapply return_preserves_unavailable_nts_invar; eauto.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply push_preserves_unavailable_nts_invar; eauto.
      eapply rhssFor_in_iff; eauto.
    - inv hi.
  Qed.

  Lemma unavailable_nts_allNts :
    forall g pred stk,
      unavailable_nts_invar g (allNts g) (Sp pred stk).
  Proof.
    intros g pred (fr, frs); repeat red; intros; ND.fsetdec.
  Qed.

End LLPredictionFn.

 
