Require Import List.
Require Import CoStar.Lex.
Require Import CoStar.SLL_optimization_sound.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module SllPredictionErrorFreeFn (Import D : Defs.T).

  Module Export SLLS := SllOptimizationSoundFn D.

  (* A more permissive well-formedness invariant that 
     places fewer restrictions on the bottom frame *)
  Inductive frames_top_wf (g : grammar) : list sll_frame -> Prop :=
  | TWF_bottom :
      forall o ys,
        frames_top_wf g [SllFr o ys]
  | TWF_upper :
      forall x pre' suf suf' o frs,
        PM.In (x, pre' ++ suf') g
        -> frames_top_wf g (SllFr o (NT x :: suf) :: frs)
        -> frames_top_wf g (SllFr (Some x) suf' :: SllFr o (NT x :: suf) :: frs).

  Hint Constructors frames_top_wf : core.

  (* invert an sframes_top_wf judgment, naming the hypotheses hi and hw' *)
  Ltac inv_twf hw  hi hw' :=
    inversion hw as [ ? ? | ? ? ? ? ? ? hi hw']; subst; clear hw.

  Ltac twf_upper_nil := eapply TWF_upper with (pre' := []); sis; eauto. 

  (* The stack top well-formedness predicate *)
  Definition stack_top_wf (g : grammar) (stk : sll_stack) : Prop :=
    match stk with
    | (fr, frs) =>
      frames_top_wf g (fr :: frs)
    end.

  Definition all_stack_tops_wf g sps :=
    forall sp, In sp sps -> stack_top_wf g (sll_stk sp).

  (*
  Lemma suffix_frames_wf__frames_top_wf :
    forall g frs,
      suffix_frames_wf g frs -> frames_top_wf g frs.
  Proof.
    intros g frs hw; induction hw; eauto.
  Qed.
  
  Lemma suffix_stack_wf__stack_top_wf :
    forall g fr frs,
      suffix_stack_wf g (fr, frs) -> stack_top_wf g (fr, frs).
  Proof.
    intros; apply suffix_frames_wf__frames_top_wf; auto.
  Qed.
   *)
  
  Lemma return_preserves_frames_top_wf :
    forall g o o' suf_cr x frs,
      frames_top_wf g (SllFr o [] :: SllFr o' (NT x :: suf_cr) :: frs)
      -> frames_top_wf g (SllFr o' suf_cr :: frs).
  Proof.
    intros g o o' suf_cr x locs hw.
    inv_twf hw  hi hw'.
    inv_twf hw' hi' hw''; auto.
    rewrite app_cons_group_l in hi'; eauto.
  Qed.

  Lemma push_preserves_frames_top_wf :
    forall g o suf x rhs frs,
      PM.In (x, rhs) g
      -> frames_top_wf g (SllFr o (NT x :: suf) :: frs)
      -> frames_top_wf g (SllFr (Some x) rhs :: SllFr o (NT x :: suf) :: frs).
  Proof.
    intros; twf_upper_nil. 
  Qed.
       
  Lemma consume_preserves_frames_top_wf_invar :
    forall g o suf a frs,
      frames_top_wf g (SllFr o (T a :: suf) :: frs)
      -> frames_top_wf g (SllFr o suf :: frs).
  Proof.
    intros g o suf a frs hw.
    inv_twf hw  hi hw'; auto.
    rewrite app_cons_group_l in hi; eauto.
  Qed.

  Lemma sllMoveSp_preserves_stack_top_wf :
    forall g t sp sp',
      stack_top_wf g sp.(sll_stk)
      -> sllMoveSp t sp = MoveSucc sp'
      -> stack_top_wf g sp'.(sll_stk).
  Proof.
    intros g t sp sp' hw hm.
    unfold sllMoveSp in hm; dms; tc; inv hm; sis.
    eapply consume_preserves_frames_top_wf_invar; eauto.
  Qed.

  Lemma sllMove_preserves_stack_top_wf :
    forall g t sps sps',
      all_stack_tops_wf g sps
      -> sllMove t sps = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g t sps sps' ha hm sp' hi.
    eapply aggrMoveResults_succ_in_input in hm; eauto.
    apply in_map_iff in hm; destruct hm as [sp [hm hi']].
    eapply sllMoveSp_preserves_stack_top_wf ; eauto.
  Qed.

  Lemma sllCstep_preserves_stack_top_wf :
    forall g rm sp sp' sps' av av',
      rhs_map_correct rm g
      -> stack_top_wf g sp.(sll_stk)
      -> sllCstep rm av sp = CstepK av' sps'
      -> In sp' sps'
      -> stack_top_wf g sp'.(sll_stk).
  Proof.
    intros g pm sp sp' sps' av av' hc hw hs hi.
    unfold sllCstep in hs; dms; tc; sis; inv hs.
    - apply in_singleton_eq in hi; subst; sis.
      eapply return_preserves_frames_top_wf; eauto.
    - inv hi.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst; sis.
      apply push_preserves_frames_top_wf; auto.
      eapply rhssFor_in_iff; eauto.
  Qed.

  (* refactor *)
  Lemma simReturn_stack_top_wf :
    forall g cm sp sp' sps',
      closure_map_correct g cm
      -> simReturn cm sp = Some sps'
      -> In sp' sps'
      -> stack_top_wf g (sll_stk sp').
  Proof.
    intros g cm [pr (fr, frs)] sp' sps' [hs hc] hr hi.
    pose proof hr as heq; apply simReturn_stack_shape in heq.
    destruct heq as [x heq]; inv heq; inv hr.
    apply in_map_iff in hi. destruct hi as [fr [heq hi]]; subst; sis.
    unfold destFrames in hi.
    dmeq hf; tc.
    - (* lemma *)
      apply FMF.find_mapsto_iff in hf.
      eapply hs in hi; eauto.
      destruct hi as [hm hst].
      destruct fr as [[y |] [| [a | y'] suf]]; inv hst; auto.
    - inv hi.
  Qed.

  Lemma sllc_preserves_suffix_stack_wf_invar :
    forall gr rm cm pr (a : Acc lex_nat_pair pr) vi sp hk sp' a' sps',
      pr = sll_meas rm vi sp
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_top_wf gr sp.(sll_stk)
      -> sllc rm cm vi sp hk a' = inr sps'
      -> In sp' sps'
      -> stack_top_wf gr sp'.(sll_stk).
  Proof.
    intros g pm cm pr a'.
    induction a' as [pr hlt IH]; intros vi sp hk sp' a sps' heq hp hc hw hs hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply simReturn_stack_top_wf; eauto.
    - apply in_singleton_eq in hi; subst; auto.
    - eapply aggrClosureResults_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply sllCstep_meas_lt; eauto.
      + eapply sllCstep_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllClosure_preserves_stack_top_wf :
    forall g pm cm sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllClosure pm cm sps hk = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g pm cm sps hk sps' hp hc ha hs sp' hi.
    eapply aggrClosureResults_succ_in_input in hs; eauto.
    destruct hs as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sllc_preserves_suffix_stack_wf_invar; eauto.
    apply lex_nat_pair_wf.
  Qed.
  
  Lemma sllTarget_preserves_stack_top_wf :
    forall g pm cm a sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllTarget pm cm a sps hk = inr sps'
      -> all_stack_tops_wf g sps'.
  Proof.
    intros g pm cm a sps hk sps' hp hc hw ht.
    apply sllTarget_cases in ht.
    destruct ht as [sps'' [hk' [hm hc']]].
    eapply sllMove_preserves_stack_top_wf in hm; eauto.
    eapply sllClosure_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllInitSps_stack_tops_wf :
    forall g pm x,
      all_stack_tops_wf g (sllInitSps pm x).
  Proof.
    intros g pm x [pr (fr, frs)] hi; sis.
    apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; inv heq; auto.
  Qed.

  Lemma sllStartState_preserves_stack_top_wf :
    forall g pm cm x sps,
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sllStartState pm cm x = inr sps
      -> all_stack_tops_wf g sps.
  Proof.
    intros g pm cm x sps hp hm hs sp hi.
    eapply sllClosure_preserves_stack_top_wf; eauto.
    apply sllInitSps_stack_tops_wf; auto.
  Qed.

  (* Some facts about the stable_config invariant --
     these should eventually move elsewhere *)

  (* refactor *)
  Lemma simReturn_some__all_stacks_stable :
    forall g cm sp sps',
      closure_map_correct g cm
      -> simReturn cm sp = Some sps'
      -> all_stable sps'.
  Proof.
    intros g cm sp sps' [hs hc] hr sp' hi.
    unfold simReturn in hr; dms; tc; inv hr.
    apply in_map_iff in hi; destruct hi as [fr [heq hi]]; subst; sis.
    unfold destFrames in hi; dmeq hf; try solve [inv hi].
    apply FMF.find_mapsto_iff in hf; eapply hs in hi; eauto.
    destruct hi as [_ hst].
    destruct fr as [[x |] [| [a|y] suf]]; sis; tc; auto.
  Qed.

  Lemma simReturn_none_cstepDone__stable_config :
    forall g pm cm vi sp,
      stack_top_wf g sp.(sll_stk)
      -> simReturn cm sp = None
      -> sllCstep pm vi sp = CstepDone
      -> sll_stable_config sp.(sll_stk).
  Proof.
    intros g pm cm vi [pred ([o suf], frs)] hw hr hs.
    unfold sllCstep in hs; dms; tc; sis; inv hw; auto.
    dms; tc.
  Qed.
  
  Lemma sllc_all_stacks_stable :
    forall g pm cm pr (a : Acc lex_nat_pair pr) vi sp hk a' sps',
      pr = sll_meas pm vi sp
      -> rhs_map_correct pm g
      -> closure_map_correct g cm
      -> stack_top_wf g sp.(sll_stk)
      -> sllc pm cm vi sp hk a' = inr sps'
      -> all_stable sps'. 
  Proof.
    intros g pm cm pr a'.
    induction a' as [pr hlt IH]; intros vi sp hk a sps' ? hp hc hw hs sp' hi; subst.
    apply sllc_success_cases in hs.
    destruct hs as [hr | [hr [[hs' ?] | [ys' [avy' [hs' [? [? ha']]]]]]]]; subst.
    - eapply simReturn_some__all_stacks_stable; eauto.
    - apply in_singleton_eq in hi; subst.
      eapply simReturn_none_cstepDone__stable_config; eauto.
    - eapply aggrClosureResults_succ_in_input in ha'; eauto.
      destruct ha' as [sps''' [hi' hi'']].
      eapply dmap_in in hi'; eauto.
      destruct hi' as [sp'' [hi' [hi''' heq]]].
      eapply IH in heq; eauto.
      + eapply sllCstep_meas_lt; eauto.
      + eapply sllCstep_preserves_stack_top_wf; eauto.
  Qed.

  Lemma sllClosure__all_stacks_stable :
    forall g pm cm sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllClosure pm cm sps hk = inr sps'
      -> all_stable sps'.
  Proof.
    intros g pm cm sps hk sps' hp hm hw hc sp' hi.
    eapply aggrClosureResults_succ_in_input in hc; eauto.
    destruct hc as [sps'' [hi' hi'']].
    eapply dmap_in in hi'; eauto; sis.
    destruct hi' as [sp [hi' [_ hs]]].
    eapply sllc_all_stacks_stable; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma sllTarget__all_stacks_stable :
    forall g pm cm a sps hk sps',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> sllTarget pm cm a sps hk = inr sps'
      -> all_stable sps'.
  Proof.
    intros g pm cm a sps hk sps' hp hc hw ht.
    apply sllTarget_cases in ht.
    destruct ht as [sps'' [hk' [hm hc']]].
    eapply sllMove_preserves_stack_top_wf in hm; eauto.
    eapply sllClosure__all_stacks_stable; eauto.
  Qed.
  
  (* X never returns SpInvalidState *)

  Lemma sllMoveSp_never_returns_SpInvalidState_for_ready_sp :
    forall t sp,
      sll_stable_config sp.(sll_stk)
      -> sllMoveSp t sp <> MoveError SpInvalidState.
  Proof.
    intros t sp hr; unfold not; intros hm.
    unfold sllMoveSp in hm.
    dms; tc; sis; inv hr.
  Qed.

  Lemma sll_move_never_returns_SpInvalidState_for_ready_sps :
    forall t sps,
      all_stable sps
      -> sllMove t sps <> inl SpInvalidState.
  Proof.
    intros t sps ha; unfold not; intros hm.
    unfold move in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply sllMoveSp_never_returns_SpInvalidState_for_ready_sp; eauto.
  Qed.
  
  Lemma sll_cstep_never_returns_SpInvalidState :
    forall g pm vi sp,
      stack_top_wf g sp.(sll_stk)
      -> sllCstep pm vi sp <> CstepError SpInvalidState.
  Proof.
    intros g pm vi sp hw hs.
    unfold sllCstep in hs; dms; subst; tc; inv hw.
  Qed.

  Lemma sllc_never_returns_SpInvalidState :
    forall (g    : grammar)
           (pm   : rhs_map)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (vi   : NtSet.t)
           (sp   : sll_subparser)
           (hk   : sll_sp_pushes_from_keyset pm sp)
           (a'   : Acc lex_nat_pair (sll_meas pm vi sp)),
      pair = sll_meas pm vi sp
      -> rhs_map_correct pm g
      -> stack_top_wf g sp.(sll_stk)
      -> sllc pm cm vi sp hk a' <> inl SpInvalidState.
  Proof.
    intros g pm cm pair a'.
    induction a' as [pair hlt IH].
    intros vi sp hk ha heq hp hw hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hsr [hs | [sps [av' [hs [crs [heq heq']]]]]]]; subst.
    - eapply sll_cstep_never_returns_SpInvalidState; eauto. 
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply sllCstep_meas_lt; eauto.
      + eapply sllCstep_preserves_stack_top_wf; eauto.
  Qed.
  
  Lemma sllClosure_neq_SpInvalidState :
    forall g pm cm sps hk,
      rhs_map_correct pm g
      -> all_stack_tops_wf g sps
      -> sllClosure pm cm sps hk <> inl SpInvalidState.
  Proof.
    intros g pm cm sps hk hp hw hc.
    unfold sllClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    eapply dmap_in in hc; eauto; sis.
    destruct hc as [sp [hi [_ hs]]].
    eapply sllc_never_returns_SpInvalidState; eauto.
    apply lex_nat_pair_wf.
  Qed.

  Lemma sllTarget_neq_SpInvalidState :
    forall g pm cm a sps hk,
      rhs_map_correct pm g
      -> all_stack_tops_wf g sps
      -> all_stable sps
      -> sllTarget pm cm a sps hk <> inl SpInvalidState.
  Proof.
    intros g pm cm a sps hk hp hw hs ht.
    apply sllTarget_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply sll_move_never_returns_SpInvalidState_for_ready_sps; eauto. 
    - eapply sllMove_preserves_stack_top_wf in hm; eauto.
      eapply sllClosure_neq_SpInvalidState; eauto.
  Qed.

  Lemma sllHandleFinalSubparsers_never_returns_error :
    forall sps e,
      sllHandleFinalSubparsers sps <> PredError e.
  Proof.
    intros sps e; unfold not; intro hh.
    unfold sllHandleFinalSubparsers in hh; dms; tc.
  Qed.

  Lemma sllPredict'_neq_SpInvalidState :
    forall g pm cm ts sps ca hk hc ca',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> all_stack_tops_wf g sps
      -> all_stable sps
      -> sllPredict' pm cm sps ts ca hk hc <> (PredError SpInvalidState, ca').
  Proof.
    intros g pm cm ts; induction ts as [| (a, l) ts IH];
      intros sps ca hk hc ca' hp' hm hw hs hp; sis.
    - inv hp; eapply sllHandleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      apply sllPredict'_cont_cases in hp.
      destruct hp as [ [sps'' [hf hp]] | [ht | [sps'' [ht hp]]]].
      + pose proof hf as hf'; apply hc in hf'.
        destruct hf' as [hk' ht].
        eapply IH in hp; eauto.
        * eapply sllTarget_preserves_stack_top_wf; eauto.
        * eapply sllTarget__all_stacks_stable; eauto.
      + eapply sllTarget_neq_SpInvalidState; eauto.
      + eapply IH in hp; eauto.
        * eapply sllTarget_preserves_stack_top_wf; eauto.
        * eapply sllTarget__all_stacks_stable; eauto.
  Qed.

  Lemma sllStartState_neq_SpInvalidState :
    forall g pm cm x,
      rhs_map_correct pm g
      -> sllStartState pm cm x <> inl SpInvalidState.
  Proof.
    intros g pm cm x hp hss.
    eapply sllClosure_neq_SpInvalidState; eauto.
    apply sllInitSps_stack_tops_wf; auto.
  Qed.
  
  Lemma sllPredict_neq_SpInvalidState :
    forall g pm cm x ts ca hc ca',
      rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sllPredict pm cm x ts ca hc <> (PredError SpInvalidState, ca').
  Proof.
    intros g pm cm x ts ca hc ca' hp hc' hs.
    apply sllPredict_cases in hs.
    destruct hs as [hs | [sps [hss hs]]].
    - eapply sllStartState_neq_SpInvalidState; eauto.
    - eapply sllPredict'_neq_SpInvalidState; eauto.
      + eapply sllStartState_preserves_stack_top_wf; eauto.
      + eapply sllClosure__all_stacks_stable; eauto.
        apply sllInitSps_stack_tops_wf; auto.
  Qed.

  (* X never returns SpLeft Recursion *)

  (* to do -- we might be able to merge the two "unavailable NTs" invariants
     into a single definition *)

  (* AN INVARIANT THAT RELATES "UNAVAILABLE" NONTERMINALS
   TO THE SHAPE OF THE STACK *)

  (* Auxiliary definition *)
  Inductive sll_frames_repr_nullable_path (g : grammar) : list sll_frame -> Prop :=
  | FR_direct :
      forall x pre' suf suf' o o',
        PM.In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> sll_frames_repr_nullable_path g [SllFr o' suf' ; SllFr o (NT x :: suf)]
  | FR_indirect :
      forall x pre' suf suf' o o' frs,
        PM.In (x, pre' ++ suf') g
        -> nullable_gamma g pre'
        -> sll_frames_repr_nullable_path g (SllFr o (NT x :: suf) :: frs)
        -> sll_frames_repr_nullable_path g (SllFr o' suf' :: SllFr o (NT x :: suf) :: frs).

  Hint Constructors sll_frames_repr_nullable_path : core.

  Ltac inv_frnp hf hi hn hf' :=
    inversion hf as [? ? ? ? ? ? hi hn | ? ? ? ? ? ? ? hi hn hf']; subst; clear hf.

  Lemma sll_frnp_inv_two_head_frames :
    forall g fr fr' fr'' frs,
      sll_frames_repr_nullable_path g (fr'' :: fr' :: frs ++ [fr])
      -> sll_frames_repr_nullable_path g (fr' :: frs ++ [fr]).
  Proof.
    intros g fr fr'' fr''' frs hf.
    destruct frs as [| fr' frs]; sis; inv hf; auto.
  Qed.

  Lemma sll_frnp_second_frame_nt_head :
    forall g fr fr' frs,
      sll_frames_repr_nullable_path g (fr' :: fr :: frs)
      -> exists o x suf,
        fr = SllFr o (NT x :: suf).
  Proof.
    intros g fr fr' frs hf; inv hf; eauto.
  Qed.

  Lemma sll_frnp_shift_head_frame :
    forall g frs o pre suf,
      nullable_gamma g pre
      -> sll_frames_repr_nullable_path g (SllFr o (pre ++ suf) :: frs)
      -> sll_frames_repr_nullable_path g (SllFr o suf :: frs).
  Proof.
    intros g frs o pre suf hn hf; destruct frs as [| fr frs]; inv_frnp hf hi hn' hf'.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
    - rewrite app_assoc in hi; econstructor; eauto.
      apply nullable_app; auto.
  Qed.
  
  Lemma sll_frnp_grammar_nullable_path :
    forall g frs fr fr_cr o o' x y suf suf',
      fr       = SllFr o' (NT y :: suf')
      -> fr_cr = SllFr o (NT x :: suf)
      -> sll_frames_repr_nullable_path g (fr :: frs ++ [fr_cr])
      -> nullable_path g (NT x) (NT y).
  Proof.
    intros g frs.
    induction frs as [| fr' frs IH]; intros fr fr_cr o o' x z suf suf'' ? ? hf; subst; sis.
    - inv_frnp hf hi hn hf'.
      + eapply DirectPath; eauto.
      + inv hf'.
    - pose proof hf as hf'; apply sll_frnp_second_frame_nt_head in hf'.
      destruct hf' as (? & y & suf' & ?); subst.
      apply nullable_path_trans with (y := NT y).
      + apply sll_frnp_inv_two_head_frames in hf; eauto.
      + inv_frnp hf hi hn hf'; eauto.
  Qed.

  Lemma sll_frnp_caller_nt_nullable :
    forall g x o o' suf suf' frs,
      sll_frames_repr_nullable_path g (SllFr o' suf' :: SllFr o (NT x :: suf) :: frs)
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
  Definition sll_unavailable_nts_are_open_calls g vi stk : Prop :=
    match stk with
    | (fr, frs) =>
      forall (x : nonterminal),
        NtSet.In x (allNts g)
        -> NtSet.In x vi
        -> exists frs_pre fr_cr frs_suf o suf,
            frs = frs_pre ++ fr_cr :: frs_suf
            /\ fr_cr = SllFr o (NT x :: suf)
            /\ sll_frames_repr_nullable_path g (fr :: frs_pre ++ [fr_cr])
    end.

  (* Lift the invariant to a subparser *)
  Definition sll_unavailable_nts_invar g vi sp :=
    match sp with
    | SllSp _ stk => sll_unavailable_nts_are_open_calls g vi stk
    end.

  (* Lift the invariant to a list of subparsers *)
  Definition sll_sps_unavailable_nts_invar g vi sps : Prop :=
    forall sp, In sp sps -> unavailable_nts_invar g vi sp.

  Lemma sll_return_preserves_unavailable_nts_invar :
    forall g vi pr o o' suf x fr cr cr' frs,
      fr     = SllFr o []
      -> cr  = SllFr o' (NT x :: suf)
      -> cr' = SllFr o' suf
      -> sll_unavailable_nts_invar g vi (SllSp pr (fr, cr :: frs))
      -> sll_unavailable_nts_invar g (NtSet.remove x vi) (SllSp pr (cr', frs)). 
  Proof.
    intros g vi pr o o' suf' x' fr cr cr' frs ? ? ? hu; subst.
    intros x hi hn.
    assert (hn' : NtSet.In x vi) by ND.fsetdec.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & suf & heq & ? & hf); subst.
    destruct frs_pre as [| fr' frs_pre]; sis; inv heq.
    - ND.fsetdec.
    - pose proof hf as hf'; apply sll_frnp_inv_two_head_frames in hf'.
      apply sll_frnp_shift_head_frame with (pre := [NT x']) in hf'; eauto 8.
      constructor; auto.
      apply sll_frnp_caller_nt_nullable in hf; auto.
  Qed.

  Lemma sll_push_preserves_unavailable_nts_invar :
    forall g cr ce vi pr o o' suf x rhs frs,
      cr = SllFr o (NT x :: suf)
      -> ce = SllFr o' rhs
      -> PM.In (x, rhs) g
      -> sll_unavailable_nts_invar g vi (SllSp pr (cr, frs))
      -> sll_unavailable_nts_invar g (NtSet.add x vi) (SllSp pr (ce, cr :: frs)).
  Proof.
    intros g cr ce vi pr o o' suf' x' rhs frs ? ? hi hu; subst.
    intros x hi' hn.
    destruct (NF.eq_dec x' x); subst.
    - exists []; repeat eexists; eauto; sis.
      eapply FR_direct with (pre' := []); auto.
    - assert (hn' : NtSet.In x vi) by ND.fsetdec.
      apply hu in hn'; simpl in hn'; clear hu; auto.
      destruct hn' as (frs_pre & fr_cr & frs_suf & ? &
                       suf & heq & heq' & hf); subst.
      exists (SllFr o (NT x' :: suf') :: frs_pre); repeat eexists; eauto.
      eapply FR_indirect with (pre' := []); eauto.
  Qed.

  Lemma sllCstep_preserves_unavailable_nts_invar :
    forall g pm sp sp' sps' vi vi',
      rhs_map_correct pm g
      -> sll_unavailable_nts_invar g vi sp
      -> sllCstep pm vi sp = CstepK vi' sps'
      -> In sp' sps'
      -> sll_unavailable_nts_invar g vi' sp'.
  Proof.
    intros g pm sp sp' sps' vi vi' hc hu hs hi.
    unfold sllCstep in hs; dmeqs h; inv hs; tc.
    - apply in_singleton_eq in hi; subst.
      eapply sll_return_preserves_unavailable_nts_invar; eauto.
    - inv hi.
    - apply in_map_iff in hi; destruct hi as [rhs [heq hi]]; subst.
      eapply sll_push_preserves_unavailable_nts_invar; eauto.
      eapply rhssFor_in_iff; eauto.
  Qed.

  Lemma sll_unavailable_nts_empty :
    forall g pred stk,
      sll_unavailable_nts_invar g NtSet.empty (SllSp pred stk).
  Proof.
    intros g pred (fr, frs); repeat red; intros; ND.fsetdec.
  Qed.

  (* Moving on to facts about the prediction mechanism ... *)
  
  Lemma sllCstep_LeftRecursion_facts :
    forall gr rm vi pred fr frs x,
      rhs_map_correct rm gr
      -> sllCstep rm vi (SllSp pred (fr, frs)) = CstepError (SpLeftRecursion x)
      -> NtSet.In x vi
         /\ NtSet.In x (allNts gr)
         /\ exists o suf,
             fr = SllFr o (NT x :: suf).
  Proof.
    intros gr rm vi pred fr frs x hp hs.
    unfold sllCstep in hs; repeat dmeq h; tc; inv hs; sis.
    repeat split; eauto.
    - apply NF.mem_iff; auto. 
    - eapply find_allNts; eauto.
  Qed.

  Lemma sllCstep_never_finds_left_recursion :
    forall gr rm vi sp x,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> sll_unavailable_nts_invar gr vi sp
      -> sllCstep rm vi sp <> CstepError (SpLeftRecursion x).
  Proof.
    intros gr rm vi [pred (fr, frs)] x hn hc hu; unfold not; intros hs.
    pose proof hs as hs'.
    eapply sllCstep_LeftRecursion_facts in hs'; eauto.
    destruct hs' as [hn' [hi [o [suf' heq]]]]; subst.
    apply hu in hn'; auto.
    destruct hn' as (frs_pre & fr_cr & frs_suf & ? & ? & ? & ? & hf); subst.
    eapply sll_frnp_grammar_nullable_path in hf; eauto.
    firstorder.
  Qed.
  
  Lemma sllc_neq_SpLeftRecursion :
    forall (g    : grammar)
           (pm   : rhs_map)
           (cm   : closure_map)
           (pair : nat * nat)
           (a    : Acc lex_nat_pair pair)
           (vi   : NtSet.t)
           (sp   : sll_subparser)
           (hk   : sll_sp_pushes_from_keyset pm sp)
           (a'   : Acc lex_nat_pair (sll_meas pm vi sp))
           (x    : nonterminal),
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sll_unavailable_nts_invar g vi sp
      -> pair = sll_meas pm vi sp
      -> sllc pm cm vi sp hk a' <> inl (SpLeftRecursion x).
  Proof.
    intros g pm cm pair a'.
    induction a' as [pair hlt IH].
    intros vi sp hk a x hn hp hu ? hs; subst.
    apply sllc_error_cases in hs.
    destruct hs as [hsr [hs | [sps [vi' [hs [crs [heq heq']]]]]]]; subst.
    - eapply sllCstep_never_finds_left_recursion; eauto. 
    - apply aggrClosureResults_error_in_input in heq'.
      eapply dmap_in in heq'; eauto.
      destruct heq' as [sp' [hi [hi' heq]]].
      eapply IH with (sp := sp'); eauto.
      + eapply sllCstep_meas_lt; eauto.
      + eapply sllCstep_preserves_unavailable_nts_invar; eauto.
  Qed.
  
  Lemma sllClosure_neq_SpLeftRecursion :
    forall g pm cm sps hk x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sllClosure pm cm sps hk <> inl (SpLeftRecursion x).
  Proof.
    intros g pm cm sps hk x hn hp hc; unfold sllClosure in hc.
    apply aggrClosureResults_error_in_input in hc.
    eapply dmap_in in hc; eauto; sis.
    destruct hc as [[pr (fr, frs)] [hi [_ hs]]].
    eapply sllc_neq_SpLeftRecursion; eauto.
    - apply lex_nat_pair_wf.
    - apply sll_unavailable_nts_empty.
  Qed.

    Lemma sllMoveSp_never_returns_SpLeftRecursion :
    forall t sp x,
      sllMoveSp t sp <> MoveError (SpLeftRecursion x).
  Proof.
    intros t sp x; unfold not; intros hm.
    unfold sllMoveSp in hm; dms; tc.
  Qed.

  Lemma sllMove_never_returns_SpLeftRecursion :
    forall t sps x,
      sllMove t sps <> inl (SpLeftRecursion x).
  Proof.
    intros t sps x; unfold not; intros hm.
    unfold sllMove in hm.
    apply aggrMoveResults_error_in_input in hm.
    apply in_map_iff in hm.
    destruct hm as [sp [hm hi]].
    eapply sllMoveSp_never_returns_SpLeftRecursion; eauto.
  Qed.

  Lemma sllTarget_neq_SpLeftRecursion :
    forall g pm cm a sps hk x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sllTarget pm cm a sps hk <> inl (SpLeftRecursion x).
  Proof.
    intros g pm cm a sps hk x hn hp ht.
    apply sllTarget_cases in ht.
    destruct ht as [hm | [sps' [hk' [hm hc]]]].
    - eapply sllMove_never_returns_SpLeftRecursion; eauto.
    - eapply sllClosure_neq_SpLeftRecursion; eauto. 
  Qed.
  
  Lemma sllPredict'_neq_SpLeftRecursion :
    forall g pm cm ts sps ca hk hc ca' x,
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sllPredict' pm cm sps ts ca hk hc <> (PredError (SpLeftRecursion x), ca').
  Proof.
    intros g pm cm ts; induction ts as [| (a,l) ts IH];
      intros sps ca hk hc ca' x hn hp hl; sis.
    - inv hl; eapply sllHandleFinalSubparsers_never_returns_error; eauto.
    - destruct sps as [| sp sps]; tc; dm; tc.
      apply sllPredict'_cont_cases in hl.
      destruct hl as [ [sps'' [hf hl]] | [ht | [sps'' [ht hl]]]].
      + pose proof hf as hf' ; apply hc in hf'.
        destruct hf' as [hk' ht].
        eapply IH in hl; eauto.
      + eapply sllTarget_neq_SpLeftRecursion; eauto.
      + eapply IH in hl; eauto.
  Qed. 
  
  Lemma sllStartState_neq_SpLeftRecursion :
    forall g pm cm x x',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sllStartState pm cm x <> inl (SpLeftRecursion x').
  Proof.
    intros g pm cm x x' hn hp hss.
    eapply sllClosure_neq_SpLeftRecursion; eauto.
  Qed.

  Lemma sllPredict_neq_SpLeftRecursion :
    forall g pm cm x x' ts ca hc ca',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> sllPredict pm cm x ts ca hc <> (PredError (SpLeftRecursion x'), ca').
  Proof.
    intros g pm cm x x' ts ca hc ca' hn hp hs.
    apply sllPredict_cases in hs.
    destruct hs as [hss | [sps [hss hs]]].
    - eapply sllStartState_neq_SpLeftRecursion; eauto. 
    - eapply sllPredict'_neq_SpLeftRecursion; eauto. 
  Qed.  

  (* Putting it all together *)
  Lemma sllPredict_never_returns_error :
    forall g pm cm x ts ca hc e ca',
      no_left_recursion g
      -> rhs_map_correct pm g
      -> closure_map_correct g cm
      -> sllPredict pm cm x ts ca hc <> (PredError e, ca').
  Proof.
    intros g pm cm x ts ca hc e ca' hn hp hm hs; destruct e as [| x'].
    - eapply sllPredict_neq_SpInvalidState; eauto.
    - eapply sllPredict_neq_SpLeftRecursion; eauto.
  Qed.
  
  Theorem adaptivePredict_neq_error :
    forall gr hw rm cm fr pre vs x suf frs ts ca hc hk e ca',
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr (fr, frs)
      -> fr = Fr pre vs (NT x :: suf)
      -> adaptivePredict gr hw rm cm pre vs x suf frs ts ca hc hk <> (PredError e, ca').
  Proof.
    intros gr hw rm cm fr pre vs x suf frs ts ca hc hk e ca' hn hp hc' hw' ? ha; subst.
    unfold adaptivePredict in ha.
    dmeq hsll; dms; tc; inv ha.
    - eapply llPredict_never_returns_error; eauto.
    - eapply sllPredict_never_returns_error; eauto.
  Qed.
  
End SllPredictionErrorFreeFn.
