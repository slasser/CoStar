Require Import SLLPrediction.

Module SllOptimizationSoundFn (Import D : Defs.T).

  Module Export SLLP := SllPredictionFn D.

End SllOptimizationSoundFn.

        
(*
Lemma sll'_ll'_equiv_succ :
    forall g cm sps sps' ts c c' ys,
      sllPredict' g cm sps ts c = (PredSucc ys, c')
      -> llPredict' g sps' ts = PredReject
         \/llPredict' g sps' ts = PredSucc ys.
  Proof.
    intros g cm sps sps' ts c c' ys hs.
    unfold sllPredict' in hs.
    induction ts as [| t ts IH].
    - destruct sps as [| sp sps]; tc.
      destruct (allPredictionsEqual sp sps) eqn:ha.
      + (* SLL all equal *)
        inv hs.
        destruct sps' as [| sp' sps']; auto.
        right. simpl.
        (* an invariant relating the LL and SLL subaparsers
           should prove that SLL all equal -> LL all equal *)
  Abort.

  (* Equivalence of LL and SLL *)
(*
Lemma sll'_ll'_equiv_succ :
  forall g cm sps sps' ts c c' ys,
    
sllPredict' g cm sps ts c = (PredSucc ys, c')
    -> llPredict' g sps' ts = PredReject
       \/llPredict' g sps' ts = PredSucc ys.
Proof.
  intros g cm sps sps' ts c c' ys hs.
  unfold SLL.sllPredict' in hs.
  induction ts as [| t ts IH].
  - destruct sps as [| sp sps]; tc.
    destruct (SLL.allPredictionsEqual sp sps) eqn:ha.
    + (* SLL all equal *)
      destruct sps' as [| sp' sps']; auto.
      right.
Abort.

Lemma sll_ll_equiv_succ :
  forall g cm fr frs x suf ts c c' ys,
    no_left_recursion g
    -> suffix_stack_wf g (fr, frs)
    -> fr = SF (NT x :: suf)
    -> SLL.sllPredict g cm x ts c = (PredSucc ys, c')
    -> llPredict g x (fr, frs) ts = PredSucc ys.
Proof.
  intros g cm fr frs x suf ts c c' ys hn hw ? hs; subst.
  unfold SLL.sllPredict in hs.
  destruct (SLL.startState g cm x) as [e | sps] eqn:hss; tc.
  unfold llPredict.
  destruct (startState g x _) as [e | sps'] eqn:hss'.
  - (* lemma *)
    destruct e as [ | x'].
    + exfalso; eapply startState_never_returns_SpInvalidState; eauto.
    + exfalso; eapply closure_never_finds_left_recursion; eauto.
  - (* what do we know at this point?
         - sllPredict' succeeded, so there must be an sp in sps with label ys
         - there must also be an sp' in sps' with label ys *)
    admit.
Abort.

Lemma adaptivePredict_equiv_llPredict :
  forall g cm x stk ts c c' r,
    SLL.adaptivePredict g cm x stk ts c = (r, c')
    -> llPredict g x stk ts = r.
Proof.
  intros g cm x stk ts c c' r ha.
  unfold SLL.adaptivePredict in ha.
  destruct (SLL.sllPredict _ _ _ _ _) as (r', c'') eqn:hs.
  destruct r' as [ys | ys | | e]; inv ha; auto.
  - (* PredSucc *)
    admit.
  - admit.
  - admit.
Admitted.
*)
*)
