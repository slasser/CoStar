Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Parser_error_free.
Require Import GallStar.Tactics.

Lemma multistep_complete' :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (wsuf w : list token)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest)
         (sr     : step_result)
         (hs     : step g (Pst av stk wsuf u) = sr),
    tri = meas g (Pst av stk wsuf u)
    -> no_left_recursion g
    -> stack_wf g stk
    -> unavailable_nts_invar g (Pst av stk wsuf u)
    -> unique_gamma_derivation g (bottomFrameSyms stk) w v
    -> match sr as res return (step g (Pst av stk wsuf u) = res -> parse_result)
       with
       | StepAccept sv =>
         fun _ => if u then Accept sv else Ambig sv
       | StepReject s =>
         fun _ => Reject s
       | StepK st' =>
         fun hs => multistep g st' (StepK_st_acc g _ st' a' hs)
       | StepError s => fun _ => Error s
       end hs = Accept v.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros av stk wsuf w u a' v sr hs heq hn hw hu hun.
  destruct sr as [v' | s | [av' stk' wsuf' u'] | s]; subst.
  - apply step_StepAccept_facts in hs.
    destruct hs as [[o [pre [v'' [heq heq']]]] hnil]; subst.
    (* we need an invariant stating that the stack 
       captures a unique derivation *)
    admit.
  - admit.
  - rewrite multistep_unfold.
    eapply IH; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_unavailable_nts_invar; eauto.
    + apply step_preserves_bottomFrameSyms_invar in hs.
      rewrite <- hs; eauto.
  - (* lemma *)
    exfalso.
    destruct s.
    + eapply stack_wf_no_invalid_state; eauto.
    + apply step_left_recursion_detection_sound in hs; auto.
      eapply hn; eauto.
    + destruct p.
      * eapply step_never_returns_SpInvalidState; eauto.
        simpl; auto.
      * eapply step_never_returns_SpLeftRecursion; eauto.
        simpl; auto.
Admitted.

Lemma multistep_complete :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (st     : parser_state)
         (w : list token)
         (a'     : Acc lex_nat_triple (meas g st))
         (v      : forest),
    tri = meas g st
    (* you'll likely need some extra parser invariants here *)
    -> unique_gamma_derivation g (bottomFrameSyms st.(stack)) w v
    -> multistep g st a' = Accept v.
Proof.
  intros.
  rewrite multistep_unfold.
  eapply multistep_complete'; eauto.
  intros g tri a.
  induction a as [tri hlt IH].
  intros st w a' v ? hu; subst.
  rewrite multistep_unfold.
  destruct (step g st).
Lemma multistep_complete :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (wsuf w : list token)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest),
    tri = meas g (Pst av stk wsuf u)
    (* you'll likely need some extra parser invariants here *)
    -> unique_gamma_derivation g (bottomFrameSyms stk) w v
    -> multistep g (Pst av stk wsuf u) a' = Accept v.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros av stk wsuf w u a' v ? hu; subst.
  rewrite multistep_unfold.
  pose proof (multistep_unfold_ex g (Pst av stk wsuf u) a') as hm.
  destruct hm as [? heq'].
  destruct x.
  simpl in heq'.
  destruct (step g _).
  dmeq hs.
  apply multistep_accept_cases.
  unfold multistep.
  apply multistep_accept_cases in hm.
  destruct hm as [hf | he].
  - apply step_StepAccept_facts in hf.
    destruct hf as [[xo [rpre [v' [heq]]]] heq']; subst.
    unfold bottomFrameSyms; simpl; rewrite app_nil_r.
    eapply stack_prefix_derivation_final; eauto.
  - destruct he as [st' [a'' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_stack_prefix_derivation; eauto.
  
Lemma multistep_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest),
    tri = meas g (Pst av stk wsuf u)
    -> stack_wf g stk
    -> stack_prefix_derivation g stk wsuf w
    -> multistep g (Pst av stk wsuf u) a' = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v.
Proof.
  
hd : gamma_derivation g ys w v
  hu : forall v' : forest, gamma_derivation g ys w v' -> v = v'
  ============================
  multistep g (mkInitState g ys w)
    (Lex.lex_nat_triple_wf (meas g (mkInitState g ys w))) = 
  Accept v

Theorem parser_complete :
  forall g ys w v,
    unique_gamma_derivation g ys w v -> parse g ys w = Accept v.
Proof.
  intros g ys w v [hd hu].
  unfold parse.
  