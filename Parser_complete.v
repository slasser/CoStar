Require Import Bool List String.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Prediction_complete.
Require Import GallStar.Parser.
Require Import GallStar.Parser_sound.
Require Import GallStar.Parser_error_free.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module ParserCompleteFn (Import D : Defs.T).

  Module Export PEF := ParserErrorFreeFn D.

  (* To do: encapsulate "gamma_recognize unprocStackSyms..." in a definition *)
  Lemma return_preserves_ussr :
    forall g ce cr cr' frs o o' x suf w,
      ce     = SF o' []
      -> cr  = SF o (NT x :: suf)
      -> cr' = SF o suf
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w
      -> gamma_recognize g (unprocStackSyms (cr', frs)) w.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma consume_preserves_ussr :
    forall g fr fr' frs suf o a l w,
      fr     = SF o (T a :: suf)
      -> fr' = SF o suf
      -> gamma_recognize g (unprocStackSyms (fr, frs)) ((a, l) :: w)
      -> gamma_recognize g (unprocStackSyms (fr', frs)) w.
  Proof.
    intros g ? ? frs suf o a l w ? ? hg; subst; sis.
    apply gamma_recognize_terminal_head in hg.
    destruct hg as (? & ? & heq & ?); inv heq; auto.
  Qed.

  Lemma push_succ_preserves_ussr :
    forall g cr ce frs o x suf rhs w,
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> llPredict g x (cr, frs) w = PredSucc rhs
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g ? ? frs o x suf rhs w ? ? hn hw hl hg; subst; sis.
    apply gamma_recognize_nonterminal_head in hg.
    destruct hg as (rhs' & wp & wms & ? & hi' & hg & hg'); subst.
    apply gamma_recognize_split in hg'.
    destruct hg' as (wm & ws & ? & hg' & hg''); subst.
    eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto; subst; sis; repeat (apply gamma_recognize_app; auto).
  Qed.

  Lemma push_ambig_preserves_ussr :
    forall g cr ce frs o x suf rhs w,
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> llPredict g x (cr, frs) w = PredAmbig rhs
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g ? ? frs o x suf rhs w ? ? hn hw hl hg; subst; sis.
    eapply llPredict_ambig_rhs_unproc_stack_syms in hl; eauto.
    sis; auto.
  Qed.

  Lemma step_preserves_ussr :
    forall g ps ps' ss ss' ts ts' av av' un un',
      no_left_recursion g
      -> suffix_stack_wf g ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> step g ps ss ts av un = StepK ps' ss' ts' av' un'
      -> gamma_recognize g (unprocStackSyms ss') ts'.
  Proof.
    intros g ps ps' ss ss' ts ts' av av' un un' hn hw hr hs.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_ussr; eauto.
    - eapply consume_preserves_ussr; eauto.
    - eapply push_succ_preserves_ussr; eauto.
    - eapply push_ambig_preserves_ussr; eauto.
  Qed.

  Lemma ussr__multistep_doesn't_reject' :
    forall (g      : grammar)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (u      : bool)
           (a'     : Acc lex_nat_triple (meas g s_stk ts av))
           (s      : string),
      tri = meas g s_stk ts av
      -> no_left_recursion g
      -> stacks_wf g p_stk s_stk
      -> gamma_recognize g (unprocStackSyms s_stk) ts
      -> multistep g p_stk s_stk ts av u a' <> Reject s.
  Proof.
    intros g tri a.
    induction a as [tri hlt IH].
    intros ps ss ts av u a' s ? hn hw hg; unfold not; intros hm; subst.
    apply multistep_reject_cases in hm.
    destruct hm as [hs | (ps' & ss' & ts' & av' & u' & a'' & hs & hm)]. 
    - (* lemma *)
      clear hlt IH.
      unfold step in hs; dmeqs h; tc; inv hs; sis.
      + inv hg.
      + inv hg.
        inv H2.
        inv H1.
      + inv hg. 
        inv H2. 
        inv H1. 
        tc.
      + eapply ussr_llPredict_neq_reject; eauto.
        eapply frames_wf__suffix_frames_wf; eauto.
      + inv hg. 
        inv H1.
        apply lhs_mem_allNts_true in H0. 
        tc.
    - eapply IH with (y := meas g ss' ts' av'); eauto. 
      + eapply step_meas_lt; eauto.
      + eapply step_preserves_stacks_wf_invar; eauto.
      + eapply step_preserves_ussr; eauto.
        eapply stacks_wf__suffix_stack_wf; eauto.
  Qed.

  Lemma ussr_implies_multistep_doesn't_reject :
    forall (g      : grammar)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (u      : bool)
           (a      : Acc lex_nat_triple (meas g s_stk ts av))
           (s      : string),
      no_left_recursion g
      -> stacks_wf g p_stk s_stk
      -> gamma_recognize g (unprocStackSyms s_stk) ts
      -> multistep g p_stk s_stk ts av u a <> Reject s.
  Proof.
    intros; eapply ussr__multistep_doesn't_reject'; eauto.
  Qed.

  Theorem valid_derivation_implies_parser_doesn't_reject :
    forall g ys w s,
      no_left_recursion g
      -> gamma_recognize g ys w
      -> parse g ys w <> Reject s.
  Proof.
    intros g ys w s hn hg; unfold not; intros hp.
    unfold parse in hp.
    eapply ussr_implies_multistep_doesn't_reject; eauto; simpl; apps.
  Qed.

  Theorem parse_complete :
    forall (g  : grammar)
           (ys : list symbol)
           (w  : list token)
           (v  : forest),
      no_left_recursion g
      -> gamma_derivation g ys w v
      -> exists (v' : forest),
          parse g ys w = Accept v'
          \/ parse g ys w = Ambig v'.
  Proof.
    intros g ys w v hn hg.
    destruct (parse g ys w) as [v' | v' | s | e] eqn:hp; eauto.
    - exfalso. 
      apply gamma_derivation__gamma_recognize in hg.
      apply valid_derivation_implies_parser_doesn't_reject in hp; auto.
    - exfalso.
      apply parser_terminates_without_error in hp; auto.
  Qed.

  (* Completeness theorem for unambiguous derivations *)
  Theorem parse_complete_unique_derivation :
    forall (g  : grammar)
           (ys : list symbol)
           (w  : list token)
           (v  : forest),
      no_left_recursion g
      -> gamma_derivation g ys w v
      -> (forall v', gamma_derivation g ys w v' -> v' = v)
      -> parse g ys w = Accept v.
  Proof.
    intros g ys w v hn hg hu.
    apply parse_complete in hg; auto.
    destruct hg as (v' & [hp | hp]); pose proof hp as hp'.
    - apply parse_sound_unambig in hp; auto.
      destruct hp as (hg & _).
      apply hu in hg; subst; auto.
    - exfalso.
      apply parse_sound_ambig in hp; auto.
      destruct hp as (hg' & (v'' & hg & hneq)).
      apply hu in hg; apply hu in hg'; subst; tc.
  Qed.

  (* Completeness theorem for ambiguous derivations *)
  Theorem parse_complete_ambiguous_derivations :
    forall (g    : grammar)
           (ys   : list symbol)
           (w    : list token)
           (v v' : forest),
      no_left_recursion g
      -> gamma_derivation g ys w v
      -> gamma_derivation g ys w v'
      -> v <> v'
      -> exists v'',
          parse g ys w = Ambig v''.
  Proof.
    intros g ys w v v' hn hg hg'' hneq.
    pose proof hg as hg'.
    apply parse_complete in hg; auto.
    destruct hg as (v'' & [hp | hp]); eauto.
    exfalso.
    apply parse_sound_unambig in hp; auto.
    destruct hp as (hg & ha).
    apply ha in hg'; apply ha in hg''; subst; tc.
  Qed.

End ParserCompleteFn.
