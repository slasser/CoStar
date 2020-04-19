Require Import Bool List String.
Require Import GallStar.Lex.
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
    forall g cm cr ce frs o x suf rhs w ca ca',
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> suffix_stack_wf g (cr, frs)
      -> adaptivePredict g cm x (cr, frs) w ca = (PredSucc rhs, ca')
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g cm ? ? frs o x suf rhs w ca ca'
           ? ? hn [hs hc] hc' hw hp hg; subst; sis.
    apply gamma_recognize_nonterminal_head in hg.
    destruct hg as (rhs' & wp & wms & ? & hi' & hg & hg'); subst.
    apply gamma_recognize_split in hg'.
    destruct hg' as (wm & ws & ? & hg' & hg''); subst.
    eapply adaptivePredict_succ_at_most_one_rhs_applies in hp; eauto;
    subst; repeat (apply gamma_recognize_app; auto).
  Qed.

  Lemma push_ambig_preserves_ussr :
    forall g cm cr ce frs o x suf rhs w ca ca',
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> adaptivePredict g cm x (cr, frs) w ca = (PredAmbig rhs, ca')
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g cm ? ? frs o x suf rhs w ca ca'
           ? ? hn hw hl hg; subst; sis.
    eapply adaptivePredict_ambig_rhs_unproc_stack_syms; eauto.
  Qed.

  Lemma step_preserves_ussr :
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca',
      no_left_recursion g
      -> closure_map_correct g cm
      -> cache_stores_target_results g cm ca
      -> suffix_stack_wf g ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> gamma_recognize g (unprocStackSyms ss') ts'.
  Proof.
    intros g cm ps ps' ss ss' ts ts' av av' un un' ca ca'
           hn hm hc hw hr hs.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_ussr; eauto.
    - eapply consume_preserves_ussr; eauto.
    - eapply push_succ_preserves_ussr; eauto.
    - eapply push_ambig_preserves_ussr; eauto.
  Qed.

  Lemma ussr__multistep_doesn't_reject' :
    forall (g      : grammar)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a'     : Acc lex_nat_triple (meas g ss ts av))
           (s      : string),
      tri = meas g ss ts av
      -> no_left_recursion g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> gamma_recognize g (unprocStackSyms ss ) ts
      -> multistep g cm ps ss ts av un ca hc a' <> Reject s.
  Proof.
    intros g cm tri a'.
    induction a' as [tri hlt IH].
    intros ps ss ts av un ca hc a s ? hn hcm hw hg hm; subst. 
    apply multistep_reject_cases in hm.
    destruct hm as [hs | (ps' & ss' & ts' & av' & un' & ca' & hc' & a'' & hs & hm)]. 
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
      + eapply ussr_adaptivePredict_neq_reject; eauto.
        eapply frames_wf__suffix_frames_wf; eauto. 
      + inv hg. 
        inv H1.
        apply lhs_mem_allNts_true in H0. 
        tc.
    - eapply IH with (y := meas g ss' ts' av'); eauto. 
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto.
      + eapply step_preserves_ussr with (ca := ca); eauto.
        eapply stacks_wf__suffix_stack_wf; eauto.
  Qed.

  Lemma ussr_implies_multistep_doesn't_reject :
    forall (g      : grammar)
           (cm     : closure_map)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (av     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a      : Acc lex_nat_triple (meas g ss ts av))
           (s      : string),
      no_left_recursion g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> multistep g cm ps ss ts av un ca hc a <> Reject s.
  Proof.
    intros; eapply ussr__multistep_doesn't_reject'; eauto.
  Qed.

  Theorem valid_derivation_implies_parser_doesn't_reject :
    forall g x w s,
      no_left_recursion g
      -> sym_recognize g (NT x) w
      -> parse g x w <> Reject s.
  Proof.
    intros g x w s hn hg hp; unfold parse in hp.
    eapply ussr_implies_multistep_doesn't_reject; eauto; simpl; apps.
    - apply mkClosureMap_result_correct.
    - (* lemma *)
      rew_nil_r w; eauto.
  Qed.

  Theorem parse_complete :
    forall (g  : grammar)
           (x  : nonterminal)
           (w  : list token)
           (v  : forest),
      no_left_recursion g
      -> gamma_derivation g [NT x] w v
      -> exists (v' : forest),
          parse g x w = Accept v'
          \/ parse g x w = Ambig v'.
  Proof.
    intros g x w v hn hg.
    destruct (parse g x w) as [v' | v' | s | e] eqn:hp; eauto.
    - exfalso. 
      apply gamma_derivation__gamma_recognize in hg.
      apply valid_derivation_implies_parser_doesn't_reject in hp; auto.
    (* clean this up *)
      inv hg. inv H3. rew_anr; auto.
    - exfalso.
      apply parse_terminates_without_error in hp; auto.
  Qed.

  (* Completeness theorem for unambiguous derivations *)
  Theorem parse_complete_unique_derivation :
    forall (g  : grammar)
           (x  : nonterminal)
           (w  : list token)
           (v  : forest),
      no_left_recursion g
      -> gamma_derivation g [NT x] w v
      -> (forall v', gamma_derivation g [NT x] w v' -> v' = v)
      -> parse g x w = Accept v.
  Proof.
    intros g x w v hn hg hu.
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
           (x    : nonterminal)
           (w    : list token)
           (v v' : forest),
      no_left_recursion g
      -> gamma_derivation g [NT x] w v
      -> gamma_derivation g [NT x] w v'
      -> v <> v'
      -> exists v'',
          parse g x w = Ambig v''
          /\ gamma_derivation g [NT x] w v''.
  Proof.
    intros g x w v v' hn hg hg'' hneq.
    pose proof hg as hg'.
    apply parse_complete in hg; auto.
    destruct hg as (v'' & [hp | hp]); eauto.
    - exfalso.
      apply parse_sound_unambig in hp; auto.
      destruct hp as (hg & ha).
      apply ha in hg'; apply ha in hg''; subst; tc.
    - eexists; split; eauto.
      eapply parse_sound_ambig; eauto.
  Qed.

End ParserCompleteFn.
