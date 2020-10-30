Require Import Bool List String.
Require Import CoStar.Lex.
Require Import CoStar.Parser_error_free.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
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
    forall g pm cm cr ce frs o x suf rhs w ca hc hk ca',
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> suffix_stack_wf g (cr, frs)
      -> adaptivePredict pm cm o x suf frs w ca hc hk = (PredSucc rhs, ca')
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g pm cm ? ? frs o x suf rhs w ca hci hk ca'
           ? ? hn hpm [hms hmc] hw hp hg; subst; sis.
    apply gamma_recognize_nonterminal_head in hg.
    destruct hg as (rhs' & wp & wms & ? & hi' & hg & hg'); subst.
    apply gamma_recognize_split in hg'.
    destruct hg' as (wm & ws & ? & hg' & hg''); subst.
    eapply adaptivePredict_succ_at_most_one_rhs_applies in hp; eauto;
    subst; repeat (apply gamma_recognize_app; auto).
  Qed.

  Lemma push_ambig_preserves_ussr :
    forall g pm cm cr ce o x suf frs w ca hc hk rhs ca',
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> production_map_correct pm g
      -> suffix_stack_wf g (cr, frs)
      -> adaptivePredict pm cm o x suf frs w ca hc hk = (PredAmbig rhs, ca')
      -> gamma_recognize g (unprocStackSyms (cr, frs)) w
      -> gamma_recognize g (unprocStackSyms (ce, cr :: frs)) w.
  Proof.
    intros g pm cm ? ? o x suf frs w ca hc hk rhs ca'
           ? ? hn hp hw hl hg; subst; sis.
    eapply adaptivePredict_ambig_rhs_unproc_stack_syms; eauto.
  Qed.

  Lemma step_preserves_ussr :
    forall g pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca' hc hk,
      no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> suffix_stack_wf g ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> step pm cm ps ss ts vi un ca hc hk = StepK ps' ss' ts' vi' un' ca'
      -> gamma_recognize g (unprocStackSyms ss') ts'.
  Proof.
    intros g pm cm ps ps' ss ss' ts ts' vi vi' un un' ca ca'
           hc hk hn hp hm hw hr hs.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_ussr; eauto.
    - eapply consume_preserves_ussr; eauto.
    - eapply push_succ_preserves_ussr; eauto.
    - eapply push_ambig_preserves_ussr; eauto.
  Qed.

  Lemma ussr__step_neq_reject :
    forall g pm cm ps ss ts vi un ca hc hk s,
      no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> step pm cm ps ss ts vi un ca hc hk <> StepReject s.
  Proof.
    intros g pm cm ps ss ts vi un ca hc hk s
           hn hp hm hw hg hs.
    unfold step in hs; dmeqs h; tc; inv hs; sis.
    - inv hg.
    - inversion hg as [| ? ? wpre wsuf hs hg' heq heq']; subst; clear hg.
      inv hs; inv heq'.
    - inversion hg as [| ? ? wpre wsuf hs hg' heq heq']; subst; clear hg.
      inv hs; inv heq'; tc.
    - inversion hg as [| ? ? wpre wsuf hs hg' heq heq']; subst; clear hg.
      inv_sr hs  hi hg''.
      (* lemma? *)
      apply hp in hi. destruct hi as [yss [hm' hi]].
      apply NMF.find_mapsto_iff in hm'; tc.
    - eapply ussr_adaptivePredict_neq_reject; eauto.
      eapply frames_wf__suffix_frames_wf; eauto.
  Qed.

  Lemma ussr__multistep_doesn't_reject' :
    forall (g      : grammar)
           (pm     : production_map)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results pm cm ca)
           (hk     : stack_pushes_from_keyset pm ss)
           (a'     : Acc lex_nat_triple (meas pm ss ts vi))
           (s      : string),
      tri = meas pm ss ts vi
      -> no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> gamma_recognize g (unprocStackSyms ss ) ts
      -> multistep pm cm ps ss ts vi un ca hc hk a' <> Reject s.
  Proof.
    intros g pm cm tri a'.
    induction a' as [tri hlt IH].
    intros ps ss ts vi un ca hc hk a s ? hn hp hcm hw hg hm; subst. 
    apply multistep_cases in hm.
    destruct hm as [hs | (ps' & ss' & ts' & vi' & un' & ca' & hc' & hk' & a'' & hs & hm)]. 
    - eapply ussr__step_neq_reject; eauto.
    - eapply IH with (y := meas pm ss' ts' vi'); eauto. 
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto.
      + eapply step_preserves_ussr with (ca := ca); eauto.
        eapply stacks_wf__suffix_stack_wf; eauto.
  Qed.

  Lemma ussr_implies_multistep_doesn't_reject :
    forall (g      : grammar)
           (pm     : production_map)
           (cm     : closure_map)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (ts     : list token)
           (vi     : NtSet.t)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results pm cm ca)
           (hk     : stack_pushes_from_keyset pm ss)
           (a      : Acc lex_nat_triple (meas pm ss ts vi))
           (s      : string),
      no_left_recursion g
      -> production_map_correct pm g
      -> closure_map_correct g cm
      -> stacks_wf g ps ss
      -> gamma_recognize g (unprocStackSyms ss) ts
      -> multistep pm cm ps ss ts vi un ca hc hk a <> Reject s.
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
    - apply mkProductionMap_correct.
    - apply mkClosureMap_result_correct.
    - (* lemma *)
      rew_nil_r w; eauto.
  Qed.

  Theorem parse_complete :
    forall (g  : grammar)
           (x  : nonterminal)
           (w  : list token)
           (t  : tree),
      no_left_recursion g
      -> sym_derivation g (NT x) w t
      -> exists (t' : tree),
          parse g x w = Accept t'
          \/ parse g x w = Ambig t'.
  Proof.
    intros g x w v hn hg.
    destruct (parse g x w) as [v' | v' | s | e] eqn:hp; eauto.
    - exfalso.
      apply sym_derivation__sym_recognize in hg.
      apply valid_derivation_implies_parser_doesn't_reject in hp; auto.
    - exfalso; destruct e.
      + eapply parse_never_reaches_invalid_state; eauto.
      + eapply parse_doesn't_find_left_recursion_in_non_left_recursive_grammar; eauto.
      + eapply parse_never_returns_prediction_error; eauto.
  Qed.

End ParserCompleteFn.
