Require Import Bool List String.
Require Import CoStar.Lex.
Require Import CoStar.Parser_error_free.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module ParserCompleteFn (Import D : Defs.T).

  Module Export PEF := ParserErrorFreeFn D.

  Lemma push_succ_preserves_sas :
    forall gr hw rm cm cr ce frs pre vs x suf rhs w ca hc hk ca',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr (cr, frs)
      -> adaptivePredict gr hw rm cm pre vs x suf frs w ca hc hk = (PredSucc rhs, ca')
      -> stack_accepts_suffix gr (cr, frs) w
      -> stack_accepts_suffix gr (ce, cr :: frs) w.
  Proof.
    intros gr hw rm cm cr ce frs pre vs x suf rhs w ca hc hk ca' ? ? hn hr hc' hw' ha hs; subst; sis.
    destruct hc' as [hcs hcc].
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    destruct vs_suf as (v_suf, vs_suf).
    eapply svd_inv_nonterminal_head with
        (x   := x)
        (v'  := v_suf)
        (vs' := vs_suf)
        (heq := eq_refl) in hd; eauto.
    destruct hd as (wpre' & wpre'' & heq & hh & ht); subst.
    inv_sv hh hm hvs hp; s_inj.
    pose proof hm as hm'.
    apply pm_mapsto_in in hm.
    eapply adaptivePredict_succ_at_most_one_rhs_applies in ha; eauto; subst.
    - exists wpre'; exists (wpre'' ++ wsuf); eexists; repeat split; eauto; apps.
      exists wpre''; exists wsuf; repeat eexists; repeat split; eauto.
    - red.
      exists wpre'; exists (wpre'' ++ wsuf); eexists; repeat split; eauto; apps.
      repeat eexists; repeat split; eauto.
  Qed.

  Lemma push_ambig_preserves_sas :
    forall gr hw rm cm cr ce pre vs x suf frs w ca hc hk rhs ca',
      cr    = Fr pre vs (NT x :: suf)
      -> ce = Fr [] tt rhs
      -> no_left_recursion gr
      -> rhs_map_correct rm gr
      -> stack_wf gr (cr, frs)
      -> adaptivePredict gr hw rm cm pre vs x suf frs w ca hc hk = (PredAmbig rhs, ca')
      -> stack_accepts_suffix gr (cr, frs) w
      -> stack_accepts_suffix gr (ce, cr :: frs) w.
  Proof.
    intros gr hw rm cm cr ce pre vs x suf frs w ca hc hk rhs ca' ? ? hn hr hw' ha hs; subst.
    eapply adaptivePredict_ambig_rhs_unproc_stack_syms; eauto.
  Qed.
  
  Lemma step_preserves_sas :
    forall gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca' hc hk,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> step gr hw rm cm sk ts vi un ca hc hk = StepK sk' ts' vi' un' ca'
      -> stack_accepts_suffix gr sk' ts'. 
  Proof.
    intros gr hw rm cm sk sk' ts ts' vi vi' un un' ca ca'
           hc hk hn hp hm hw' hr hs.
    unfold step in hs; dmeqs h; tc; inv hs.
    - appl_fpaa; eapply return_preserves_sas; eauto; auto.
    - eapply consume_preserves_sas; eauto; auto.
    - eapply push_succ_preserves_sas; eauto.
    - eapply push_ambig_preserves_sas; eauto.
  Qed.

  Lemma ussr__step_neq_reject :
    forall gr hw rm cm sk ts vi un ca hc hk s,
      no_left_recursion gr
      -> rhs_map_correct rm gr
      -> closure_map_correct gr cm
      -> stack_wf gr sk
      -> stack_accepts_suffix gr sk ts
      -> step gr hw rm cm sk ts vi un ca hc hk <> StepReject s.
  Proof.
    intros gr hw rm cm sk ts vi un ca hc hk s
           hn hr hm hw' hsas hs.
    unfold step in hs; dmeqs h; tc; inv hs; sis.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & heq'); subst; sis; rew_anr; subst.
      inv hd.
    - pose proof hsas as hsas'.
      destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      destruct hl as (wsuf' & wsuf'' & vs_suf' & p & f & heq & hd' & hm' & hp' & hl); subst.
      appl_fpaa.
      eapply sas_failed_predicate_contra; eauto.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      symmetry in heq; apply app_eq_nil in heq; destruct heq; subst.
      eapply svd_terminal_head_contra; eauto.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl).
      apply svd_inv_terminal_head in hd.
      destruct hd as (v & ts' & heq'); subst; sis.
      inv_cons_tokens_eq; tc.
    - destruct hsas as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
      destruct vs_suf as (v_suf, vs_suf).
      eapply svd_inv_nonterminal_head with
          (v'  := v_suf)
          (vs' := vs_suf)
          (heq := eq_refl) in hd; eauto.
      destruct hd as (ts' & ts'' & heq & hh & ht); subst.
      inv_sv hh hm' hd' hp'.
      (* lemma *)
      red in hr.
      destruct hr as (_ & _ & hrc).
      red in hrc.
      apply pm_mapsto_in in hm'.
      apply hrc in hm'.
      destruct hm' as (yss & hm' & hi).
      apply NMF.find_mapsto_iff in hm'; tc.
    - admit.
  Admitted.

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
 *)
  
End ParserCompleteFn.
