Require Import List String.
Require Import CoStar.Defs.
Require Import CoStar.Parser.
Require Import CoStar.Parser_sound.
Require Import CoStar.Parser_error_free.
Require Import CoStar.Parser_complete.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

Module Make (Export D : Defs.T).

  Module Export ParserAndProofs := ParserCompleteFn D.

  (* Soundness theorems for unique 
     and ambiguous derivations *)

  Theorem parse_sound__unique_derivation :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (v  : tree),
      no_left_recursion g
      -> parse g x ts = Accept v
      -> sym_derivation g (NT x) ts v
         /\ (forall v',
                sym_derivation g (NT x) ts v'
                -> v' = v).
  Proof.
    intros g x ts v hn hp.
    unfold parse in hp.
    eapply multistep_sound_unambig with (w := ts) in hp; eauto.
    - destruct hp as [hg hu]; unfold bottomFrameSyms in *; sis.
      (* lemma *)
      inv hg. inv H5; rew_anr.
      split; auto.
      intros v' hs.
      assert (hg : gamma_derivation g [NT x] wpre [v']).
      { rew_nil_r wpre; eauto. }
      apply hu in hg; inv hg; auto.
    - apply mkProductionMap_correct.
    - apply mkClosureMap_result_correct.
    - constructor.
    - apply unique_stack_prefix_derivation_invar_starts_true.
  Qed.

  Theorem parse_sound__ambiguous_derivation :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (t  : tree),
      no_left_recursion g
      -> parse g x ts = Ambig t
      -> sym_derivation g (NT x) ts t
         /\ (exists t',
                sym_derivation g (NT x) ts t'
                /\ t' <> t).
  Proof.
    intros g x ts v hn hp.
    unfold parse in hp.
    eapply multistep_sound_ambig with (w := ts) in hp; eauto.
    - destruct hp as [hg [v' [hg' hneq]]]. unfold bottomFrameSyms in *; sis.
      (* lemma *)
      inv hg.
      inv H5; rew_anr.
      split; auto.
      inv hg'.
      inv H5; rew_anr.
      eexists; split; eauto.
      intros heq; subst; tc.
    - apply mkProductionMap_correct.
    - constructor.
    - exists []; eauto. 
    - apply ambiguous_stack_prefix_derivation_invar_starts_true.
  Qed.

  (* Error-free termination theorem *)

  Theorem parse_terminates_without_error :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (e  : parse_error),
      no_left_recursion g
      -> parse g x ts <> Error e.
  Proof.
    intros g x ts e hn hp; destruct e.
    - (* invalid state case *)
      eapply parse_never_reaches_invalid_state; eauto.
    - (* left recursion case *)
      eapply parse_doesn't_find_left_recursion_in_non_left_recursive_grammar; eauto.
    - (* prediction error case *)
      eapply parse_never_returns_prediction_error; eauto.
  Qed.

  (* Completeness theorems for unique
     and ambiguous derivations *)

  Theorem parse_complete__unique_derivation :
    forall (g  : grammar)
           (x  : nonterminal)
           (w  : list token)
           (t  : tree),
      no_left_recursion g
      -> sym_derivation g (NT x) w t
      -> (forall t', sym_derivation g (NT x) w t' -> t' = t)
      -> parse g x w = Accept t.
  Proof.
    intros g x w v hn hg hu.
    apply parse_complete in hg; auto.
    destruct hg as (v' & [hp | hp]); pose proof hp as hp'.
    - apply parse_sound__unique_derivation in hp; auto.
      destruct hp as (hg & _).
      apply hu in hg; subst; auto.
    - exfalso.
      apply parse_sound__ambiguous_derivation in hp; auto.
      destruct hp as (hg' & (v'' & hg & hneq)).
      apply hu in hg; apply hu in hg'; subst; tc.
  Qed.

  Theorem parse_complete__ambiguous_derivation :
    forall (g    : grammar)
           (x    : nonterminal)
           (w    : list token)
           (t t' : tree),
      no_left_recursion g
      -> sym_derivation g (NT x) w t
      -> sym_derivation g (NT x) w t'
      -> t <> t'
      -> exists t'',
          parse g x w = Ambig t''
          /\ sym_derivation g (NT x) w t''.
  Proof.
    intros g x w v v' hn hg hg'' hneq.
    pose proof hg as hg'.
    apply parse_complete in hg; auto.
    destruct hg as (v'' & [hp | hp]); eauto.
    - exfalso.
      apply parse_sound__unique_derivation in hp; auto.
      destruct hp as (hg & ha).
      apply ha in hg'; apply ha in hg''; subst; tc.
    - eexists; split; eauto.
      eapply parse_sound__ambiguous_derivation; eauto.
  Qed.

End Make.

Module Type MakeT (D : Defs.T).
  Include      D.
  Include Make D.
End MakeT.
