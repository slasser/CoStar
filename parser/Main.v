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

  (* Soundness theorems for unique and ambiguous derivations *)

  Theorem parse_sound__unique_derivation :
    forall (gr    : grammar)
           (hw    : grammar_wf gr)
           (start : nonterminal)
           (word  : list token)
           (sem_v : nt_semty start),
      no_left_recursion gr
      -> parse gr hw start word = Accept _ sem_v
      -> sem_value_derivation gr (NT start) word sem_v
         /\ (forall sem_v',
                sem_value_derivation gr (NT start) word sem_v'
                -> sem_v' = sem_v).
  Proof.
    intros gr hw x w v hn hp.
    unfold parse in hp.
    eapply multistep_sound_unambig in hp; eauto.
    - apply mkClosureMap_correct.
    - constructor.
    - apply unique_stack_prefix_derivation_invar_starts_true.
  Qed.

  Theorem parse_sound__ambiguous_derivation :
    forall (gr    : grammar)
           (hw    : grammar_wf gr)
           (start : nonterminal)
           (word  : list token)
           (sem_v : nt_semty start),
      no_left_recursion gr
      -> parse gr hw start word = Ambig _ sem_v
      -> sem_value_derivation gr (NT start) word sem_v
         /\ (exists tr tr',
                tree_derivation gr (NT start) word tr
                /\ tree_derivation gr (NT start) word tr'
                /\ tr <> tr').
  Proof.
    intros g hw x w v hn hp.
    unfold parse in hp.
    eapply multistep_sound_ambig in hp; eauto.
    - constructor.
    - apply stack_prefix_derivation_start_true. 
    - apply ambiguous_stack_prefix_derivation_invar_starts_true.
  Qed.

  (* Error-free termination theorem *)

  Theorem parse_terminates_without_error :
    forall (gr    : grammar)
           (hw    : grammar_wf gr)
           (start : nonterminal)
           (word  : list token)
           (e     : parse_error),
      no_left_recursion gr
      -> parse gr hw start word <> Error _ e.
  Proof.
    intros gr hw x ts e hn hp; destruct e.
    - (* invalid state case *)
      eapply parse_never_reaches_invalid_state; eauto.
    - (* left recursion case *)
      eapply parse_doesn't_find_left_recursion_in_non_left_recursive_grammar; eauto.
    - (* prediction error case *)
      eapply parse_never_returns_prediction_error; eauto.
  Qed.

  (* Completeness theorem for unique and ambiguous derivations *)

  Theorem parse_complete :
    forall (gr : grammar)
           (hw : grammar_wf gr)
           (start : nonterminal)
           (word  : list token)
           (sem_v : nt_semty start),
      no_left_recursion gr
      -> sem_value_derivation gr (NT start) word sem_v
      -> (parse gr hw start word = Accept _ sem_v
          /\ (forall sem_v', sem_value_derivation gr (NT start) word sem_v' -> sem_v' = sem_v))
         \/
         ((exists sem_v',
              parse gr hw start word = Ambig _ sem_v')
          /\ (exists (t t' : tree),
                 tree_derivation gr (NT start) word t
                 /\ tree_derivation gr (NT start) word t'
                 /\ t <> t')).
  Proof.
    intros gr hw start word sem_v hn hd.
    pose proof hd as hd'.
    eapply parse_complete with (hw := hw) in hd; eauto.
    destruct hd as (sem_v' & [hp | hp]).
    - left.
      pose proof hp as hp'.
      apply parse_sound__unique_derivation in hp; auto.
      destruct hp as [hd hu].
      apply hu in hd'; subst; auto.
    - right; split; eauto.
      apply parse_sound__ambiguous_derivation in hp; auto.
      destruct hp as (_ & t & t' & htd & htd' & hneq); eauto.
  Qed.

End Make.

Module Type MakeT (D : Defs.T).
  Include      D.
  Include Make D.
End MakeT.
