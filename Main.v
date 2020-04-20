Require Import List String.
Require Import GallStar.Defs.
Require Import GallStar.Parser.
Require Import GallStar.Parser_sound.
Require Import GallStar.Parser_error_free.
Require Import GallStar.Parser_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

Module Make (Export D : Defs.T).

  Module Export ParserAndProofs := ParserCompleteFn D.

  Inductive parse_result :=
  | Acc : tree -> parse_result
  | Amb : tree -> parse_result
  | Rej : string -> parse_result
  | Err : parse_error -> parse_result.

  (* to do : this can be replaced by parse *)
  Definition parseSymbol (g : grammar)
                         (x : nonterminal)
                         (w : list token) : parse_result :=
    match parse g x w with
    | Accept [v] => Acc v
    | Ambig  [v] => Amb v
    | Reject str => Rej str
    | Error e    => Err e
    | _          => Err InvalidState
    end.

  (* Soundness theorems for unambiguous and ambiguous derivations *)

  Theorem parseSymbol_sound_unambig :
    forall (g : grammar)
           (x : nonterminal)
           (w : list token)
           (t : tree),
      no_left_recursion g
      -> parseSymbol g x w = Acc t
      -> sym_derivation g (NT x) w t
         /\ (forall t', sym_derivation g (NT x) w t' -> t' = t).
  Proof.
    intros g x w t hn hp.
    unfold parseSymbol in hp.
    destruct (parse _ _ _) as [v | v | str | e] eqn:hp'; tc.
    - apply parse_sound_unambig in hp'; auto.
      destruct hp' as (hg & ha).
      (* lemma *)
      inv hg.
      inv H4; rew_anr.
      inv hp.
      split; auto.
      intros g' hs.
      assert (gamma_derivation g [NT x] wpre [g']).
      { rew_nil_r wpre; eauto. }
      apply ha in H; inv H; auto.
    - destruct v as [ | ? [ | ? ? ]]; tc.
  Qed.

  Theorem parseSymbol_sound_ambig :
    forall (g : grammar)
           (x : nonterminal)
           (w : list token)
           (t : tree),
      no_left_recursion g
      -> parseSymbol g x w = Amb t
      -> sym_derivation g (NT x) w t
         /\ (exists t', sym_derivation g (NT x) w t' /\ t' <> t).
  Proof.
    intros g x w t hn hp.
    unfold parseSymbol in hp.
    destruct (parse _ _ _) as [v | v | str | e] eqn:hp'; tc.
    - destruct v as [ | ? [ | ? ? ]]; tc.
    - apply parse_sound_ambig in hp'; auto.
      destruct hp' as (hg & (v' & hg' & hneq)). 
      (* lemma *)
      inv hg.
      inv H4; rewrite app_nil_r in *.
      inv hp.
      inv hg'.
      inv H5; rewrite app_nil_r in *.
      split; auto.
      eexists; split; eauto.
      unfold not; intros; subst; tc.
  Qed.

  (* Error-free termination theorem *)

  Theorem parseSymbol_error_free :
    forall (g  : grammar)
           (x  : nonterminal)
           (ts : list token)
           (e  : parse_error),
      no_left_recursion g
      -> parseSymbol g x ts <> Err e.
  Proof.
    intros g x ts e hn; unfold not; intros hp.
    unfold parseSymbol in hp.
    destruct (parse _ _ _) eqn:hp'; tc.
    - apply parse_sound_unambig in hp'; auto.
      destruct hp' as (hg & _).
      inv hg. inv H4. tc.
    - apply parse_sound_ambig in hp'; auto.
      destruct hp' as (hg & _).
      inv hg. inv H4. tc.
    - apply parse_terminates_without_error in hp'; auto.
  Qed.

  (* Completeness theorems for unambiguous and ambiguous derivations *)

  Theorem parseSymbol_complete_unique_derivation :
    forall (g : grammar)
           (x : nonterminal)
           (w : list token)
           (t : tree),
      no_left_recursion g
      -> sym_derivation g (NT x) w t
      -> (forall t', sym_derivation g (NT x) w t' -> t' = t)
      -> parseSymbol g x w = Acc t.
  Proof.
    intros g x w t hn hs ha.
    assert (hg : gamma_derivation g [NT x] w [t]).
    { rew_nil_r w; eauto. }
    apply parse_complete_unique_derivation in hg; auto.
    - unfold parseSymbol; rewrite hg; auto.
    - (* lemma *)
      inv hg.
      inv H5; rewrite app_nil_r in *.
      intros v' hg'.
      inv hg'.
      inv H5; rewrite app_nil_r in *.
      apply ha in H1; subst; auto.
  Qed.

  Theorem parseSymbol_complete_ambiguous_derivations :
    forall (g    : grammar)
           (x    : nonterminal)
           (w    : list token)
           (t t' : tree),
      no_left_recursion g
      -> sym_derivation g (NT x) w t
      -> sym_derivation g (NT x) w t'
      -> t <> t'
      -> exists t'', parseSymbol g x w = Amb t''.
  Proof.
    intros g x w t t' hn hs hs' hneq.
    assert (hg : gamma_derivation g [NT x] w [t]).
    { rew_nil_r w; eauto. }
    assert (hg' : gamma_derivation g [NT x] w [t']).
    { rew_nil_r w; eauto. }
    assert (hneq' : [t] <> [t']).
    { unfold not; intros ?; subst; tc. }
    eapply parse_complete_ambiguous_derivations in hg; eauto.
    destruct hg as (v'' & hp & hg).
    pose proof hp as hp'.
    apply parse_sound_ambig in hp; auto.
    destruct hp as (hg'' & _).
    inv hg''.
    inv H4; rew_anr.
    unfold parseSymbol.
    rewrite hp'; eauto.
  Qed.

End Make.
