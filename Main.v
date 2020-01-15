Require Import List String.
Require Import GallStar.Defs.
Require Import GallStar.Parser.
Require Import GallStar.Parser_sound.
Require Import GallStar.Parser_error_free.
Require Import GallStar.Parser_complete.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
        Import ListNotations.

Inductive parse_result :=
| Acc : tree -> parse_result
| Amb : tree -> parse_result
| Rej : string -> parse_result
| Err : parse_error -> parse_result.

Definition parseSymbol (g : grammar)
                       (s : symbol)
                       (w : list token) : parse_result :=
  match Parser.parse g [s] w with
  | Accept [v] => Acc v
  | Ambig  [v] => Amb v
  | Reject str => Rej str
  | Error e    => Err e
  | _          => Err InvalidState
  end.

(* Soundness theorems for unambiguous and ambiguous derivations *)

Theorem parseSymbol_sound_unambig :
  forall (g : grammar)
         (s : symbol)
         (w : list token)
         (t : tree),
    no_left_recursion g
    -> parseSymbol g s w = Acc t
    -> sym_derivation g s w t
       /\ (forall t', sym_derivation g s w t' -> t' = t).
Proof.
  intros g s w t hn hp.
  unfold parseSymbol in hp.
  destruct (Parser.parse _ _ _) as [v | v | str | e] eqn:hp'; tc.
  - apply parse_sound_unambig in hp'; auto.
    destruct hp' as (hg & ha).
    (* lemma *)
    inv hg.
    inv H4; rewrite app_nil_r in *.
    inv hp.
    split; auto.
    intros g' hs.
    assert (gamma_derivation g [s] wpre [g']).
    { rew_nil_r wpre; eauto. }
    apply ha in H; inv H; auto.
  - destruct v as [ | ? [ | ? ? ]]; tc.
Qed.

Theorem parseSymbol_sound_ambig :
  forall (g : grammar)
         (s : symbol)
         (w : list token)
         (t : tree),
    no_left_recursion g
    -> parseSymbol g s w = Amb t
    -> sym_derivation g s w t
       /\ (exists t', sym_derivation g s w t' /\ t' <> t).
Proof.
  intros g s w t hn hp.
  unfold parseSymbol in hp.
  destruct (Parser.parse _ _ _) as [v | v | str | e] eqn:hp'; tc.
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
         (s  : symbol)
         (ts : list token)
         (e  : parse_error),
    no_left_recursion g
    -> parseSymbol g s ts <> Err e.
Proof.
  intros g s ts e hn; unfold not; intros hp.
  unfold parseSymbol in hp.
  destruct (Parser.parse _ _ _) eqn:hp'; tc.
  - apply Parser_sound.parse_sound_unambig in hp'; auto.
    destruct hp' as (hg & _).
    inv hg. inv H4. tc.
  - apply Parser_sound.parse_sound_ambig in hp'; auto.
    destruct hp' as (hg & _).
    inv hg. inv H4. tc.
  - apply parser_terminates_without_error in hp'; auto.
Qed.

(* Completeness theorems for unambiguous and ambiguous derivations *)

Theorem parseSymbol_complete_unambig :
  forall (g : grammar)
         (s : symbol)
         (w : list token)
         (t : tree),
    no_left_recursion g
    -> sym_derivation g s w t
    -> (forall t', sym_derivation g s w t' -> t' = t)
    -> parseSymbol g s w = Acc t.
Proof.
  intros g s w t hn hs ha.
  assert (hg : gamma_derivation g [s] w [t]).
  { rew_nil_r w; eauto. }
  apply parse_complete_unambig in hg; auto.
  - unfold parseSymbol; rewrite hg; auto.
  - (* lemma *)
    inv hg.
    inv H5; rewrite app_nil_r in *.
    intros v' hg'.
    inv hg'.
    inv H5; rewrite app_nil_r in *.
    apply ha in H1; subst; auto.
Qed.

Theorem parseSymbol_complete_ambig :
  forall (g    : grammar)
         (s    : symbol)
         (w    : list token)
         (t t' : tree),
    no_left_recursion g
    -> sym_derivation g s w t
    -> sym_derivation g s w t'
    -> t <> t'
    -> exists t'', parseSymbol g s w = Amb t''.
Proof.
  intros g s w t t' hn hs hs' hneq.
  assert (hg : gamma_derivation g [s] w [t]).
  { rew_nil_r w; eauto. }
  assert (hg' : gamma_derivation g [s] w [t']).
  { rew_nil_r w; eauto. }
  assert (hneq' : [t] <> [t']).
  { unfold not; intros ?; subst; tc. }
  eapply parse_complete_ambig in hg; eauto.
  destruct hg as (v'' & hp).
  pose proof hp as hp'.
  apply Parser_sound.parse_sound_ambig in hp; auto.
  destruct hp as (hg & _).
  inv hg.
  inv H4; rewrite app_nil_r in *.
  unfold parseSymbol.
  rewrite hp'; eauto.
Qed.
  