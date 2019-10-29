Require Import Arith List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.

Lemma multistep_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf)))
         (v      : forest),
    tri = meas g (Pst av stk wsuf)
    -> stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> multistep g (Pst av stk wsuf) a' = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros w wsuf av stk a' v heq hw hi hm; subst.
  apply multistep_accept_cases in hm.
  destruct hm as [hf | he].
  - apply step_StepAccept_facts in hf.
    destruct hf as [[xo [rpre [v' [heq]]]] heq']; subst.
    inv hi. 
    inv H; sis.
    unfold bottomFrameSyms; simpl; apps.
  - destruct he as [st' [a'' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_stack_derivation_invar; eauto.
Qed.

Theorem parser_sound :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token)
         (v  : forest),
    parse g ss ts = Accept v
    -> gamma_derivation g ss ts v.
Proof.
  intros g ss ts v hp.
  unfold parse in hp.
  eapply multistep_sound in hp; eauto.
  - apply lex_nat_triple_wf.
  - constructor. (* how do I get auto to take care of this? *)
  - eapply SD_invar; eauto.
Qed.
  