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

(* To do: encapsulate "gamma_recognize unprocStackSyms..." in a definition *)
Fixpoint unprocStackSyms' (stk : parser_stack) : list symbol :=
  unprocStackSyms (lstackOf stk).

Lemma return_preserves_ussr :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' w,
    ce = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> gamma_recognize g (unprocStackSyms' (ce, cr :: frs)) w
    -> gamma_recognize g (unprocStackSyms' (cr', frs)) w.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' w
         ? ? ? hs; subst; auto.
Qed.

Lemma consume_preserves_ussr :
  forall g fr fr' frs o pre suf a l v w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> gamma_recognize g (unprocStackSyms' (fr, frs)) ((a, l) :: w)
    -> gamma_recognize g (unprocStackSyms' (fr', frs)) w.
Proof.
  intros g fr fr' frs o pre suf a l v w ? ? hs; subst; sis.
  apply gamma_recognize_terminal_head in hs.
  destruct hs as [l' [w' [heq hg]]]. 
  inv heq; auto.
Qed.

Lemma push_succ_preserves_ussr :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) w = PredSucc rhs
    -> gamma_recognize g (unprocStackSyms' (fr, frs)) w
    -> gamma_recognize g (unprocStackSyms' (Fr (Loc (Some x) [] rhs) [], fr :: frs)) w.
Proof.
  intros g fr o pre x suf v frs w rhs heq hn hw hl hu; subst; sis.
  apply gamma_recognize_nonterminal_head in hu.
  destruct hu as [rhs' [wpre [wmidsuf [heq [hin [hg hg']]]]]]; subst.
  apply gamma_recognize_split in hg'.
  destruct hg' as [wmid [wsuf [? [hg' hg'']]]]; subst.
  eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto; sis; subst;
  (do 2 (apply gamma_recognize_app; auto)).
Qed.

Lemma push_ambig_preserves_ussr :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) w = PredAmbig rhs
    -> gamma_recognize g (unprocStackSyms' (fr, frs)) w
    -> gamma_recognize g (unprocStackSyms' (Fr (Loc (Some x) [] rhs) [], fr :: frs)) w.
Proof.
  intros g fr o pre x suf v frs w rhs ? hn hw hl hu; subst; sis.
  eapply llPredict_ambig_rhs_unproc_stack_syms in hl; eauto.
  sis; auto.
Qed.

Lemma step_preserves_ussr :
  forall g av av' stk stk' w w' u u',
    no_left_recursion g
    -> stack_wf g stk
    -> gamma_recognize g (unprocStackSyms' stk) w
    -> step g (Pst av stk w u) = StepK (Pst av' stk' w' u')
    -> gamma_recognize g (unprocStackSyms' stk') w'.
Proof.
  intros g av av' stk stk' w w' u u' hn hw hu hs.
  unfold step in hs; dmeqs h; tc; inv hs.
  - eapply return_preserves_ussr; eauto.
  - eapply consume_preserves_ussr; eauto.
  - eapply push_succ_preserves_ussr; eauto.
  - eapply push_ambig_preserves_ussr; eauto.
Qed.

Lemma ussr_implies_multistep_doesn't_reject' :
  forall (g : grammar) 
         (tri : nat * nat * nat)
         (a   : Acc lex_nat_triple tri)
         (av  : NtSet.t)
         (stk : parser_stack)
         (w   : list token)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g (Pst av stk w u)))
         (s   : string),
    tri = meas g (Pst av stk w u)
    -> no_left_recursion g
    -> stack_wf g stk
    -> gamma_recognize g (unprocStackSyms' stk) w
    -> multistep g (Pst av stk w u) a <> Reject s.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros av stk w u a s heq hn hw hu; unfold not; intros hm; subst.
  apply multistep_reject_cases in hm.
  destruct hm as [hs | [st' [a' [hs hm]]]]. 
  - (* lemma *)
    clear a hlt IH.
    unfold step in hs; dmeqs h; tc; inv hs; sis.
    + inv hu.
    + inv hu. 
      inv H2.
      inv H1.
    + inv hu. 
      inv H2. 
      inv H1. 
      tc.
    + eapply ussr_llPredict_neq_reject; eauto.
    + inv hu. 
      inv H1.
      apply lhs_mem_allNts_true in H0. 
      tc.
  - destruct st' as [av' stk' w' u']. 
    eapply IH with (y := meas g (Pst av' stk' w' u')); eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto. 
    + eapply step_preserves_ussr; eauto.
Qed.

Lemma ussr_implies_multistep_doesn't_reject :
  forall (g : grammar) 
         (av  : NtSet.t)
         (stk : parser_stack)
         (w   : list token)
         (u   : bool)
         (a   : Acc lex_nat_triple (meas g (Pst av stk w u)))
         (s   : string),
    no_left_recursion g
    -> stack_wf g stk
    -> gamma_recognize g (unprocStackSyms' stk) w
    -> multistep g (Pst av stk w u) a <> Reject s.
Proof.
  intros; eapply ussr_implies_multistep_doesn't_reject'; eauto.
Qed.

Theorem valid_derivation_implies_parser_doesn't_reject :
  forall g ys w s,
    no_left_recursion g
    -> gamma_recognize g ys w
    -> parse g ys w <> Reject s.
Proof.
  intros g ys w s hn hg; unfold not; intros hp.
  unfold parse in hp.
  unfold mkInitState in hp.
  eapply ussr_implies_multistep_doesn't_reject; eauto.
  - constructor. 
  - simpl; rewrite app_nil_r; auto.
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
Theorem parse_complete_unambig :
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
Theorem parse_complete_ambig :
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