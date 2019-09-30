Require Import Arith List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.

Lemma return_preserves_stack_derivation_invar :
  forall g callee caller caller' frs x xo xo_cr pre pre_cr suf_cr v v_cr wsuf w,
    stack_wf g (callee, caller :: frs)
    -> callee  = Fr (Loc xo pre []) v
    -> caller  = Fr (Loc xo_cr pre_cr (NT x :: suf_cr)) v_cr
    -> caller' = Fr (Loc xo_cr (pre_cr ++ [NT x]) suf_cr) (v_cr ++ [Node x v])
    -> stack_derivation_invar g (callee, caller :: frs) wsuf w
    -> stack_derivation_invar g (caller', frs) wsuf w.
Proof.
  intros g ce cr cr' frs x xo xo_cr pre pre_cr suf_cr v v_cr wsuf w 
         hwf hce hcr hcr' hi; subst.
  inv hwf; rewrite app_nil_r in *.
  inv_sdi wpre hsd.
  inv_sd  hsd wpre' wsuf' hgd hsd'.
  eapply stack_derivation_cases in hsd'.
  destruct frs as [| fr' frs]; sis.
  - repeat (econstructor; auto).
    eapply forest_app_singleton_node; eauto.
  - destruct hsd' as [w [w' [happ [hsd hgd']]]]; subst. 
    apply SD_invar with (wpre := w ++ w' ++ wsuf'); auto.
    + constructor; auto.
      eapply forest_app_singleton_node; eauto.
    + rewrite app_assoc; auto.
Qed.

Lemma consume_preserves_stack_derivation_invar :
  forall g fr fr' frs xo pre suf a l v w wsuf,
    fr = Fr (Loc xo pre (T a :: suf)) v
    -> fr' = Fr (Loc xo (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> stack_derivation_invar g (fr, frs) ((a, l) :: wsuf) w
    -> stack_derivation_invar g (fr', frs) wsuf w.
Proof.
  intros g fr fr' frs xo pre suf a l v w wsuf heq heq' hsd; subst.
  inv_sdi wpre hsd'.
  apply stack_derivation_cases in hsd'; destruct frs as [| fr' frs]; sis.
  - apply SD_invar with (wpre := wpre ++ [(a, l)]).
    + constructor.
      apply gamma_derivation_app; auto.
      apply terminal_head_gamma_derivation; auto.
    + rewrite <- app_assoc; auto.
  - destruct hsd' as [w [w' [happ [hsd hgd]]]]; subst.
    apply SD_invar with (wpre := w ++ w' ++ [(a, l)]).
    + constructor; auto.
      apply gamma_derivation_app; auto.
      apply terminal_head_gamma_derivation; auto.
    + repeat rewrite <- app_assoc; auto.
Qed.

Lemma push_preserves_stack_derivation_invar :
  forall g fr frs xo gamma wpre w,
    stack_derivation_invar g (fr, frs) wpre w
    -> stack_derivation_invar g (Fr (Loc xo [] gamma) [], fr :: frs) wpre w.
Proof.
  intros g fr frs xo gamma wpre w hi.
  inv_sdi w' hsd.
  eapply SD_invar; eauto.
  rewrite app_nil_r; auto.
Qed.

Lemma step_preserves_stack_derivation_invar :
  forall g av av' stk stk' wsuf wsuf' w,
    stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> step g (Pst av stk wsuf) = StepK (Pst av' stk' wsuf')
    -> stack_derivation_invar g stk' wsuf' w.
Proof.
  intros g av av' stk stk' wsuf wsuf' w hw hi hs.
  unfold step in hs.
  dms; inv hs; tc.
  - eapply return_preserves_stack_derivation_invar;  eauto.
  - eapply consume_preserves_stack_derivation_invar; eauto.
  - eapply push_preserves_stack_derivation_invar;    eauto.
  - eapply push_preserves_stack_derivation_invar;    eauto.
Qed.

Lemma step_preserves_bottomFrameSyms_invar :
  forall g av av' stk stk' ts ts',
    step g (Pst av stk ts) = StepK (Pst av' stk' ts')
    -> bottomFrameSyms stk = bottomFrameSyms stk'.
Proof.
  intros g av av' stk stk' ts ts' hs.
  unfold step in hs.
  dms; inv hs; tc; unfold bottomFrameSyms.
  - destruct l; sis; auto.
    rewrite <- app_assoc; auto.
  - destruct l; sis; auto.
    rewrite <- app_assoc; auto.
  - destruct l; sis; auto.
  - destruct l; sis; auto.
Qed.

Lemma multistep_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (a'     : Acc lex_nat_triple (Parser.meas g (Pst av stk wsuf)))
         (v      : forest),
    tri = Parser.meas g (Pst av stk wsuf)
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
    unfold bottomFrameSyms; simpl.
    repeat rewrite app_nil_r; auto.
  - destruct he as [st' [a'' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_stack_derivation_invar; eauto.
Qed.

Theorem parser_sound :
  forall (g : grammar)
         (ss : list symbol)
         (ts : list token)
         (v : forest),
    parse g ss ts = Accept v
    -> gamma_derivation g ss ts v.
Proof.
  intros g ss ts v hp.
  unfold parse in hp.
  eapply multistep_sound with (w := ts) in hp; try (constructor; auto).
  - unfold bottomFrameSyms in hp; sis; auto. 
  - intros; apply lex_nat_triple_wf.
  - eapply SD_invar with (wpre := []); auto.
Qed.
  