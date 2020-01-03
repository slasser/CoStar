Require Import Bool List String.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Prediction_complete.
Require Import GallStar.Parser.
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
Print Assumptions parse_complete.


(* experimenting *)

(*
Definition unprocTailSyms' (frs : list frame) :=
  unprocTailSyms (map loc frs).
 *)

(*
(* Invariant for proving the "unambiguous" version of the parser soundness
   lemma. The processed stack symbols and the semantic values stored
   in each frame comprise a unique partial derivation for the tokens that
   have been consumed. *)
Inductive unique_frames_derivation (g : grammar) :
  list frame -> list token -> list token -> Prop :=
| USD_empty :
    forall w,
      unique_frames_derivation g [] [] w
| USD_bottom :
    forall o pre suf v wpre wsuf,
      gamma_derivation g pre wpre v
      -> (forall wpre' wsuf' v',
             wpre' ++ wsuf' = wpre ++ wsuf
             -> gamma_derivation g pre wpre' v'
             -> gamma_recognize g suf wsuf'
             -> wpre' = wpre /\ wsuf' = wsuf /\ v' = v)
      -> unique_frames_derivation g [Fr (Loc o pre suf) v] wpre wsuf
| USD_upper :
    forall cr ce o o' pre pre' x suf suf' frs wpre wmid wsuf v v',
      cr = Fr (Loc o pre (NT x :: suf)) v
      -> ce = Fr (Loc o' pre' suf') v'
      -> unique_frames_derivation g (cr :: frs) wpre (wmid ++ wsuf)
      -> gamma_derivation g pre' wmid v'
      -> (forall wmid' wsuf' v'',
             wmid' ++ wsuf' = wmid ++ wsuf
             -> gamma_derivation g pre' wmid' v''
             -> gamma_recognize g (suf' ++ suf ++ unprocTailSyms' frs) wsuf'
             -> wmid' = wmid /\ wsuf' = wsuf /\ v'' = v')
      (* Here's the interesting part -- all pushes are unique *)
      -> (forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms' frs) (wmid ++ wsuf)
             -> rhs = pre' ++ suf')
      -> unique_frames_derivation g (ce :: cr :: frs) (wpre ++ wmid) wsuf.

Lemma return_preserves_unique_frames_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v',
    ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_wf g (ce, cr :: frs)
    -> unique_frames_derivation g (ce :: cr :: frs) wpre wsuf
    -> unique_frames_derivation g (cr' :: frs) wpre wsuf.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v'
         ? ? ? hw hu; subst; sis.
  inversion hu as [ ?
                  | ? ? ? ? ? ? ? ?
                  | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?
                    heq heq' htl hg hder hpush]; subst; clear hu.
  inv heq; inv heq'.
  destruct frs.
  - inv htl.
    apply USD_bottom.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + intros wpre' wsuf' v' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H4. rewrite app_nil_r in *.
      inv H1.
      eapply H6 in heq; eauto.
      * destruct heq as [? [? ?]]; subst.
        assert (ys = pre'0).
        { rewrite <- H1 in hpush.
          apply hpush in H0; auto.
          - rewrite app_nil_r in *; subst; auto.
          - apply gamma_recognize_app; auto.
            eapply gamma_derivation__gamma_recognize; eauto. }
        subst.
        eapply hder with (v'' := sts) in H1; eauto.
        destruct H1 as [? [? ?]]; subst.
        repeat split; auto.
      * econstructor; eauto.
        econstructor; eauto.
        eapply gamma_derivation__gamma_recognize; eauto.
  - inv htl.
    inv H3.
    rewrite <- app_assoc.
    eapply USD_upper; eauto.
    + rewrite <- app_assoc; auto.
    + eapply gamma_derivation_app; auto.
      inv hw. rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + intros wpre' wsuf' v'' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H6. rewrite app_nil_r in *.
      inv H1.
      eapply H8 in heq; eauto.
      * destruct heq as [? [? ?]]; subst.
        assert (ys = pre'0).
        { rewrite <- H1 in hpush.
          apply hpush in H0; auto.
          unfold unprocTailSyms'. simpl.
          apply gamma_recognize_app; auto.
          eapply gamma_derivation__gamma_recognize; eauto. }
        subst.
        eapply hder with (v'' := sts) in H1; eauto.
        destruct H1 as [? [? ?]]; subst.
        repeat split; auto.
      * constructor; auto.
        econstructor; eauto.
        eapply gamma_derivation__gamma_recognize; eauto.
    + intros rhs hi hr; subst.
      apply H9 in hi; auto.
      * rewrite hi. apps.
      * rewrite <- app_assoc in hr; auto.
Qed.

Lemma consume_preserves_unique_frames_derivation :
  forall g fr fr' frs o pre a suf v l wpre wsuf,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> unique_frames_derivation g (fr :: frs) wpre ((a,l) :: wsuf)
    -> unique_frames_derivation g (fr' :: frs) (wpre ++ [(a,l)]) wsuf.
Proof.
  intros g fr fr' frs o pre a suf v l wpre wsuf ? ? hu; subst.
  inv hu.
  - constructor.
    + apply gamma_derivation_app; auto.
      assert ([(a,l)] = [(a,l)] ++ []) by apps.
      rewrite H; eauto.
    + intros wpre' wsuf' v' heq hd hr; subst.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v'' [v''' [? [? [hd hd']]]]]]]; subst.
      inv hd'.
      inv H1. inv H4. rewrite app_nil_r in*.
      repeat rewrite <- app_assoc in heq.
      eapply H7 in heq; eauto.
      destruct heq as [? [? ?]]; subst.
      inv H0. repeat split; auto.
  - inv H2.
    rewrite <- app_assoc.
    econstructor; eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      assert ([(a,l)] = [(a,l)] ++ []) by apps.
      rewrite H; eauto.
    + intros wpre' wsuf' v'' heq hd hr; subst.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v''' [v'''' [? [? [hd hd']]]]]]]; subst.
      inv hd'.
      inv H1. inv H7. rewrite app_nil_r in*.
      repeat rewrite <- app_assoc in heq.
      eapply H5 in heq; eauto.
      * destruct heq as [? [? ?]]; subst.
        inv H0. repeat split; auto.
      * constructor; auto.
    + intros rhs hi hr.
      sis.
      eapply H8 in hi; eauto.
      * rewrite hi. apps.
      * rewrite <- app_assoc in hr; auto.
Qed.

Lemma push_succ_preserves_usd :
  forall g fr o pre x suf v frs wpre wsuf rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) wsuf = PredSucc rhs
    -> unique_frames_derivation g (fr :: frs) wpre wsuf
    -> unique_frames_derivation g (Fr (Loc (Some x) [] rhs) [] :: fr :: frs) wpre wsuf.
Proof.
  intros g fr o pre x suf v frs wpre wsuf rhs ? hn hw hl hu; subst; sis.
  assert (wpre = wpre ++ []) by apps. rewrite H.
  econstructor; eauto.
  - intros wmid' wsuf' v'' heq hd hr; sis; subst.
    inv hd; auto.
  - intros rhs' hi hr; sis.
    eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
Qed.    

Definition unique_prefix_derivation g w st :=
  match st with
  | Pst _ (fr, frs) wsuf u =>
    u = true
    -> exists wpre,
        w = wpre ++ wsuf
        /\ unique_frames_derivation g (fr :: frs) wpre wsuf
  end.

Lemma step_preserves_upd :
  forall g w st st',
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> unique_prefix_derivation g w st
    -> step g st = StepK st'
    -> unique_prefix_derivation g w st'.
Proof.
  intros g w [av (fr,frs) wsuf u] [av' (fr',frs') wsuf' u'] hn hw hu hs.
  red; red in hu.
  intros hu'.
  unfold step in hs; dmeqs h; inv hs; tc;
  destruct hu as [wpre [heq hu]]; subst; auto.
  - exists wpre; split; auto.
    eapply return_preserves_unique_frames_derivation; eauto.
  - exists (wpre ++ [(t,l1)]); split.
    + apps.
    + eapply consume_preserves_unique_frames_derivation; eauto.
  - exists wpre; split; auto.
    eapply push_succ_preserves_usd; eauto.
Qed.

Lemma upd_starts_true :
  forall g ys ts,
    unique_prefix_derivation g ts (mkInitState g ys ts).
Proof.
  intros g ys ts.
  unfold mkInitState; sis.
  intros _.
  exists []; split; auto.
  constructor; auto.
  intros wpre' wsuf' v' heq hd hr; sis.
  inv hd; auto.
Qed.

Require Import Parser_sound.

Lemma multistep_sound_unambig' :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest),
    tri = meas g (Pst av stk wsuf u)
    -> no_left_recursion g
    -> stack_wf g stk
    -> unique_prefix_derivation g w (Pst av stk wsuf u)
    -> multistep g (Pst av stk wsuf u) a' = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v
       /\ (forall v',
              gamma_derivation g (bottomFrameSyms stk) w v'
              -> v' = v).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros w wsuf av stk u a' v heq hn hw hi hm; subst.
  apply multistep_accept_cases in hm.
  destruct hm as [[hf hu] | he].
  - simpl in hu; subst.
    apply step_StepAccept_facts in hf.
    destruct hf as [[xo [rpre [v' [heq]]]] heq']; subst.
    unfold bottomFrameSyms; simpl; rewrite app_nil_r.
    red in hi.
    destruct hi as [wpre [heq hu]]; subst; auto.
    inv hu.
    rewrite app_nil_r in *.
    split; auto.
    intros v' hd.
    eapply H6 in hd; eauto.
    + destruct hd as [? [? ?]]; auto.
    + apps.
  - destruct he as [st' [a'' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_upd; eauto.
      simpl; auto.
Qed.

Lemma multistep_sound_unambig :
  forall (g      : grammar)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (u      : bool)
         (a      : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest),
    no_left_recursion g
    -> stack_wf g stk
    -> unique_prefix_derivation g w (Pst av stk wsuf u)
    -> multistep g (Pst av stk wsuf u) a = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v
       /\ (forall v',
              gamma_derivation g (bottomFrameSyms stk) w v'
              -> v' = v).
Proof.
  intros; eapply multistep_sound_unambig'; eauto.
Qed.

Theorem parse_sound_unambig :
  forall (g  : grammar)
         (ys : list symbol)
         (ts : list token)
         (v  : forest),
    no_left_recursion g
    -> parse g ys ts = Accept v
    -> gamma_derivation g ys ts v
       /\ (forall v',
              gamma_derivation g ys ts v'
              -> v' = v).
Proof.
  intros g ys ts v hn hp.
  unfold parse in hp.
  eapply multistep_sound_unambig in hp; eauto.
  - constructor.
  - apply upd_starts_true.
Qed.

(* now for the ambiguous case *)

Inductive frames_derivation (g : grammar) :
  list frame -> list token -> list token -> Prop :=
| FD_nil  :
    forall wsuf,
      frames_derivation g [] [] wsuf
| FD_cons :
    forall o pre suf v frs wpre wmid wsuf,
      gamma_derivation g pre wmid v
    -> frames_derivation g frs wpre (wmid ++ wsuf) 
    -> frames_derivation g (Fr (Loc o pre suf) v :: frs) (wpre ++ wmid) wsuf.

Hint Constructors frames_derivation.

Lemma fd_inv_cons :
  forall g o pre suf v frs w wsuf,
    frames_derivation g (Fr (Loc o pre suf) v :: frs) w wsuf
    -> exists wpre wmid,
      w = wpre ++ wmid
      /\ frames_derivation g frs wpre (wmid ++ wsuf)
      /\ gamma_derivation g pre wmid v.
Proof.
  intros g o pre suf v frs w wsuf hf; inv hf; eauto.
Qed.

Lemma return_preserves_frames_derivation :
  forall g ce cr cr' o o' pre pre' x suf v v' wpre wsuf frs,
    ce = Fr (Loc o' pre' []) v'
    -> cr = Fr (Loc o pre (NT x :: suf)) v
    -> cr' = Fr (Loc o (pre ++ [NT x]) suf) (v ++ [Node x v'])
    -> stack_wf g (ce, cr :: frs)
    -> frames_derivation g (ce :: cr :: frs) wpre wsuf
    -> frames_derivation g (cr' :: frs) wpre wsuf.
Proof.
  intros g ce cr cr' o o' pre pre' x suf v v' w wsuf frs ? ? ? hw hf; subst.
  apply fd_inv_cons in hf; destruct hf as [w' [wmid' [heq [hf hg']]]]; subst.
  apply fd_inv_cons in hf; destruct hf as [wpre [wmid [heq [hf hg]]]]; subst.
  rewrite <- app_assoc; econstructor; eauto.
  - apply gamma_derivation_app; auto.
    inv hw; rewrite app_nil_r in *.
    rew_nil_r wmid'; eauto.
  - rewrite <- app_assoc; auto.
Qed.

Lemma consume_preserves_frames_derivation :
  forall g fr fr' frs o pre suf v a l wpre wsuf,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> frames_derivation g (fr :: frs) wpre ((a,l) :: wsuf)
    -> frames_derivation g (fr' :: frs) (wpre ++ [(a,l)]) wsuf.
Proof.
  intros g fr fr' frs o pre suf v a l wpre wsuf ? ? hf; subst; inv hf.
  rewrite <- app_assoc; econstructor.
  - apply gamma_derivation_app; auto.
    rew_nil_r [(a,l)]; eauto.
  - rewrite <- app_assoc; auto.
Qed.

Lemma push_preserves_frames_derivation :
  forall g cr ce frs o o' pre suf v x rhs wpre wsuf,
    cr = Fr (Loc o pre (NT x :: suf)) v
    -> ce = Fr (Loc o' [] rhs) []
    -> frames_derivation g (cr :: frs) wpre wsuf
    -> frames_derivation g (ce :: cr :: frs) wpre wsuf.
Proof.
  intros g cr ce frs o o' pre suf v x rhs w wsuf ? ? hf; subst.
  apply fd_inv_cons in hf; destruct hf as [wpre [wmid [heq [hf hg]]]]; subst.
  rew_nil_r (wpre ++ wmid); eauto.
Qed.

Definition frames_prefix_derivation g w st :=
  match st with
  | Pst _ (fr, frs) wsuf _ =>
    exists wpre,
    w = wpre ++ wsuf
    /\ frames_derivation g (fr :: frs) wpre wsuf
  end.

Lemma step_preserves_frames_prefix_derivation :
  forall g w st st',
    stack_wf g st.(stack)
    -> frames_prefix_derivation g w st
    -> step g st = StepK st'
    -> frames_prefix_derivation g w st'.
Proof.
  intros g w [av (fr,frs) ts u] [av' (fr',frs') ts' u'] hw hf hs.
  red; red in hf.
  destruct hf as [wpre [heq hf]]; subst.
  unfold step in hs; dmeqs h; tc; inv hs.
  - eexists; split; eauto.
    eapply return_preserves_frames_derivation; eauto.
  - exists (wpre ++ [(t,l1)]); split; apps.
    eapply consume_preserves_frames_derivation; eauto.
  - eexists; split; eauto.
    eapply push_preserves_frames_derivation; eauto.
  - eexists; split; eauto.
    eapply push_preserves_frames_derivation; eauto.
Qed.

(* Invariant for proving the "ambiguous" version of the parser soundness
   theorem. The processed stack symbols and semantic values constructed
   for them comprise a correct partial derivation for the tokens consumed,
   and there exists a different semantic value for a (possibly different)
   prefix of the complete token sequence. *)
Inductive ambiguous_frames_derivation (g : grammar) :
  list frame -> list token -> list token -> Prop :=
| AFD_push :
    forall cr ce o o' pre pre' x suf suf' v v' wpre wmid wsuf frs alt_rhs,
      cr = Fr (Loc o pre (NT x :: suf)) v
      -> ce = Fr (Loc o' pre' suf') v'
      -> frames_derivation g (cr :: frs) wpre (wmid ++ wsuf)
      -> gamma_derivation g pre' wmid v'
      -> In (x, alt_rhs) g
      -> pre' ++ suf' <> alt_rhs
      -> gamma_recognize g (alt_rhs ++ suf ++ unprocTailSyms' frs) (wmid ++ wsuf)
      -> ambiguous_frames_derivation g (ce :: cr :: frs) (wpre ++ wmid) wsuf
| AFD_sem :
    forall fr o pre suf v v' wpre wmid wmid' wsuf wsuf' frs,
      fr = Fr (Loc o pre suf) v
      -> frames_derivation g frs wpre (wmid ++ wsuf)
      -> gamma_derivation g pre wmid v
      -> gamma_derivation g pre wmid' v'
      -> gamma_recognize g (suf ++ unprocTailSyms' frs) wsuf'
      -> wmid' ++ wsuf' = wmid ++ wsuf
      -> v' <> v
      -> ambiguous_frames_derivation g (fr :: frs) (wpre ++ wmid) wsuf
| AFD_tail :
    forall fr o pre suf v frs wpre wmid wsuf,
      fr = Fr (Loc o pre suf) v
      -> ambiguous_frames_derivation g frs wpre (wmid ++ wsuf)
      -> gamma_derivation g pre wmid v
      -> ambiguous_frames_derivation g (fr :: frs) (wpre ++ wmid) wsuf.

Lemma return_preserves_ambiguous_frames_derivation :
  forall g ce cr cr' o o' pre pre' x suf v v' wpre wsuf frs,
    ce = Fr (Loc o' pre' []) v'
    -> cr = Fr (Loc o pre (NT x :: suf)) v
    -> cr' = Fr (Loc o (pre ++ [NT x]) suf) (v ++ [Node x v'])
    -> stack_wf g (ce, cr :: frs)
    -> ambiguous_frames_derivation g (ce :: cr :: frs) wpre wsuf
    -> ambiguous_frames_derivation g (cr' :: frs) wpre wsuf.
Proof.
  intros g ce cr cr' o o' pre pre' x suf v v' w wsuf frs ? ? ? hw ha; subst.
  inv ha; subst.
  - (* ambig push case *)
    inv H2; inv H3.
    rewrite app_nil_r in *; sis.
    rename pre'0 into rhs; rename pre0 into pre;
    rename suf0 into suf; rename v0 into v; rename v'0 into v';
    rename x0 into x.    
    apply fd_inv_cons in H4.
    destruct H4 as [wp [wp' [heq [hf hg]]]]; subst.
    apply gamma_recognize_split in H10.
    destruct H10 as [w [w' [heq [hr hr']]]]; subst.
    apply gamma_recognize__exists_gamma_derivation in hr.
    destruct hr as [v_alt hr].
    inv hw. rewrite app_nil_r in *.
    rewrite <- app_assoc.
    eapply AFD_sem with (v := v ++ [Node x v'])
                        (v' := v ++ [Node x v_alt])
                        (wmid' := wp' ++ w); eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      rew_nil_r wmid; eauto.
    + apply gamma_derivation_app; eauto.
      rew_nil_r w; eauto.
    + repeat rewrite <- app_assoc in *.
      rewrite heq; auto.
    + unfold not; intros.
      apply app_inv_head in H.
      inv H.
      eapply trees_eq__gammas_eq_words_eq with
          (ys := rhs) in hr; eauto.
      firstorder.
  - (* sem case *)
    inv H1; inv H2; unfold unprocTailSyms' in *; sis.
    rewrite <- app_assoc.
    eapply AFD_sem with (v' := v ++ [Node x v'0])
                        (wmid' := wmid0 ++ wmid'); eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid'; eauto.
    + repeat rewrite <- app_assoc in *.
      rewrite H6; auto.
    + unfold not; intros.
      apply app_inv_head in H.
      inv H; tc.
  - (* tail case *)
    inv H1.
    inv H2.
    + (* caller push case *)
      inv H3.
      rewrite <- app_assoc.
      eapply AFD_push; eauto.
      * rewrite <- app_assoc; auto.
      * apply gamma_derivation_app; auto.
        inv hw. inv H14; rewrite app_nil_r in *.
        rew_nil_r wmid; eauto.
      * rewrite <- app_assoc; auto.
      * rewrite <- app_assoc; auto.
    + (* caller sem case *)
      inv H1.
      inv H7.
      inv H1.
      apply gamma_recognize__exists_gamma_derivation in H2.
      destruct H2 as [vy hvy].
      rewrite <- app_assoc.
      eapply AFD_sem with (wmid' := wmid' ++ wpre)
                          (v' := v' ++ [Node x vy]); eauto.
      * rewrite <- app_assoc; auto.
      * apply gamma_derivation_app; auto.
        inv hw; rewrite app_nil_r in *.
        rew_nil_r wmid; eauto.
      * apply gamma_derivation_app; auto.
        rew_nil_r wpre; eauto.
      * repeat rewrite <- app_assoc; auto.
      * unfold not; intros.
        apply app_inj_tail in H; firstorder.
    + inv H1.
      rewrite <- app_assoc.
      eapply AFD_tail; eauto.
      * rewrite <- app_assoc; auto.
      * apply gamma_derivation_app; auto.
        inv hw; rewrite app_nil_r in *.
        rew_nil_r wmid; eauto.
Qed.

Lemma consume_preserves_ambiguous_frames_derivation :
  forall g fr fr' frs o pre suf v a l wpre wsuf,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf a l])
    -> ambiguous_frames_derivation g (fr :: frs) wpre ((a,l) :: wsuf)
    -> ambiguous_frames_derivation g (fr' :: frs) (wpre ++ [(a,l)]) wsuf.
Proof.
  intros g fr fr' frs o pre suf v a l wpre wsuf ? ? ha; subst; inv ha.
  - (* push case *)
    inv H2.
    rewrite <- app_assoc.
    eapply AFD_push; eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      rew_nil_r ([(a,l)]); eauto.
    + rewrite <- app_assoc; auto.
    + rewrite <- app_assoc; auto.
  - (* sem case *)
    inv H1.
    inv H5.
    inv H1; sis.
    rewrite <- app_assoc.
    eapply AFD_sem with (wmid' := wmid' ++ [(a,l0)])
                        (v' := v' ++ [Leaf a l0]); eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      rew_nil_r ([(a,l)]); eauto.
    + apply gamma_derivation_app; auto.
      rew_nil_r ([(a,l0)]); eauto.
    + repeat rewrite <- app_assoc; auto.
    + unfold not; intros.
      apply app_inj_tail in H; destruct H; tc.
  - inv H1.
    rewrite <- app_assoc.
    eapply AFD_tail; eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      rew_nil_r ([(a,l)]); eauto.
Qed.

(* before proving that this invariant is preserved, 
   I'll need to prove a stronger fact about a PredAmbig result *)
Require Import GallStar.Prediction.

Lemma allPredictionsEqual_false_exists_diff_rhs :
  forall sp sps,
    allPredictionsEqual sp sps = false
    -> exists sp',
      In sp' sps
      /\ sp'.(prediction) <> sp.(prediction).
Proof.
  intros sp sps ha; unfold allPredictionsEqual in ha.
  induction sps as [| sp' sps IH]; simpl in ha.
  - inv ha.
  - apply andb_false_iff in ha; destruct ha as [hh | ht].
    + exists sp'; split.
      * apply in_eq.
      * unfold beqGamma in hh.
        destruct (gamma_eq_dec sp.(prediction) sp'.(prediction)); inv hh; auto.
    + apply IH in ht.
      destruct ht as [sp'' [hi hn]].
      exists sp''; split; auto.
      apply in_cons; auto.
Qed.

(* refactor *)
Lemma llPredict'_ambig_rhs_leads_to_successful_parse' :
  forall g orig_sps wsuf wpre curr_sps rhs,
    all_sp_stacks_wf g curr_sps
    -> subparsers_sound_wrt_originals g orig_sps wpre curr_sps wsuf
    -> llPredict' g curr_sps wsuf = PredAmbig rhs
    -> exists orig_sp final_sp orig_sp' final_sp' rhs',
        In orig_sp orig_sps
        /\ orig_sp.(prediction) = rhs
        /\ move_closure_multistep' g orig_sp (wpre ++ wsuf) final_sp []
        /\ finalConfig final_sp = true
        /\ In orig_sp' orig_sps
        /\ orig_sp'.(prediction) = rhs'
        /\ move_closure_multistep' g orig_sp' (wpre ++ wsuf) final_sp' []
        /\ finalConfig final_sp' = true
        /\ rhs' <> rhs.
Proof.
  intros g orig_sps wsuf.
  induction wsuf as [| t wsuf' IH]; intros wpre curr_sps rhs ha hi hl; destruct curr_sps as [| csp csps]; sis; tc.
  - destruct (allPredictionsEqual csp csps) eqn:ha'; tc.
    unfold handleFinalSubparsers in hl.
    destruct (filter _ _) as [| csp' csps'] eqn:hf; tc.
    destruct (allPredictionsEqual csp' csps') eqn:ha''; tc.
    inv hl.
    unfold subparsers_sound_wrt_originals in hi.
    pose proof hf as hf'.
    eapply filter_cons_in in hf.
    apply hi in hf.
    destruct hf as [orig_sp [hi' hm]].
    apply allPredictionsEqual_false_exists_diff_rhs in ha''.
    destruct ha'' as [csp'' [hi'' hn]].
    assert (hi''' : In csp'' (csp :: csps)).
    { eapply filter_tail_in; eauto. }
    apply hi in hi'''.
    destruct hi''' as [orig_sp' [hi''' hm']].
    exists orig_sp; exists csp'; exists orig_sp'; exists csp''; exists csp''.(prediction); repeat split; auto.
    + (* easy *)
      eapply mcms'_preserves_label; eauto.
    + assert (hi'''' : In csp' (filter finalConfig (csp :: csps))).
      { rewrite hf'; apply in_eq. }
      eapply filter_In in hi''''; destruct hi''''; auto.
    + eapply mcms'_preserves_label; eauto.
    + assert (hi'''' : In csp'' (filter finalConfig (csp :: csps))).
      { rewrite hf'; apply in_cons; auto. }
      eapply filter_In in hi''''; destruct hi''''; auto.
  - destruct (allPredictionsEqual _ _); tc.
    destruct (move _ _ ) as [e | sps'] eqn:hm; tc.
    destruct (closure _ _) as [e | sps''] eqn:hc; tc.
    eapply IH with (wpre := wpre ++ [t]) in hl.
    + destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi' [heq [hm' [hf [hi'' [heq' [hm'' [hf' hn]]]]]]]]]]]]]; subst.
      rewrite <- app_assoc in *; sis.
      exists osp; exists fsp; exists osp'; exists fsp'; exists osp'.(prediction); repeat split; eauto.
    + apply move_preserves_lstack_wf_invar in hm; auto.
      apply closure_preserves_lstack_wf_invar in hc; auto.
    + eapply move_closure_op_preserves_subparsers_sound_invar; eauto.
Qed.

(* okay, this version of the lemma is better because it doesn't
   include unprocStackSyms in the conclusion *)
Lemma llPredict_ambig_rhs_unproc_stack_syms' :
  forall g cr ce o pre x suf frs w rhs,
    cr = Loc o pre (NT x :: suf)
    -> ce = Loc (Some x) [] rhs
    -> no_left_recursion g
    -> lstack_wf g (cr, frs)
    -> llPredict g x (cr, frs) w = PredAmbig rhs
    -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms frs) w
       /\ (exists rhs',
              In (x, rhs') g
              /\ rhs' <> rhs
              /\ gamma_recognize g (rhs' ++ suf ++ unprocTailSyms frs) w).
           
Proof.
  intros g cr ce o pre x suf frs w rhs ? ? hn hw hl; subst; sis.
  pose proof hl as hl'; apply llPredict_ambig_in_grammar in hl'.
  unfold llPredict in hl.
  destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
  eapply llPredict'_ambig_rhs_leads_to_successful_parse'
    with (orig_sps := sps) (wpre := []) in hl; sis.
  - destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi [heq [hm [hf [hi' [heq' [hm' [hf' hn']]]]]]]]]]]]]; subst.
    split.
    + eapply mcms'_final_config in hm; auto.
      eapply closure_ussr_backwards with (sp' := osp) (w := w) in hs; eauto.
      * destruct hs as [init_sp [hi'' [hc hg]]].
      (* lemma? *)
      unfold initSps in hi''.
      apply in_map_iff in hi''.
      destruct hi'' as [rhs [heq hi'']]; subst; sis.
      apply closure_multistep_preserves_label in hc; sis; subst; auto.
      * (* lemma *)
        red. intros init_sp hi''.
        eapply initSps_preserves_lstack_wf_invar; eauto.
    + exists osp'.(prediction); repeat split; auto.
      * eapply startState_sp_prediction_in_rhssForNt
          with (sp' := osp') in hs; eauto.
        apply rhssForNt_in_iff in hs; auto.
      * eapply mcms'_final_config in hm'; auto.
        eapply closure_ussr_backwards with (sp' := osp') (w := w) in hs; auto.
        -- destruct hs as [init_sp [hi'' [hc hg]]].
           (* lemma? *)
           unfold initSps in hi''.
           apply in_map_iff in hi''.
           destruct hi'' as [rhs [heq hi'']]; subst; sis.
           apply closure_multistep_preserves_label in hc; sis; subst; auto.
        -- red; intros init_sp hi''.
           eapply initSps_preserves_lstack_wf_invar; eauto.
  - eapply stacks_wf_in_startState_result; eauto.
    simpl; auto.
  - red. intros sp' hi; sis.
    exists sp'; split; auto.
    eapply closure_func_refines_closure_multistep_backward in hi; eauto.
    + destruct hi as [sp [hi hc]].
      assert (hst : stable_config sp'.(stack)).
      { eapply stable_config_after_closure_multistep; eauto. }
      destruct sp' as [av pred ([o' pre' suf'], frs')]; sis.
      inv hst; auto.
    + red.
      intros sp hi'.
      eapply initSps_preserves_lstack_wf_invar; eauto.
Qed.
*)