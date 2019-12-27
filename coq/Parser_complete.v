Require Import List String.
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


(* a thought: maybe replace this invariant with a function of
   the stack, i.e., "unprocessed symbols" *)

(*
Inductive unproc_tail_syms_recognize (g : grammar) : list frame -> list token -> Prop :=
| TR_nil :
    unproc_tail_syms_recognize g [] []
| TR_cons :
    forall o pre x suf v w w' frs,
      gamma_recognize g suf w
      -> unproc_tail_syms_recognize g frs w'
      -> unproc_tail_syms_recognize g (Fr (Loc o pre (NT x :: suf)) v :: frs) (w ++ w').

Hint Constructors unproc_tail_syms_recognize.

Inductive unproc_stack_syms_recognize (g : grammar) : parser_stack -> list token -> Prop :=
| SR :
    forall o pre suf v w w' frs,
      gamma_recognize g suf w
      -> unproc_tail_syms_recognize g frs w'
      -> unproc_stack_syms_recognize g (Fr (Loc o pre suf) v, frs) (w ++ w').

Hint Constructors unproc_stack_syms_recognize.


Lemma ussr_inv :
  forall g o pre suf v frs w'',
    unproc_stack_syms_recognize g (Fr (Loc o pre suf) v, frs) w''
    -> exists w w',
      w'' = w ++ w'
      /\ gamma_recognize g suf w
      /\ unproc_tail_syms_recognize g frs w'.
Proof.
  intros g o pre suf v frs w'' hs; inv hs; eauto.
Qed.
*)

Inductive unproc_tail_syms_recognize (g : grammar) : list frame -> list token -> Prop :=
| TR_nil :
    unproc_tail_syms_recognize g [] []
| TR_cons :
    forall o pre x suf v w w' frs,
      gamma_recognize g suf w
      -> unproc_tail_syms_recognize g frs w'
      -> unproc_tail_syms_recognize g (Fr (Loc o pre (NT x :: suf)) v :: frs) (w ++ w').

Hint Constructors unproc_tail_syms_recognize.

Inductive unproc_stack_syms_recognize (g : grammar) : parser_stack -> list token -> Prop :=
| SR :
    forall o pre suf v w w' frs,
      gamma_recognize g suf w
      -> unproc_tail_syms_recognize g frs w'
      -> unproc_stack_syms_recognize g (Fr (Loc o pre suf) v, frs) (w ++ w').

Hint Constructors unproc_stack_syms_recognize.

Lemma ussr_inv :
  forall g o pre suf v frs w'',
    unproc_stack_syms_recognize g (Fr (Loc o pre suf) v, frs) w''
    -> exists w w',
      w'' = w ++ w'
      /\ gamma_recognize g suf w
      /\ unproc_tail_syms_recognize g frs w'.
Proof.
  intros g o pre suf v frs w'' hs; inv hs; eauto.
Qed.

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
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
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
Print Assumptions ussr_implies_multistep_doesn't_reject'.

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

Lemma gamma_derivation__gamma_recognize :
  forall g ys w v,
    gamma_derivation g ys w v
    -> gamma_recognize g ys w.
Proof.
  intros g ys w v hg.
  induction hg using gamma_derivation_mutual_ind with
      (P := fun s w t (hs : sym_derivation g s w t) => 
              sym_recognize g s w); eauto.
Qed.

Lemma gamma_recognize__exists_gamma_derivation :
  forall g ys w,
    gamma_recognize g ys w
    -> exists v,
      gamma_derivation g ys w v.
Proof.
  intros g ys w hg.
  induction hg using gamma_recognize_mutual_ind with
      (P := fun s w (hs : sym_recognize g s w) => 
              exists t, sym_derivation g s w t); firstorder; eauto.
  repeat econstructor; eauto.
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

Fixpoint procSyms (frs : list frame) : list (list symbol) :=
  map (fun fr => fr.(loc).(rpre)) frs.

Definition procStackSyms (stk : parser_stack) :=
  let (fr, frs) := stk in procSyms (fr :: frs).

Fixpoint procVals (frs : list frame) : list (list tree) :=
  map sem frs.

Definition stackVals (stk : parser_stack) :=
  let (fr, frs) := stk in procVals (fr :: frs).

Definition unprocTailSyms' (frs : list frame) :=
  unprocTailSyms (map loc frs).

Inductive unique_frames_derivation (g : grammar) : list frame -> list token -> list token -> Prop :=
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
                  | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' htl hg hder hpush]; subst; clear hu.
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
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
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



Inductive unique_frames_derivation (g : grammar) : list frame -> list token -> list token -> bool -> Prop :=
| USD_empty :
    forall w u,
      unique_frames_derivation g [] [] w u
| USD_bottom :
    forall o pre suf v wpre wsuf u,
      gamma_derivation g pre wpre v
      -> (u = true
          -> forall wpre' wsuf' v',
             wpre' ++ wsuf' = wpre ++ wsuf
             -> gamma_derivation g pre wpre' v'
             -> gamma_recognize g suf wsuf'
             -> wpre' = wpre /\ wsuf' = wsuf /\ v' = v)
      -> unique_frames_derivation g [Fr (Loc o pre suf) v] wpre wsuf u
| USD_upper :
    forall cr ce o o' pre pre' x suf suf' frs wpre wmid wsuf v v' u u',
      cr = Fr (Loc o pre (NT x :: suf)) v
      -> ce = Fr (Loc o' pre' suf') v'
      -> unique_frames_derivation g (cr :: frs) wpre (wmid ++ wsuf) u
      -> gamma_derivation g pre' wmid v'
      -> (u' = true
          -> forall wmid' wsuf' v'',
             wmid' ++ wsuf' = wmid ++ wsuf
             -> gamma_derivation g pre' wmid' v''
             -> gamma_recognize g (suf' ++ suf ++ unprocTailSyms' frs) wsuf'
             -> wmid' = wmid /\ wsuf' = wsuf /\ v'' = v')
      -> (u' = true
          -> forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms' frs) (wmid ++ wsuf)
             -> rhs = pre' ++ suf')
      -> unique_frames_derivation g (ce :: cr :: frs) (wpre ++ wmid) wsuf (u && u').

(* NEXT STEP: HAVE TO SPLIT THESE INTO CASES WHERE 
   PREVIOUS U FLAG IS TRUE AND FALSE *)

Lemma return_preserves_unique_frames_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v',
    ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_wf g (ce, cr :: frs)
    -> unique_frames_derivation g (ce :: cr :: frs) wpre wsuf (false && u)
    -> unique_frames_derivation g (cr' :: frs) wpre wsuf 
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v'
         ? ? ? hw hu; subst; sis.
  inversion hu as [? ? | ? ? ? ? ? ? ? ? ? |
                   ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' htl hg hder hpush]; subst; clear hu.
  inv heq; inv heq'.
  destruct frs.
  - inv htl.
    apply USD_bottom.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + intros hc; tc.
  - inv htl. inv H3.
    sis.
    rewrite <- app_assoc.
    rewrite <- Bool.andb_assoc.
    eapply USD_upper; eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + 
    destruct f as [[o pre suf'] v]; subst.
    inv H9.
    eapply USD_upper; eauto.
    + rewrite <- app_assoc; auto.
  
Lemma return_preserves_unique_frames_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v' u,
    ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_wf g (ce, cr :: frs)
    -> unique_frames_derivation g (ce :: cr :: frs) wpre wsuf u
    -> unique_frames_derivation g (cr' :: frs) wpre wsuf u.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v' u
         ? ? ? hw hu; subst; sis.
  inversion hu as [? ? | ? ? ? ? ? ? ? ? ? |
                   ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' htl hg hder hpush]; subst; clear hu.
  inv heq; inv heq'.
  destruct frs.
  - inv htl.
    apply USD_bottom.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + intros hu wpre' wsuf' v' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H4. rewrite app_nil_r in *.
      inv H1.
      eapply H7 in heq; eauto.
      * destruct heq as [? [? ?]]; subst.
        assert (ys = pre'0).
        { rewrite <- H1 in hpush.
          apply hpush in H0; auto.
          - rewrite app_nil_r in *; subst; auto.
          - apply andb_prop in hu. destruct hu; auto.
            - apply gamma_recognize_app; auto.
            eapply gamma_derivation__gamma_recognize; eauto. }
        subst.
        eapply hder with (v'' := sts) in H1; eauto.
        -- destruct H1 as [? [? ?]]; subst.
           repeat split; auto.
        -- apply andb_prop in hu; firstorder.
      * apply andb_prop in hu; firstorder.
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
    + intros hu wpre' wsuf' v'' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H6. rewrite app_nil_r in *.
      inv H1.
      eapply H9 in heq; eauto.
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
    + intros hu' rhs hi hr; subst.
      apply H10 in hi; auto.
      * rewrite hi. apps.
      * rewrite <- app_assoc in hr; auto.
Qed.

(* refactor *)
Lemma return_preserves_unique_frames_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v' u,
    ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_wf g (ce, cr :: frs)
    -> unique_frames_derivation g (ce :: cr :: frs) wpre wsuf u
    -> unique_frames_derivation g (cr' :: frs) wpre wsuf u.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' wpre wsuf v v' u
         ? ? ? hw hu; subst; sis.
  inversion hu as [? ? | ? ? ? ? ? ? ? ? ? |
                   ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? heq heq' htl hg hder hpush]; subst; clear hu.
  inv heq. inv heq; inv heq'.
  destruct frs.
  - inv htl.
    apply USD_bottom.
    + apply gamma_derivation_app; auto.
      inv hw; rewrite app_nil_r in *.
      rew_nil_r wmid; eauto.
    + intros hu wpre' wsuf' v' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H4. rewrite app_nil_r in *.
      inv H1.
      eapply H7 in heq; eauto.
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
      * constructor; auto.
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
    + intros hu wpre' wsuf' v'' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [vs [vs' [? [? [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      inv hd'.
      inv H6. rewrite app_nil_r in *.
      inv H1.
      eapply H9 in heq; eauto.
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
    + intros hu' rhs hi hr; subst.
      apply H10 in hi; auto.
      * rewrite hi. apps.
      * rewrite <- app_assoc in hr; auto.
Qed.

Lemma consume_preserves_unique_frames_derivation :
  forall g fr fr' frs o pre a suf v l wpre wsuf u,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> unique_frames_derivation g (fr :: frs) wpre ((a,l) :: wsuf) u
    -> unique_frames_derivation g (fr' :: frs) (wpre ++ [(a,l)]) wsuf u.
Proof.
  intros g fr fr' frs o pre a suf v l wpre wsuf u ? ? hu; subst.
  inv hu.
  - constructor.
    + apply gamma_derivation_app; auto.
      assert ([(a,l)] = [(a,l)] ++ []) by apps.
      rewrite H; eauto.
    + intros hu wpre' wsuf' v' heq hd hr; subst.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v'' [v''' [? [? [hd hd']]]]]]]; subst.
      inv hd'.
      inv H1. inv H4. rewrite app_nil_r in*.
      repeat rewrite <- app_assoc in heq.
      eapply H8 in heq; eauto.
      destruct heq as [? [? ?]]; subst.
      inv H0. repeat split; auto.
  - inv H2.
    rewrite <- app_assoc.
    econstructor; eauto.
    + rewrite <- app_assoc; auto.
    + apply gamma_derivation_app; auto.
      assert ([(a,l)] = [(a,l)] ++ []) by apps.
      rewrite H; eauto.
    + intros hu wpre' wsuf' v'' heq hd hr; subst.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v''' [v'''' [? [? [hd hd']]]]]]]; subst.
      inv hd'.
      inv H1. inv H7. rewrite app_nil_r in*.
      repeat rewrite <- app_assoc in heq.
      eapply H5 in heq; eauto.
      * destruct heq as [? [? ?]]; subst.
        inv H0. repeat split; auto.
      * constructor; auto.
    + intros hu rhs hi hr.
      sis.
      eapply H9 in hi; eauto.
      * rewrite hi. apps.
      * rewrite <- app_assoc in hr; auto.
Qed.

Lemma usd_inv_cons :
  forall g o pre suf v frs wpre wsuf u,
    unique_frames_derivation g (Fr (Loc o pre suf) v :: frs) wpre wsuf u
    -> exists wpre' wmid,
      wpre = wpre' ++ wmid
      /\ gamma_derivation g pre wmid v
      /\ unique_frames_derivation g frs wpre' (wmid ++ wsuf) u.
Proof.
  intros g o pre suf v frs wpre wsuf u hu.
  inv hu.
  - exists []; exists wpre; repeat split; auto.
    constructor.
  - inv H2; eauto.
Qed.

Lemma push_succ_preserves_usd :
  forall g fr o pre x suf v frs wpre wsuf rhs u,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) wsuf = PredSucc rhs
    -> unique_frames_derivation g (fr :: frs) wpre wsuf u
    -> unique_frames_derivation g (Fr (Loc (Some x) [] rhs) [] :: fr :: frs) wpre wsuf u.
Proof.
  intros g fr o pre x suf v frs wpre wsuf rhs u ? hn hw hl hu; subst; sis.
  assert (wpre = wpre ++ []) by apps. rewrite H.
  econstructor; eauto.
  - intros hu' wmid' wsuf' v'' heq hd hr; sis; subst.
    inv hd; auto.
  - intros hu' rhs' hi hr; sis.
    eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
Qed.    

Definition unique_prefix_derivation g w st :=
  match st with
  | Pst _ (fr, frs) wsuf u =>
    exists wpre,
    w = wpre ++ wsuf
    /\ unique_frames_derivation g (fr :: frs) wpre wsuf u
  end.

Lemma step_preserves_upd :
  forall g w st st',
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> unique_prefix_derivation g w st
    -> step g st = StepK st'
    -> unique_prefix_derivation g w st'.
Proof.
  intros g w [av (fr,frs) wsuf u] [av' (fr',frs') wsuf' u'] hn hw hu hs; red; red in hu.
  destruct hu as [wpre [heq hu]]; subst.
  unfold step in hs; dmeqs h; tc; inv hs.
  - exists wpre; split; auto.
    eapply return_preserves_unique_frames_derivation; eauto.
  - exists (wpre ++ [(t,l1)]); split.
    + apps.
    + eapply consume_preserves_unique_frames_derivation; eauto.
  - exists wpre; split; auto.
    eapply push_succ_preserves_usd; eauto.
  - exists wpre; split; auto.
    rew_nil_r wpre. destruct u; sis.
    + econstructor; eauto.
      * sis; auto.
    + sis. auto.
Inductive frames_derivation (g : grammar) :
  list (list symbol) -> list (list token) -> list (list tree) -> Prop :=
| FD_nil  :
    frames_derivation g [] [] []
| FD_cons :
    forall ys yss ts tss vs vss,
      gamma_derivation g ys ts vs
      -> frames_derivation g yss tss vss
      -> frames_derivation g (ys :: yss) (ts :: tss) (vs :: vss). 

Hint Constructors frames_derivation.

Lemma fd_inv :
  forall g ys yss' ts tss' vs vss',
    frames_derivation g (ys :: yss') (ts :: tss') (vs :: vss')
    -> gamma_derivation g ys ts vs
       /\ frames_derivation g yss' tss' vss'.
Proof.
  intros g ys yss' ts tss' vs vss' hf; inv hf; eauto.
Qed.

Lemma fd_split_tss :
  forall g ys yss' tss vs vss',
    frames_derivation g (ys :: yss') tss (vs :: vss')
    -> exists ts tss',
      tss = ts :: tss'
      /\ gamma_derivation g ys ts vs
      /\ frames_derivation g yss' tss' vss'.
Proof.
  intros g ys yss' tss vs vss' hf; inv hf; eauto.
Qed.

Lemma fd_split_tss_vss :
  forall g ys yss' tss vss,
    frames_derivation g (ys :: yss') tss vss
    -> exists ts tss' vs vss',
      tss = ts :: tss'
      /\ vss = vs :: vss'
      /\ gamma_derivation g ys ts vs
      /\ frames_derivation g yss' tss' vss'.
Proof.
  intros g ys yss' tss vss hf; inv hf; eauto 8.
Qed.

Lemma return_preserves_frames_derivation' :
  forall g ce cr cr' frs x o o' pre pre' suf' ts ts' tss v v',
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> frames_derivation g (procStackSyms (ce, cr :: frs)) (ts :: ts' :: tss) (stackVals (ce, cr :: frs))
    -> frames_derivation g (procStackSyms (cr', frs)) ((ts' ++ ts) :: tss) (stackVals (cr', frs)).
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' ts ts' tss v v'
         hw ? ? ? hf; subst; sis.
  do 2 (apply fd_inv in hf; destruct hf as [? hf]).
  constructor; auto.
  apply gamma_derivation_app; auto.
  inv hw; rewrite app_nil_r in *; rew_nil_r ts; eauto.
Qed.

Lemma consume_preserves_frames_derivation :
  forall g fr fr' frs o pre a suf v l ts tss,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> frames_derivation g (procStackSyms (fr, frs)) (ts :: tss) (stackVals (fr, frs))
    -> frames_derivation g (procStackSyms (fr', frs)) ((ts ++ [(a,l)]) :: tss) (stackVals (fr', frs)).
Proof.
  intros g fr fr' frs o pre a suf v l ts tss ? ? hf; subst; sis. 
  inv hf; constructor; auto.
  apply gamma_derivation_app; auto.
  apply terminal_head_gamma_derivation; auto.
Qed.

Lemma push_preserves_frames_derivation :
  forall g fr frs o' suf' ts tss,
    frames_derivation g (procStackSyms (fr, frs)) (ts :: tss) (stackVals (fr, frs))
    -> frames_derivation g (procStackSyms (Fr (Loc o' [] suf') [], fr :: frs)) ([] :: ts :: tss) (stackVals (Fr (Loc o' [] suf') [], fr :: frs)).
Proof.
  intros g [[o pre suf] v] frs o' suf' ts tss hf; sis.
  apply fd_inv in hf; destruct hf; auto.
Qed.

(*
Inductive all_pushes_unique (g : grammar) : list frame -> list token -> list token -> Prop :=
| APU_empty :
    forall w,
    all_pushes_unique g [] [] w
| APU_bottom :
    forall o pre suf v w w',
      gamma_derivation g pre w v
      -> all_pushes_unique g [Fr (Loc o pre suf) v] w w'
| APU_upper :
    forall o o' pre pre' suf suf' v v' x frs wpre wmid wsuf,
      all_pushes_unique g (Fr (Loc o pre (NT x :: suf)) v :: frs) wpre (wmid ++ wsuf)
      -> gamma_derivation g pre' wmid v'
      -> (forall pre'' suf'' wmid'' wsuf'' v'',
             In (x, pre'' ++ suf'') g
             -> wmid'' ++ wsuf'' = wmid ++ wsuf
             -> gamma_derivation g pre'' wmid'' v''
             -> gamma_recognize g (suf'' ++ suf ++ unprocTailSyms' frs) wsuf
             -> pre'' = pre' /\ suf'' = suf')
      -> all_pushes_unique g (Fr (Loc o' pre' suf') v' ::
                              Fr (Loc o  pre  (NT x :: suf )) v  ::
                              frs)
                           (wpre ++ wmid) wsuf.
 *)

Inductive all_pushes_unique (g : grammar) : list frame -> list (list token) -> list token -> Prop :=
| APU_empty :
    forall w,
    all_pushes_unique g [] [] w
| APU_bottom :
    forall o pre suf v ts wsuf,
      gamma_recognize g pre ts
      -> all_pushes_unique g [Fr (Loc o pre suf) v] [ts] wsuf
| APU_upper :
    forall o o' pre pre' suf suf' v v' x frs tss ts wsuf,
      all_pushes_unique g (Fr (Loc o pre (NT x :: suf)) v :: frs) tss (ts ++ wsuf)
      -> gamma_recognize g pre' ts
      -> (forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms' frs) (ts ++ wsuf)
             -> rhs = pre' ++ suf')
      -> all_pushes_unique g (Fr (Loc o' pre' suf') v' ::
                              Fr (Loc o  pre  (NT x :: suf )) v  ::
                              frs)
                           (ts :: tss) wsuf.
(*
Inductive all_pushes_unique (g : grammar) : list frame -> list token -> list token -> Prop :=
| APU_empty :
    forall w,
    all_pushes_unique g [] [] w
| APU_bottom :
    forall o pre suf v w w',
      gamma_recognize g pre w
      -> all_pushes_unique g [Fr (Loc o pre suf) v] w w'
| APU_upper :
    forall o o' pre pre' suf suf' v v' x frs wpre wmid wsuf,
      all_pushes_unique g (Fr (Loc o pre (NT x :: suf)) v :: frs) wpre (wmid ++ wsuf)
      -> gamma_recognize g pre' wmid
      -> (forall rhs wmid'' wsuf'',
             In (x, rhs) g
             -> wmid'' ++ wsuf'' = wmid ++ wsuf
             -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms' frs) (wmid'' ++ wsuf'')
             -> rhs = pre' ++ suf')
      -> all_pushes_unique g (Fr (Loc o' pre' suf') v' ::
                              Fr (Loc o  pre  (NT x :: suf )) v  ::
                              frs)
                           (wpre ++ wmid) wsuf.
*)
(*

Inductive all_pushes_unique (g : grammar) : list frame -> list token -> Prop :=
| APU_empty :
    forall w,
    all_pushes_unique g [] w
| APU_bottom :
    forall fr w,
      all_pushes_unique g [fr] w
| APU_upper :
    forall o o' pre pre' suf suf' v v' x frs w,
      all_pushes_unique g (Fr (Loc o pre (NT x :: suf)) v :: frs) w
      -> (forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ 
             -> gamma_recognize g (suf ++ unprocTailSyms' frs) w'
             -> rhs = pre' ++ suf')
      -> all_pushes_unique g (Fr (Loc o' pre' suf') v' ::
                              Fr (Loc o  pre  (NT x :: suf )) v  ::
                              frs) (w ++ w').
*)
Hint Constructors all_pushes_unique.

Definition all_stack_pushes_unique g (stk : parser_stack) ws w' :=
  let (fr, frs) := stk in all_pushes_unique g (fr :: frs) ws w'.

Fixpoint rconcat {A : Type} (xss : list (list A)) : list A :=
  match xss with
  | []         => []
  | xs :: xss' => rconcat xss' ++ xs
  end.
      
Definition all_stack_pushes_unique_invar g st w :=
  match st with
  | Pst av stk wsuf u =>
    u = true
    -> exists tss,
        w = rconcat tss ++ wsuf
        /\ all_stack_pushes_unique g stk tss wsuf
  end.

Lemma apu_cons :
  forall g o pre suf v frs ts tss wsuf,
    all_pushes_unique g (Fr (Loc o pre suf) v :: frs) (ts :: tss) wsuf
    -> gamma_recognize g pre ts
       /\ all_pushes_unique g frs tss (ts ++ wsuf).
Proof.
  intros g o pre suf v frs ts tss wsuf ha; inv ha; auto.
Qed.

Lemma apu_split_tss :
  forall g o pre suf v frs tss wsuf,
    all_pushes_unique g (Fr (Loc o pre suf) v :: frs) tss wsuf
    -> exists ts tss',
      tss = ts :: tss'
      /\ gamma_recognize g pre ts
       /\ all_pushes_unique g frs tss' (ts ++ wsuf).
Proof.
  intros g o pre suf v frs tss wsuf ha; inv ha; eauto.
Qed.

Lemma return_preserves_apu :
  forall g ce cr cr' frs x o o' pre pre' suf' ts ts' tss wsuf v v',
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> all_stack_pushes_unique g (ce, cr :: frs) (ts :: ts' :: tss) wsuf
    -> all_stack_pushes_unique g (cr', frs) ((ts' ++ ts) :: tss) wsuf.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' ts ts' tss wsuf v v' hw ? ? ? ha; subst; sis.
  inv hw; rewrite app_nil_r in *.
  pose proof ha as ha'.
  do 2 (apply apu_cons in ha; destruct ha as [? ha]).
  inv ha'.
  inv H16.
  - constructor.
    apply gamma_recognize_app; auto.
    rew_nil_r ts; eauto.
  - constructor.
    + rewrite <- app_assoc; auto.
    + apply gamma_recognize_app; auto.
      rew_nil_r ts; eauto.
    + intros rhs hi hg.
      apply H13 in hi.
      * rewrite hi; apps.
      * rewrite <- app_assoc in hg; auto.
Qed.

Lemma consume_preserves_apu :
  forall g fr fr' frs o pre suf a l v ts tss wsuf,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> all_stack_pushes_unique g (fr, frs) (ts :: tss) ((a,l) :: wsuf)
    -> all_stack_pushes_unique g (fr', frs) ((ts ++ [(a,l)]) :: tss) wsuf.
Proof.
  intros g fr fr' frs o pre suf a l v ts tss wsuf ? ? ha; subst; sis.
  pose proof ha as ha'; apply apu_cons in ha; destruct ha as [hg ha].
  destruct frs.
  - inv ha.
    constructor.
    apply gamma_recognize_app; auto.
    rew_nil_r [(a,l)]; auto.
  - inv ha'.
    constructor.
    + rewrite <- app_assoc; auto.
    + apply gamma_recognize_app; auto.
      rew_nil_r [(a,l)]; auto.
    + intros rhs hi hg'.
      apply H10 in hi.
      * rewrite hi; apps.
      * rewrite <- app_assoc in hg'; auto.
Qed.

Lemma push_succ_preserves_apu :
  forall g fr o pre x suf v frs tss wsuf rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) wsuf = PredSucc rhs
    -> all_stack_pushes_unique g (fr, frs) tss wsuf
    -> all_stack_pushes_unique g (Fr (Loc (Some x) [] rhs) [], fr :: frs) ([] :: tss) wsuf.
Proof.
  intros g fr o pre x suf v frs tss wsuf rhs ? hn hw hl ha; subst; sis.
  constructor; auto.
  intros rhs' hi hg; sis.
  pose proof hl as hl'.
  apply llPredict_succ_in_grammar in hl'.
  eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
Qed.
(*
  apply apu_inv_cons in H13.
  destruct 
  
  inv 
  constructor.
  apply apu_inv_cons in ha.
  destruct ha as [wpres' [wpre [heq [hg ha]]]]; subst.
  apply apu_inv_cons in ha.
  destruct ha as [wpres'' [wpre' [heq [hg' ha]]]]; subst.
  destruct frs; destruct wpres''; sis.
  - inv ha.
  - constructor.
  inv ha.
  inv H13.
  - eapply APU_bottom with (weconstructor.
  destruct frs.
  - inv H13. econstructor.
  inv H13.
  - constructor.
    apply gamma_recognize_app; auto.
    rew_nil_r wmid; eauto.
  - rewrite <- app_assoc; constructor.
    + rewrite <- app_assoc; auto.
    + apply gamma_recognize_app; auto.
      rew_nil_r wmid; eauto.
    + intros rhs wmid'' wsuf'' hi heq hg.
      rewrite <- app_assoc.
      eapply H10; eauto.
      rewrite heq in hg.
      rewrite <- app_assoc in hg; auto.
Qed.
 *)
(*
Lemma consume_preserves_apu :
  forall g fr fr' frs o pre suf a l v w w',
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> all_stack_pushes_unique g (fr, frs) w ((a,l) :: w')
    -> all_stack_pushes_unique g (fr', frs) (w ++ [(a,l)]) w'.
Proof.
  intros g fr fr' frs o pre suf a l v w w' ? ? ha; subst; sis.
  destruct frs; auto.
  - constructor.
    inv ha.
    apply gamma_recognize_app; auto.
    rew_nil_r [(a,l)]; auto.
  - inv ha.
    rewrite <- app_assoc.
    constructor; auto.
    + assert ((wmid ++ [(a,l)]) ++ w' = wmid ++ (a,l) :: w') by apps.
      rewrite H; auto.
    + apply gamma_recognize_app; auto.
      rew_nil_r [(a,l)]; auto.
    + intros rhs wmid'' wsuf'' hi heq hg.
      eapply H9 in hi; eauto.
      * rewrite <- app_assoc; auto.
      * rewrite heq in hg.
        rewrite <- app_assoc in hg; sis; auto.
Qed.

Lemma push_succ_preserves_apu :
  forall g fr o pre x suf v frs w w' rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) w' = PredSucc rhs
    -> all_stack_pushes_unique g (fr, frs) w w'
    -> all_stack_pushes_unique g (Fr (Loc (Some x) [] rhs) [], fr :: frs) w w'.
Proof.
  intros g fr o pre x suf v frs w w' rhs heq hn hw hl ha; subst; sis.
  rew_nil_r w.
  constructor; auto.
  intros rhs' wmid'' wsuf'' hi heq hg; sis; subst.
  pose proof hl as hl'.
  apply llPredict_succ_in_grammar in hl'.
  eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
Qed.

Lemma step_preserves_apu :
    forall g st st' w,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> all_stack_pushes_unique_invar g st w
    -> step g st = StepK st'
    -> all_stack_pushes_unique_invar g st' w.
Proof.
  intros g st st' w hn hw ha hs.
  unfold step in hs; dmeqs h; tc; inv hs; red; red in ha.
  - intros hu'; apply ha in hu'.
    destruct hu' as [wpre [heq ha']]; subst.
    exists wpre; split; auto.
    eapply return_preserves_apu; eauto.
  - intros hu'; apply ha in hu'.
    destruct hu' as [wpre [heq ha']]; subst.
    exists (wpre ++ [(t, l2)]); split.
    + apps.
    + eapply consume_preserves_apu; eauto.
  - intros hu'; apply ha in hu'.
    destruct hu' as [wpre [heq ha']]; subst.
    exists wpre; split; auto.
    eapply push_succ_preserves_apu; eauto.
  - intros hc; inv hc.
Qed.
 *)

Lemma step_preserves_apu :
    forall g st st' w,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> all_stack_pushes_unique_invar g st w
    -> step g st = StepK st'
    -> all_stack_pushes_unique_invar g st' w.
Proof.
  intros g st st' w hn hw ha hs.
  unfold step in hs; dmeqs h; tc; inv hs; red; red in ha.
  - intros hu'; apply ha in hu'; clear ha.
    destruct hu' as [tss [heq ha']]; subst.
    pose proof ha' as ha''.
    apply apu_split_tss in ha'.
    firstorder; subst.
    apply apu_split_tss in H1.
    firstorder; subst; sis.
    eapply return_preserves_apu in ha''; eauto.
    exists ((x1 ++ x) :: x2); split; eauto.
    sis; apps.
  - intros hu'; apply ha in hu'.
    destruct hu' as [tss [heq ha']]; subst.
    pose proof ha' as ha''.
    apply apu_split_tss in ha''.
    firstorder; subst.
    eapply consume_preserves_apu in ha'; eauto.
    exists ((x ++ [(t,l2)]) :: x0); split; auto.
    sis; apps.
  - intros hu'; apply ha in hu'.
    destruct hu' as [tss [heq ha']]; subst.
    exists ([] :: tss); split; auto.
    + sis; apps.
    + eapply push_succ_preserves_apu; eauto.
  - intros hc; inv hc.
Qed.

Definition stack_derives_unique_prefix (g : grammar) (st : parser_state) (w : list token) : Prop :=
  match st with
  | Pst av stk wsuf u =>
    exists tss,
    w = rconcat tss ++ wsuf
    /\ frames_derivation g (procStackSyms stk) tss (stackVals stk)
    /\ (u = true
        -> (forall tss' wsuf' vss',
               w = rconcat tss' ++ wsuf'
               -> frames_derivation g (procStackSyms stk) tss' vss'
               -> gamma_recognize g (unprocStackSyms' stk) wsuf'
               -> tss' = tss /\ wsuf' = wsuf /\ vss' = stackVals stk))
  end.

Lemma step_preserves_uspd :
  forall g st st' w,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> all_stack_pushes_unique_invar g st w
    -> stack_derives_unique_prefix g st w
    -> step g st = StepK st'
    -> stack_derives_unique_prefix g st' w.
Proof.
  intros g [av stk ts u] [av' stk' ts' u'] w hn hw ha hu hs.
  unfold step in hs; dmeqs h; tc; inv hs; destruct hu as [tss [heq [hd hu]]]; subst.
  - (* return case *)
    pose proof hd as hd'. 
    apply fd_split_tss in hd'.
    destruct hd' as [? [? [? [? ?]]]]; subst.
    apply fd_split_tss in H1.
    destruct H1 as [? [? [? [? ?]]]]; subst.
    pose proof hd as hd'.
    eapply return_preserves_frames_derivation' in hd'; eauto.
    simpl in hd'.
    red.
    sis.
    exists ((x1 ++ x) :: x2); split; auto.
    + sis; apps.
    + split; auto.
      intros hu' tss' wsuf' vss' heq hd'' hr.
      assert (sym_derivation g (NT n) x (Node n sem)) by admit.
      
      pose proof hd'' as hd'''.
      apply fd_split_tss_vss in hd'''.
      destruct hd''' as [? [? [? [? [? [? [? ?]]]]]]]; subst.
      apply fd_inv in hd'; destruct hd'.
      apply gamma_derivation_split in H4.
      destruct H4 as [? [? [? [? [? [? [? ?]]]]]]]; subst.
      inv H8.
      inv H12.
      rewrite app_nil_r in *.
      inv H9.
      eapply hu with (tss' := wpre :: x6 :: x3)
                     (vss' := sts  :: x8 :: x5) in hr; eauto.
      * destruct hr as [? [? ?]]; subst.
        inv H4. repeat split; auto.
        inv H10; auto.
      * simpl in heq. simpl.
        rewrite heq. apps.
      * constructor; auto.
        inv hw. rewrite app_nil_r in *.
        pose proof ha as test.
        destruct ha as [tss [heq' ha]]; auto.
        pose proof ha as ha'.
        apply apu_split_tss in ha'.
        destruct ha' as [? [? [? [? ?]]]]; subst.
        apply apu_split_tss in H11.
        destruct H11 as [? [? [? [? ?]]]]; subst.
        pose proof ha as ha'.
        apply apu_cons in ha'; destruct ha'; subst.
        apply apu_cons in H13; destruct H13; subst.
        inv ha.
        apply apu_cons in H29; destruct H29.
        simpl in heq'.
        rewrite heq' in heq. simpl in heq.
        apply fd_inv in hd''.
        destruct hd'' as [a b].
        apply gamma_derivation_split in a.
        destruct a as [? [? [? [? [? [? [bee cee]]]]]]].
        inv cee.
        inv H25.
        inv H22.
        apply app_inj_tail in H19. destruct H19; subst.
        
        
        
        subst. 
        inv ha'.
        apply H24 in H6; auto.
        -- rewrite app_nil_r in *; subst; auto.
        -- apply app_inv_tail in heq'.
           apply apu_cons in ha.
           destruct ha as [hi lo].
           apply apu_split_tss in lo.
           destruct lo as [? [? [? [? ?]]]]; subst.
           sis.
           rewrite heq' in heq.
           assert (rconcat (x :: x1 :: x2) =
                   rconcat (ts :: x0 :: x4)).
           { simpl; auto. }
           assert (rconcat (ts :: x0 :: x4) ++ ts' =
                   rconcat (wpre :: x6 :: x3) ++ wsuf').
           { simpl; auto.
             rewrite heq. apps. }
           
           inv H4.
           inv ha
           simpl in heq'.
           rewrite heq' in heq.
           simpl in heq.
           
           rewrite heq in heq'.
           simpl in heq'.
        
        apply fd_inv in hd''; destruct hd''.
        
      apply fd_inv in hd; destruct hd.
      sis.
      apply gamma_derivation_split in 
      assert (rconcat (x :: x1 :: x2) ++ ts' = rconcat (x0 :: x3) ++ wsuf').
      { simpl; auto. }
      eapply hu in H10; eauto.
      * destruct H10 as [? [? ?]]; subst.
        repeat split; auto.
        -- inv H10.
           exfalso.
           eapply cons_neq_tail.
           symmetry in H6. eauto.
        -- 
           assert (x1 :: x2 = [x1] ++ x2) by auto.
           assert (x2 = [] ++ x2) by auto.
           rewrite H6 in H3.
           rewrite H in H3.
           apply app_
           rewrite <- app_nil_r in H6.
           
        -- 
      
    exists tss; split; auto.
    split.
    + simpl.
      pose proof hd as hd'.
      inv hd.
      inv hd'.
      eapply return_preserves_frames_derivation.


    
    + cbv beta in *. eapply return_preserves_frames_derivation; eauto.
    + intros hu' wpre' wsuf' vss' heq hf hg; sis.
      (* should be able to peel stuff off in hd *)
      apply frames_derivation_inv_cons in hd.
      destruct hd as [w [w' [vss [vs [heq' [heq'' [hf' hd]]]]]]]; subst.
      apply frames_derivation_inv_cons in hf.
      destruct hf as [wpre [wsuf [vss'' [vs' [heq''' [heq'''' [hf hd']]]]]]]; subst.
      eapply gamma_derivation_split in hd'.
      destruct hd' as [w'' [w''' [v [v' [? [? [hd' hd'']]]]]]]; subst.
      inv hw. rewrite app_nil_r in *.
      rename rpre into xs.
      inv hd''.
      inv H5. rewrite app_nil_r in *.
      inv H2.
      rename n into x; rename ys into ys'; rename xs into ys.
      (* notice that ys and ys' appear at the ends of the
         derivation judgments, so the invariant about unique
         pushes will have to say something about the derivation
         involving the procStackSyms *)
      (*      assert (ys' = ys) by admit.
      { destruct ha as [ww [heq' ha]]; auto.
        apply app_inv_tail in heq'; subst.
        inv ha.
        rewrite <- H14 in heq.
        eapply H17 in H0; eauto.
        - rewrite app_nil_r in H0; auto.
        - apply gamma_recognize_app; auto.
          + *)
      pose proof hg as hg'.
      eapply hu with (vss' := (vss'' ++ [v]) ++ [sts]) in hg; eauto.
      * destruct hg as [? [? ?]]; subst.
        repeat split; auto.
        apply app_inj_tail in H4; destruct H4; subst.
        apply app_inj_tail in H2; destruct H2; subst; auto.
      * rewrite app_assoc.
        constructor; auto.
        destruct ha as [wpres [heq' ha]]; subst; auto.
        (* new thought : maybe you're losing information with
           the app in the prefix derivation invariant *)




        
        pose proof ha as ha'.
        apply apu_inv_cons in ha'.
        destruct ha' as [wpres' [wpre' [? [hg'' ha']]]]; subst.
        apply apu_inv_cons in ha'.
        destruct ha' as [wpres'' [wpre'' [? [hg''' ha']]]]; subst.
        pose proof ha as ha''.
        apply apu_inv_cons in ha''.
        firstorder; subst.
        apply app_inj_tail in H2; destruct H2; subst.
        apply apu_inv_cons in H5.
        firstorder; subst.
        apply app_inj_tail in H2; destruct H2; subst.
        inv ha.
        apply app_inj_tail in H18; destruct H18; subst.
        apply apu_inv_cons in H19.
        firstorder; subst.
        apply app_inj_tail in H2; destruct H2; subst.
        apply app_inv_tail in heq'; destruct heq'; subst.
        eapply H21 in H0; eauto.
        -- rewrite app_nil_r in *; subst; auto.
        -- 
        
        firstorder; subst.
        assert (ys' = ys).
        { apply app_inj_tail in heq''; destruct heq''; subst.
          destruct ha as [wpres [heq' ha]]; auto.
          apply app_inv_tail in heq'; subst.
          pose proof ha as ha'.
          apply apu_inv_cons in ha'.
          destruct ha' as [wpres' [wpre'' [? [hg'' ha']]]]; subst.
          apply apu_inv_cons in ha'.
          destruct ha' as [wpres'' [wpre''' [? [hg''' ha']]]]; subst.
          inv ha.
          apply app_inj_tail in H14; destruct H14; subst.
          apply apu_inv_cons in H15; firstorder; subst.
          apply app_inj_tail in H2; destruct H2; subst.
          eapply H17 in H0; eauto.
          - rewrite app_nil_r in *; auto.
          - 
            
          rewrite heq' in heq.
          
          destruct wpres'.
          - (* exfalso *)
            sis.
            inv ha.
            rewrite app_nil_r in *; subst.
            inv H15.
            + inv H14.
            + assert ([w ++ w'] = [] ++ [w ++ w']) by auto.
              rewrite H in H14.
              apply app_inj_tail in H14; destruct H14.
              subst.
              symmetry in H2. apply app_cons_not_nil in H2.
              inv H2.
          - 

                inv H14. inv H2. inv H4.
            subst.
          apply apu_inv_cons in ha.
          destruct ha as [wpres'' [wpre''' [? [? ?]]]]; subst.
          pose proof ha' as ha''.
          inv ha'.
          apply apu_inv_cons in H17.
          firstorder; subst.
          inv ha''.
          apply app_inj_tail in H22; destruct H22; subst.
          eapply H25 in H0; eauto.
          - rewrite app_nil_r in *; auto.
          - 
          apply apu_inv_cons in ha.
          destruct ha as [wpres' [wpre' [heq''' [hg'' ha]]]]; subst.
          rewrite concat_app in heq'; sis.
          rewrite app_nil_r in *.
          subst.
          sis.c
          sis.
          
          assert (gamma_recognize g ys w') by admit.
          assert (gamma_recognize g (l1 ++ unprocTailSyms' l0) ts'
          
          inv ha.
          pose proof H0 as H0'.
          eapply H17 in H0; eauto.
          - rewrite app_nil_r in H0; auto.
          - inv H15.
            + rewrite app_nil_r in *; sis.
              
              cinv hg'.
              unfold unprocTailSyms'. sis.
              rewrite <- H2.
              rewrite app_nil_r.
              
          inv H15.
          - eapply H17 in H0; eauto.
            + rewrite app_nil_r in H0; auto.
            + sis. inv hf. sis.
              
          - inv H15.
            + 
            rewrite <- H14 in heq. apply gamma_recognize_app; auto.
            + *)
        
  - exists (wpre ++ [(t, l2)]); split; auto.
    + apps.
    + split.
      * eapply consume_preserves_frames_derivation; eauto.
      * (* uniqueness part *)
        intros hu' wpre' wsuf' vss' heq hf hg; sis.
        apply frames_derivation_inv_cons in hd.
        destruct hd as [? [? [? [? [? [? [? ?]]]]]]]; subst.
        apply app_inj_tail in H0; destruct H0; subst.
        apply frames_derivation_inv_cons in hf.
        destruct hf as [w [w' [vss [vs [heq' [heq'' [hf hg']]]]]]]; subst.
        apply gamma_derivation_terminal_end in hg'.
        destruct hg' as [wf [l' [vf [? [? hg']]]]]; subst.
        assert ((w ++ wf ++ [(t,l')]) ++ wsuf' =
                (w ++ wf) ++ ([(t,l')] ++ wsuf')) by apps.
        rewrite H in heq.
        apply hu with (vss' := vss ++ [vf]) in heq; auto.
        destruct heq as [? [? ?]]; subst.
        rewrite <- H0.
        inv H3.
        apply app_inj_tail in H4; destruct H4; subst.
        repeat split; auto.
        apps.
  - exists wpre; split; auto.
    split.
    + eapply push_preserves_frames_derivation; eauto.
    + intros hu' wpre' wsuf' vss' heq hf hg; sis.
      apply frames_derivation_inv_cons in hf.
      destruct hf as [wpre'' [wsuf [vss [vs [? [? [hf hg']]]]]]]; subst.
      inv hg'. rewrite app_nil_r in *.
      eapply hu in hf; eauto.
      * destruct hf as [? [? ?]]; subst.
        repeat split; auto.
      * apply llPredict_succ_in_grammar in h5.
        apply gamma_recognize_split in hg.
        destruct hg as [w [w' [? [hg hg']]]]; subst.
        constructor; eauto.
  - exists wpre; split; auto.
    split.
    + eapply push_preserves_frames_derivation; eauto.
    + intros hc; inv hc.
Admitted.

Fixpoint procSyms (frs : list frame) : list symbol :=
  match frs with
  | []                         => []
  | Fr (Loc _ pre _) _ :: frs' => procSyms frs' ++ pre
  end.

Definition procStackSyms (stk : parser_stack) :=
  let (fr, frs) := stk in procSyms (fr :: frs).

Fixpoint procVals (frs : list frame) : forest :=
  match frs with
  | []                         => []
  | Fr _ v :: frs' => procVals frs' ++ v
  end.

Definition stackVals (stk : parser_stack) :=
  let (fr, frs) := stk in procVals (fr :: frs).

Lemma frames_derivation__gamma_derivation :
  forall g frs w,
    frames_derivation g frs w
    -> gamma_derivation g (procSyms frs) w (procVals frs).
Proof.
  intros g frs w hf; induction hf; sis; auto.
  apply gamma_derivation_app; auto.
Qed.

Lemma stack_derivation__gamma_derivation :
  forall g stk w,
    stack_derivation g stk w
    -> gamma_derivation g (procStackSyms stk) w (stackVals stk).
Proof.
  intros g (fr, frs) w hs.
  unfold procStackSyms; unfold stackVals; simpl in hs.
  apply frames_derivation__gamma_derivation; auto.
Qed.

(*
(* Experiment with adding a semantic value (forest) to this relation *)
Inductive frames_derivation (g : grammar) : list frame -> list token -> forest -> Prop :=
| FD_nil :
    frames_derivation g [] [] []
| FD_cons :
    forall o pre suf wpre wsuf vpre vsuf frs,
      gamma_derivation g pre wsuf vsuf
      -> frames_derivation g frs wpre vpre
      -> frames_derivation g (Fr (Loc o pre suf) vsuf :: frs) (wpre ++ wsuf) (vpre ++ vsuf).

Hint Constructors frames_derivation.

Lemma frames_derivation_inv_cons :
  forall g o pre suf vsuf v frs w,
    frames_derivation g (Fr (Loc o pre suf) vsuf :: frs) w v
    -> exists wpre wsuf vpre,
      w = wpre ++ wsuf
      /\ v = vpre ++ vsuf
      /\ gamma_derivation g pre wsuf vsuf
      /\ frames_derivation g frs wpre vpre.
Proof.
  intros g o pre suf vsuf v frs w hf; inv hf; eauto 8.
Qed.

Definition stack_derivation g stk w v :=
  match stk with
  | (fr, frs) => frames_derivation g (fr :: frs) w v
  end.

Lemma stack_derivation_inv_return :
  forall g o o' pre pre' suf suf' vmid vsuf v frs w,
    stack_derivation g (Fr (Loc o pre suf) vsuf, Fr (Loc o' pre' suf') vmid :: frs) w v
    -> exists wpre wmid wsuf vpre,
      w = wpre ++ wmid ++ wsuf
      /\ v = vpre ++ vmid ++ vsuf
      /\ gamma_derivation g pre wsuf vsuf
      /\ gamma_derivation g pre' wmid vmid
      /\ frames_derivation g frs wpre vpre.
Proof.
  intros g o o' pre pre' suf suf' vmid vsuf v frs w hf; sis.
  apply frames_derivation_inv_cons in hf.
  destruct hf as [wpre [wsuf [vpre [? [? [hg hf]]]]]]; subst.
  apply frames_derivation_inv_cons in hf; firstorder; subst.
  repeat rewrite <- app_assoc; eauto 10.
Qed.

Lemma return_preserves_stack_derivation :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' v'' w,
    stack_wf g (ce, cr :: frs)
    -> ce  = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_derivation g (ce, cr :: frs) w (v'' ++ v' ++ v)
    -> stack_derivation g (cr', frs) w (v'' ++ v' ++ [Node x v]).
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' v'' w
         hw ? ? ? hs; subst; sis.
  apply stack_derivation_inv_return in hs.
  destruct hs as [wpre [wmid [wsuf [vpre [heq [heq' [hg [hg' hf]]]]]]]]; subst.
  apply app_inv_tail in heq'; subst; constructor; auto.
  inv hw; rewrite app_nil_r in *; eapply forest_app_singleton_node; eauto.
Qed.

Lemma consume_preserves_stack_derivation :
  forall g fr fr' frs o pre suf a l v v' w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> stack_derivation g (fr, frs) w (v' ++ v)
    -> stack_derivation g (fr', frs) (w ++ [(a, l)]) (v' ++ v ++ [Leaf l]).
Proof.
  intros g fr fr' frs o pre suf a l v v' w ? ? hs; subst.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [wpre [wsuf [vpre [heq [heq' [hg hf]]]]]]; subst.
  apply app_inv_tail in heq'; subst.
  rewrite <- app_assoc; constructor; auto.
  apply gamma_derivation_app; auto.
  apply terminal_head_gamma_derivation; auto.
Qed.

Lemma push_preserves_stack_derivation :
  forall g fr frs o' suf' w v,
    stack_derivation g (fr, frs) w v
    -> stack_derivation g (Fr (Loc o' [] suf') [], fr :: frs) w v.
Proof.
  intros g [[o pre suf] v'] frs o' suf' w v hs.
  apply frames_derivation_inv_cons in hs.
  destruct hs as [wpre [wsuf [vpre [heq [heq' [hg hf]]]]]]; subst.
  rew_nil_r (wpre ++ wsuf); rew_nil_r (vpre ++ v'); constructor; auto.
Qed.


(*
Lemma consume_preserves_ussr :
  forall g fr fr' frs o pre suf a l v w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
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
 *)
 *)

Definition unique_stack_prefix_derivation (g : grammar) (st : parser_state) (w : list token) : Prop :=
  match st with
  | Pst av stk wsuf u =>
    exists wpre,
    w = wpre ++ wsuf
    /\ stack_derivation g stk wpre
    /\ (u = true
        -> (forall wpre' wsuf' v',
               w = wpre' ++ wsuf'
               -> gamma_derivation g (procStackSyms stk) wpre' v'
               -> gamma_recognize g (unprocStackSyms' stk) wsuf'
               -> wpre' = wpre /\ wsuf' = wsuf /\ v' = stackVals stk))
  end.

Lemma step_preserves_uspd :
  forall g st st' w,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> unique_stack_prefix_derivation g st w
    -> step g st = StepK st'
    -> unique_stack_prefix_derivation g st' w.
Proof.
  intros g [av stk ts u] [av' stk' ts' u'] w hn hw hu hs.
  unfold step in hs; dmeqs h; tc; inv hs; destruct hu as [wpre [heq [hd hu]]]; subst.
  - (* return case *)
    exists wpre; split; auto.
    split.
    + eapply return_preserves_stack_derivation; eauto.
    + (* uniqueness part *)
      apply stack_derivation_inv_return in hd.
      destruct hd as [wpre' [wmid [wsuf [heq [heq' [hg hf]]]]]]; subst.
      sis.
      intros hu' wpre'' wsuf' v' heq hd' hr; subst; sis.
      rewrite app_assoc in hd'.
      apply gamma_derivation_nonterminal_end in hd'.
      destruct hd' as [wpre''' [wsuf'' [vpre [v'' [heq'' [heq''' [hg' hs]]]]]]]; subst.
      eapply hu in hr; eauto.
      inv hw. rewrite app_nil_r in *.
      eapply frames_derivation__gamma_derivation in hd.
      simpl in hd.
      eapply hu with (v' := (procVals l0 ++ sem0) ++ sem) in hr; eauto.
      * destruct hr as [? [? ?]]; subst.
        repeat split; auto.
        rewrite app_assoc in hd'.
        apply gamma_derivation_nonterminal_end in hd'.
        destruct hd' as [wpre'' [wsuf [vpre [v'' [heq' [heq'' [hg hs]]]]]]]; subst.
        inv hs.
        
      assert (gamma_derivation g rpre wsuf v'') by admit.
      assert (gamma_derivation g ((procSyms l0 ++ rpre0) ++ rpre) (wpre'' ++ wsuf) (vpre ++ v'')) by admit.
      inv hd.
      eapply frames_derivation_inv_cons in H10.
      destruct H10 as [wpre [wsuf'' [? [? ?]]]]; subst.
      eapply hu in H0; eauto.
      destruct H0 as [? [? ?]]; subst.
      repeat split; auto.
      inv hd.
      inv hs.
      assert (rpre = ys) by admit; subst.
      assert (gamma_derivation g ((procSyms l0 ++ rpre0) ++ ys)
                               (
      inv hd.
      eapply gamma_derivation_split in hg.
      destruct hg as [w [w' [v [v' [? [? [hg hg']]]]]]]; subst.
      
      eapply hu with (v' := v ++ v' ++ v'') in hr; eauto.
      * destruct hr as [? [? ?]]; subst.
        repeat split; auto.
        apply app_inv_tail in heq. subst.
        
      assert (
      eapply hu in hg.
      eapply hu in hr; eauto.
      
      admit.
  - exists (wpre ++ [(t, l2)]); split; auto.
    + apps.
    + split.
      * eapply consume_preserves_stack_derivation; eauto.
      * (* uniqueness part *)
        intros hu' wpre' wsuf' v' heq hd' hr; subst; sis.
        rewrite app_assoc in hd'.
        apply gamma_derivation_terminal_end in hd'.
        destruct hd' as [w_front [l' [v_front [? [? hd']]]]]; subst.
        eapply hu with (wpre' := w_front)
                       (wsuf' := (t, l') :: wsuf') in hd'; eauto.
        -- destruct hd' as [? [? ?]]; subst.
           inv H0.
           repeat split; auto.
           apps.
        -- rewrite heq. apps.
        -- assert ((t,l') :: wsuf' = [(t,l')] ++ wsuf') by auto.
           rewrite H; auto.
  - exists wpre; split; auto.
    split.
    + eapply push_preserves_stack_derivation; eauto.
    + (* uniqueness part *)
      intros hu' wpre' wsuf' v' ? hd' hr; sis.
      rewrite app_nil_r in *.
      eapply hu with (v' := v') in hu'; eauto.
      apply llPredict_succ_in_grammar in h5.
      apply gamma_recognize_split in hr.
      destruct hr as [w [w' [? [hr hr']]]]; subst; eauto.
  - exists wpre; split; auto.
    split.
    + eapply push_preserves_stack_derivation; eauto.
    + (* u is false *)
      intros hc; inv hc.
Admitted.

(* Note: using st here, as opposed to the deconstructed components, seems to work well *)
(*Inductive unique_stack_prefix_derivation g st w : Prop :=
| USPD :
    forall av stk wpre wsuf u,
      st = Pst av stk wsuf u
      -> wpre ++ wsuf = w
      -> stack_derivation g stk wpre 
      -> (u = true
          -> (forall wpre' wsuf' v',
                 wpre' ++ wsuf' = w
                 -> gamma_derivation g (procStackSyms stk) wpre' v'
                 -> gamma_recognize g (unprocStackSyms' stk) wsuf'
                 -> wpre' = wpre /\ wsuf' = wsuf /\ v' = (stackVals stk)))
      -> unique_stack_prefix_derivation g st w.
*)
Lemma step_preserves_uspd :
  forall g st st' w,
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> unique_stack_prefix_derivation g st w
    -> step g st = StepK st'
    -> unique_stack_prefix_derivation g st' w.
Proof.
  intros g [av stk ts u] [av' stk' ts' u'] w hn hw hu hs.
  unfold step in hs; dmeqs h; tc; inv hs.
  - (* return case *)
    sis.
    econstructor; eauto.
    inv hu. inv H. sis.
    econstructor; eauto.
    + sis.
      eapply gamma_derivation_split in H1.
      destruct H1 as [w [w' [v [v' [? [? [hd hd']]]]]]]; subst.
      apply gamma_derivation_split in hd.
      destruct hd as [w'' [w''' [v'' [v''' [? [? [hd hd'']]]]]]]; subst.
      inv hw.
    admit. 
    + admit.
  - (* consume case *)
    inv hu. inv H; sis.
    eapply USPD with (wpre := wpre ++ [(t, l2)]); eauto; sis.
    + apps.
    + sis.
      (* lemma *)
      repeat rewrite app_assoc. apply gamma_derivation_app; auto.
      assert ([(t, l2)] = [(t, l2)] ++ []) by apps.
      rewrite H; eauto.
    + intros.
      rewrite app_assoc in H3.
      apply gamma_derivation_terminal_end in H3.
      destruct H3 as [wfront [l' [vfront [? [? hg]]]]]; subst.
      eapply H2 in hg; eauto.
      * destruct hg as [? [? ?]]; subst.
        rewrite <- app_assoc in H0.
        apply app_inv_head in H0.
        inv H0.
        repeat split; auto.
        apps.
      * rewrite <- app_assoc in H0. rewrite <- H0. eauto.
      * constructor; auto.
  - (* PredSucc case *)
    sis.
    inv hu. inv H. sis.
    econstructor; eauto.
    + sis.
      repeat rewrite app_nil_r; auto.
    + intros hu wpre' wsuf' v' heq hd hr. sis.
      rewrite app_nil_r in *.
      eapply H2 with (v' := v') in hu ; eauto.
      pose proof h5 as hll.
      apply llPredict_succ_in_grammar in hll.
      eapply gamma_recognize_split in hr.
      destruct hr as [w [w' [? [hr hr']]]]; subst.
      econstructor; eauto.
  - (* PredAmbig case *)
    sis.
    inv hu. inv H. sis.
    econstructor; eauto.
    + sis. repeat rewrite app_nil_r in *. auto.
    + intros hc; inv hc.
Admitted.

Lemma uspd_starts_true :
  forall g ys ts,
    unique_stack_prefix_derivation g (mkInitState g ys ts) ts.
Proof.
  intros g ys ts.
  unfold mkInitState; sis.
  eapply USPD with (wpre := []); eauto.
  intros ? wpre' wsuf' v' heq hd hr; sis; subst.
  inv hd; repeat split; auto.
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
    -> stack_wf g stk
    -> unique_stack_prefix_derivation g (Pst av stk wsuf u) w
    -> multistep g (Pst av stk wsuf u) a' = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v
       /\ (forall v',
              gamma_derivation g (bottomFrameSyms stk) w v'
              -> v' = v).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros w wsuf av stk u a' v heq hw hi hm; subst.
  apply multistep_accept_cases in hm.
  destruct hm as [[hf hu] | he].
  - apply step_StepAccept_facts in hf.
    destruct hf as [[xo [rpre [v' [heq]]]] heq']; subst.
    unfold bottomFrameSyms; simpl; rewrite app_nil_r.
    inv hi.
    inv H.
    rewrite app_nil_r in *.
    sis.
    split; auto.
    intros.
    eapply H2 with (wsuf' := []) in H; eauto.
    + destruct H as [? [? ?]]; auto.
    + apply app_nil_r.
  - destruct he as [st' [a'' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_uspd; eauto.
Abort.

Theorem parse_sound_unambig :
  forall (g  : grammar)
         (ys : list symbol)
         (ts : list token)
         (v  : forest),
    parse g ys ts = Accept v
    -> gamma_derivation g ys ts v
       /\ (forall v',
              gamma_derivation g ys ts v'
              -> v' = v).
Proof.
  intros g ys ts v hp.
  unfold parse in hp.
  eapply multistep_sound in hp; eauto.
Abort.
(*  - apply lex_nat_triple_wf.
  - constructor. (* how do I get auto to take care of this? *)
  - apply stack_prefix_derivation_init. 
Qed. *)

(*
Inductive unique_stack_prefix_derivation g stk wsuf u w : Prop :=
| USPD :
    forall wpre,
      wpre ++ wsuf = w
      -> gamma_derivation g (procStackSyms stk) wpre (stackVals stk)
      -> (u = true
          -> (forall wpre' wsuf' v',
                 wpre' ++ wsuf' = w
                 -> gamma_derivation g (procStackSyms stk) wpre' v'
                 -> gamma_recognize g (unprocStackSyms' stk) wsuf'
                 -> wpre' = wpre /\ wsuf' = wsuf /\ v' = (stackVals stk)))
      -> unique_stack_prefix_derivation g stk wsuf u w.

Inductive unique_stack_prefix_derivation g stk wsuf w :=
| USPD :
    forall wpre,
      wpre ++ wsuf = w
      -> gamma_derivation g (procStackSyms stk) wpre (stackVals stk)
      -> (forall wpre' wsuf' v',
             wpre' ++ wsuf' = w
             -> gamma_derivation g (procStackSyms stk) wpre' v'
             -> gamma_recognize g (unprocStackSyms' stk) wsuf'
             -> wpre' = wpre /\ wsuf' = wsuf /\ v' = (stackVals stk))
      -> unique_stack_prefix_derivation g stk wsuf w.


Lemma uspd_starts_true :
  forall g ys ts,
    unique_stack_prefix_derivation g (mkInitState g ys ts).(stack) ts ts.
Proof.
  intros g ys ts.
  unfold mkInitState; sis.
  eapply USPD with (wpre := []); eauto.
  intros wpre' wsuf' v' heq hd hr; sis; subst.
  inv hd; repeat split; auto.
Qed.
*)
(*
Inductive all_pushes_unique (g : grammar) : list frame -> list token -> Prop :=
| APU_empty :
    forall w,
    all_pushes_unique g [] w
| APU_bottom :
    forall fr w,
      all_pushes_unique g [fr] w
| APU_upper :
    forall o o' pre pre' suf suf' v v' x frs w,
      all_pushes_unique g (Fr (Loc o pre (NT x :: suf)) v :: frs) w
      -> (forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ 
             -> gamma_recognize g (suf ++ unprocTailSyms' frs) w'
             -> rhs = pre' ++ suf')
      -> all_pushes_unique g (Fr (Loc o' pre' suf') v' ::
                              Fr (Loc o  pre  (NT x :: suf )) v  ::
                              frs) (w ++ w').

Hint Constructors all_pushes_unique.

Definition all_stack_pushes_unique g (stk : parser_stack) w :=
  let (fr, frs) := stk in all_pushes_unique g (fr :: frs) w.

Definition all_stack_pushes_unique_invar g st :=
  match st with
  | Pst av stk ts u =>
    if u then all_stack_pushes_unique g stk ts else True
  end.
      
Lemma return_preserves_apu_invar :
  forall g fr cr cr' frs o o' pre pre' x suf' v v' v'' w,
    fr     = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') v''
    -> stack_wf g (fr, cr :: frs)
    -> all_stack_pushes_unique g (fr, cr :: frs) w
    -> all_stack_pushes_unique g (cr', frs) w.
Proof.
  intros g fr cr cr' frs o o' pre pre' x suf' v v' v'' w ? ? ? hw hu; subst; sis.
  inv hw.
  inv hu.
  destruct frs as [| fr' frs]; auto.
  destruct fr' as [[o'' pre'' suf''] v''']; sis.
  inv H12.
  constructor; auto.
  intros.
  apply H14 in H; auto.
  subst.
  apps.
Qed.

Lemma consume_preserves_apu_invar :
  forall g fr fr' frs o pre suf a l ts' v,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> stack_wf g (fr, frs)
    -> all_stack_pushes_unique g (fr, frs) ((a,l) :: ts')
    -> all_stack_pushes_unique g (fr', frs) ts'.
Proof.
  intros g fr fr' frs o pre suf a l ts' v ? ? hw hu; subst; sis.
  destruct frs as [| fr' frs]; auto.
  inv hw.
  inv hu; sis.
  rewrite H9 in H2.
  inv H2.
  - 
    constructor.
  econstructor.
  sis.
  destruct fr' as [[o' pre' suf'] v'].
  simpl in H3.
  rewrite <- H3.
  constructor.
  inv hu.
  constructor; auto.
  inv H6; auto.
  constructor; auto.
  inv H6.
  inv H5.
  constructor; auto.
    -> stack_derivation g (fr', frs) (w ++ [(a, l)]).
Proof.




Lemma return_preserves_ussr :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' w,
    ce = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> unproc_stack_syms_recognize g (ce, cr :: frs) w
    -> unproc_stack_syms_recognize g (cr', frs) w.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' w
         ? ? ? hs; subst.
  apply ussr_inv in hs.
  destruct hs as [wpre [wsuf [heq [hg ht]]]]; subst.
  inv ht; inv hg; simpl; auto.
Qed.

Lemma consume_preserves_ussr :
  forall g fr fr' frs o pre suf a l v w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> unproc_stack_syms_recognize g (fr, frs) ((a, l) :: w)
    -> unproc_stack_syms_recognize g (fr', frs) w.
Proof.
  intros g fr fr' frs o pre suf a l v w ? ? hs; subst.
  apply ussr_inv in hs.
  destruct hs as [wpre [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_terminal_head in hg.
  destruct hg as [l' [w' [? hg]]]; subst.
  inv heq; auto.
Qed.

(* replace this with something better *)
Lemma unproc_tail_syms_unprocTailSyms :
  forall g frs w,
    unproc_tail_syms_recognize g frs w
    -> gamma_recognize g (unprocTailSyms (map loc frs)) w.
Proof.
  intros g frs; induction frs as [| fr frs IH]; intros w hu; sis; inv hu; auto.
  sis. apply gamma_recognize_app; auto.
Qed.

Lemma push_succ_preserves_ussr :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) w = PredSucc rhs
    -> unproc_stack_syms_recognize g (fr, frs) w
    -> unproc_stack_syms_recognize g (Fr (Loc (Some x) [] rhs) [], fr :: frs) w.
Proof.
  intros g fr o pre x suf v frs w rhs heq hn hw hl hu; subst; sis.
  eapply ussr_inv in hu.
  destruct hu as [wpremid [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_nonterminal_head in hg.
  destruct hg as [rhs' [wpre [wmid [heq [hin [hg hg']]]]]]; subst.
  rewrite <- app_assoc; constructor; auto.
  eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
  - subst; auto.
  - sis.
    rewrite <- app_assoc.
    do 2 (apply gamma_recognize_app; auto).
    apply unproc_tail_syms_unprocTailSyms; auto.
Qed.

Lemma push_ambig_preserves_ussr :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> no_left_recursion g
    -> stack_wf g (fr, frs)
    -> llPredict g x (lstackOf (fr, frs)) w = PredAmbig rhs
    -> unproc_stack_syms_recognize g (fr, frs) w
    -> unproc_stack_syms_recognize g (Fr (Loc (Some x) [] rhs) [], fr :: frs) w.
Proof.
  intros g fr o pre x suf v frs w rhs ? hn hw hl hu; subst; sis.
  eapply ussr_inv in hu.
  destruct hu as [wpremid [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_nonterminal_head in hg.
  destruct hg as [rhs' [wpre [wmid [heq [hin [hg hg']]]]]]; subst.
  eapply llPredict_ambig_rhs_unproc_stack_syms in hl; eauto; sis.
  rewrite <- app_assoc in *.
  constructor.
  

Lemma step_preserves_ussr :
  forall g av av' stk stk' w w' u u',
    no_left_recursion g
    -> stack_wf g stk
    -> unproc_stack_syms_recognize g stk w
    -> step g (Pst av stk w u) = StepK (Pst av' stk' w' u')
    -> unproc_stack_syms_recognize g stk' w'.
Proof.
  intros g av av' stk stk' w w' u u' hn hw hu hs.
  unfold step in hs; dmeqs h; tc; inv hs; sis.
  - eapply return_preserves_ussr; eauto.
  - eapply consume_preserves_ussr; eauto.
  - eapply push_succ_preserves_ussr; eauto.
  - admit.
Admitted.

Fixpoint processedSyms' (frs : list location) : list symbol :=
  match frs with 
  | [] => []
  | Loc o pre suf :: frs' => processedSyms' frs' ++ pre
  end.

Definition processedSyms stk : list symbol :=
  match stk with
  | (fr, frs) => processedSyms' (fr :: frs)
  end.

Fixpoint unprocTailSyms (frs : list location) : list symbol :=
  match frs with 
  | []                            => []
  | Loc _ _ [] :: _               => [] (* impossible *)
  | Loc _ _ (T _ :: _) :: _       => [] (* impossible *)
  | Loc _ _ (NT x :: suf) :: frs' => suf ++ unprocTailSyms frs'
  end.

Definition unprocStackSyms stk : list symbol :=
  match stk with
  | (Loc o pre suf, frs) => suf ++ unprocTailSyms frs
  end.

Inductive gamma_recognizes_prefix g gamma wpre w : Prop :=
| GRP :
    forall wsuf,
      gamma_recognize g gamma wpre
      -> w = wpre ++ wsuf
      -> gamma_recognizes_prefix g gamma wpre w.

Lemma llPredict'_succ_exists_unique_viable_unproc_prefix :
  forall g orig_stk o pre x suf frs w'' w' sps rhs,
    orig_stk = (Loc o pre (NT x :: suf), frs)
    -> llPredict' g w'' sps = PredSucc rhs
    -> (forall sp, 
           In sp sps 
           -> match sp with
              | Sp av pred stk => 
                exists orig_unproc_pre orig_unproc_suf new_proc_syms,
                orig_unproc_pre ++ orig_unproc_suf = pred ++ suf ++ unprocTailSyms frs
                /\ processedSyms stk = processedSyms orig_stk ++ new_proc_syms
                /\ gamma_recognize g new_proc_syms w'
                /\ (forall w, gamma_recognize g new_proc_syms w -> gamma_recognize g orig_unproc_pre w)
              end)
    -> exists upre usuf wpre wsuf,
        upre ++ usuf = rhs ++ suf ++ unprocTailSyms frs
        /\ wpre ++ wsuf = w' ++ w''
        /\ gamma_recognize g upre wpre
        /\ forall upre' usuf' wpre' wsuf',
            upre ++ usuf = upre' ++ usuf'
            -> wpre ++ wsuf = wpre' ++ wsuf'
            -> gamma_recognize g upre' wpre'
            -> upre = upre' /\ wpre = wpre'.
Proof.
  intros g orig_stk o pre x suf frs w''.
  induction w'' as [| t w'' IH]; intros w' sps rhs ho hl ha; subst.
  - unfold llPredict' in hl.
    eapply handleFinalSubparsers_facts in hl.
    destruct hl as [sp [o' [pre' [hin [heq heq']]]]]; subst.
    apply ha in hin; clear ha.
    destruct sp as [av pred stk]; sis; subst.
    destruct hin as [orig_unproc_pre [orig_unproc_suf [new_proc_syms [heq [heq' [heq'' hequiv]]]]]]; sis; subst.
    apply hequiv in heq''.
    exists orig_unproc_pre.
    exists orig_unproc_suf.
    exists w'.
    exists [].
    split; auto.
    split; auto.
    split; auto.
    intros upre' usuf' wpre' wsuf' ho heq''' hg.
    rewrite app_nil_r in *; subst.
Abort.

Definition gamma_recog_subset g ys ys' :=
  forall w, gamma_recognize g ys w -> gamma_recognize g ys' w.

Lemma start_state_init_invar :
  forall g fr o pre x suf frs w sp,
    fr = Loc o pre (NT x :: suf)
    -> gamma_recognize g (NT x :: suf ++ unprocTailSyms frs) w
    -> exists sp,
        In sp (map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, fr :: frs))
                   (rhssForNt g x))
        /\ gamma_recognize g (unprocStackSyms sp.(stack)) w.

                     
In sp'
          (map
             (fun rhs : list symbol =>
              {|
              Prediction.avail := allNts g;
              prediction := rhs;
              Prediction.stack := ({|
                                   lopt := Some x;
                                   rpre := [];
                                   rsuf := rhs |},
                                  {|
                                  lopt := o;
                                  rpre := pre;
                                  rsuf := NT x :: suf |}
                                  :: frs) |}) 
             (rhssForNt g x))


Lemma startState_invar :
  forall g x fr o pre suf frs sp sps,
    fr = Loc o pre (NT x :: suf)
    -> startState g x (fr, frs) = inr sps
    -> In sp sps
    -> False.
Proof.
  intros g x fr o pre suf frs sp sps heq hs hi; subst.
  unfold startState in hs.
  eapply aggrClosureResults_succ_in_input in hs; eauto.
  destruct hs as [orig_sps [hin hin']].
  apply in_map_iff in hin.
  destruct hin as [sp' [heq hin]].
  apply in_map_iff in hin.
  destruct hin as [rhs [heq' hin]]; subst.

Lemma llPredict_succ_thing :
  forall g fr o pre x suf frs w rhs,
    fr = Loc o pre (NT x :: suf)
    -> llPredict g x (fr, frs) w = PredSucc rhs
    -> exists wpre,
      forall rhs' wpre' wsuf',
        In (x, rhs') g
        -> w = wpre' ++ wsuf'
        -> gamma_recognize g rhs' wpre'
        -> gamma_recognize g (suf ++ unprocTailSyms frs) wsuf'
        -> wpre' = wpre /\ rhs' = rhs.
Proof.
  intros g fr o pre x suf frs w rhs heq hl; subst.
  unfold llPredict in hl.

    exists upre usuf wpre wsuf,
        upre ++ usuf = rhs ++ suf ++ unprocTailSyms frs
        /\ wpre ++ wsuf = w
        /\ gamma_recognize g upre wpre
        /\ forall upre' usuf' wpre' wsuf',
            upre ++ usuf = upre' ++ usuf'
            -> wpre ++ wsuf = wpre' ++ wsuf'
            -> gamma_recognize g upre' wpre'
            -> upre = upre' /\ wpre = wpre'.
Proof.
  intros g fr o pre x suf frs w rhs heq hl; subst.
  unfold llPredict in hl.
  destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
  
Admitted.    

Lemma llPredict_succ_exists_unique_viable_unproc_prefix :
  forall g fr o pre x suf frs w rhs,
    fr = Loc o pre (NT x :: suf)
    -> llPredict g x (fr, frs) w = PredSucc rhs
    -> exists upre usuf wpre wsuf,
        upre ++ usuf = rhs ++ suf ++ unprocTailSyms frs
        /\ wpre ++ wsuf = w
        /\ gamma_recognize g upre wpre
        /\ forall upre' usuf' wpre' wsuf',
            upre ++ usuf = upre' ++ usuf'
            -> wpre ++ wsuf = wpre' ++ wsuf'
            -> gamma_recognize g upre' wpre'
            -> upre = upre' /\ wpre = wpre'.
Proof.
  intros g fr o pre x suf frs w rhs heq hl; subst.
  unfold llPredict in hl.
  destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
  
Admitted.

Lemma push_succ_preserves_ussr :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> llPredict g x (lstackOf (fr, frs)) w = PredSucc rhs
    -> unproc_stack_syms_recognize g (fr, frs) w
    -> unproc_stack_syms_recognize g (Fr (Loc (Some x) [] rhs) [], fr :: frs) w.
Proof.
  intros g fr o pre x suf v frs w rhs heq hl hs; subst; sis.
  eapply ussr_inv in hs.
  destruct hs as [wpremid [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_nonterminal_head in hg.
  destruct hg as [rhs' [wpre [wmid [heq [hin [hg hg']]]]]]; subst.
  rewrite <- app_assoc; constructor; auto.
  eapply llPredict_succ_exists_unique_viable_unproc_prefix in hl; eauto.
  destruct hl as [upre [usuf [wpre' [wsuf' [heq [heq' [hg'' hall]]]]]]].
Admitted.

Lemma step_preserves_ussr :
  forall g av av' stk stk' w w' u u',
    unproc_stack_syms_recognize g stk w
    -> step g (Pst av stk w u) = StepK (Pst av' stk' w' u')
    -> unproc_stack_syms_recognize g stk' w'.
Proof.
  intros g av av' stk stk' w w' u u' hi hs.
  unfold step in hs; dmeqs h; tc; inv hs; sis.
  - eapply return_preserves_ussr; eauto.
  - eapply consume_preserves_ussr; eauto.
  - eapply push_succ_preserves_ussr; eauto.
  - admit.
Admitted.

Lemma ussr_implies_multistep_doesn't_reject :
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
    -> unproc_stack_syms_recognize g stk w
    -> multistep g (Pst av stk w u) a <> Reject s.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros av stk w u a s heq hu; unfold not; intros hm; subst.
  apply multistep_reject_cases in hm.
  destruct hm as [hs | [st' [a' [hs hm]]]]. 
  - (* lemma *)
    clear a hlt IH.
    unfold step in hs; dmeqs h; tc; inv hs.
    + inv hu.
      inv H1; inv H6.
      inv H5.
    + inv hu.
      inv H1.
      inv H2.
      inv H5.
    + inv hu.
      inv H1.
      inv H2.
      inv H5.
      apply n; auto.
    + inv hu.
      inv H5.
      inv H1.
      admit.
    + inv hu.
      inv H5.
      inv H1.
      assert (In n (lhss g)) by admit.
      apply in_lhss_iff_in_allNts in H.
      apply NtSet.mem_spec in H.
      rewrite H in h5; inv h5.
  - destruct st' as [av' stk' w' u']. 
    eapply IH with (y := meas g (Pst av' stk' w' u')); eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_ussr; eauto.
Admitted.

Theorem valid_derivation_implies_parser_doesn't_reject :
  forall g ys w s,
    gamma_recognize g ys w
    -> parse g ys w <> Reject s.
Proof.
  intros g ys w s hg; unfold not; intros hp.
  unfold parse in hp.
  unfold mkInitState in hp.
  eapply ussr_implies_multistep_doesn't_reject; eauto.
  - apply lex_nat_triple_wf.
  - (* lemma *)
    rew_nil_r w; auto.
Qed.

(* a thought: maybe replace this invariant with a function of
   the stack, i.e., "unprocessed symbols" *)

Inductive tail_frames_recognize (g : grammar) : list frame -> list token -> Prop :=
| TFR_nil :
    tail_frames_recognize g [] []
| TFR_cons :
    forall o pre x suf v w w' frs,
      gamma_recognize g suf w
      -> tail_frames_recognize g frs w'
      -> tail_frames_recognize g (Fr (Loc o pre (NT x :: suf)) v :: frs) (w ++ w').

Hint Constructors tail_frames_recognize.

(*Inductive stack_recognize (g : grammar) : parser_stack -> list token -> Prop :=
| SR :
    forall o pre suf v w w' frs,
      gamma_recognize g suf w
      -> tail_frames_recognize g frs w'
      -> stack_recognize g (Fr (Loc o pre suf) v, frs) (w ++ w').

Hint Constructors stack_recognize.

Lemma stack_recognize_inv :
  forall g o pre suf v frs w'',
    stack_recognize g (Fr (Loc o pre suf) v, frs) w''
    -> exists w w',
      w'' = w ++ w'
      /\ gamma_recognize g suf w
      /\ tail_frames_recognize g frs w'.
Proof.
  intros g o pre suf v frs w'' hs; inv hs; eauto.
Qed.

Lemma return_preserves_stack_recognize :
  forall g ce cr cr' frs x o o' pre pre' suf' v v' w,
    ce = Fr (Loc o pre []) v
    -> cr  = Fr (Loc o' pre' (NT x :: suf')) v'
    -> cr' = Fr (Loc o' (pre' ++ [NT x]) suf') (v' ++ [Node x v])
    -> stack_recognize g (ce, cr :: frs) w
    -> stack_recognize g (cr', frs) w.
Proof.
  intros g ce cr cr' frs x o o' pre pre' suf' v v' w
         ? ? ? hs; subst.
  apply stack_recognize_inv in hs.
  destruct hs as [wpre [wsuf [heq [hg ht]]]]; subst.
  inv ht; inv hg; simpl; auto.
Qed.

Lemma gamma_recognize_terminal_head :
  forall g a suf w,
    gamma_recognize g (T a :: suf) w
    -> exists l w',
      w = (a, l) :: w'
      /\ gamma_recognize g suf w'.
Proof.
  intros g a suf w hg.
  inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
  inv hs; simpl; eauto.
Qed.

Lemma consume_preserves_stack_recognize :
  forall g fr fr' frs o pre suf a l v w,
    fr = Fr (Loc o pre (T a :: suf)) v
    -> fr' = Fr (Loc o (pre ++ [T a]) suf) (v ++ [Leaf l])
    -> stack_recognize g (fr, frs) ((a, l) :: w)
    -> stack_recognize g (fr', frs) w.
Proof.
  intros g fr fr' frs o pre suf a l v w ? ? hs; subst.
  apply stack_recognize_inv in hs.
  destruct hs as [wpre [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_terminal_head in hg.
  destruct hg as [l' [w' [? hg]]]; subst.
  inv heq; auto.
Qed.

Lemma gamma_recognize_nonterminal_head :
  forall g x suf w,
    gamma_recognize g (NT x :: suf) w
    -> exists rhs wpre wsuf,
      w = wpre ++ wsuf
      /\ In (x, rhs) g
      /\ gamma_recognize g rhs wpre
      /\ gamma_recognize g suf wsuf.
Proof.
  intros g x suf w hg.
  inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
  inv hs; simpl; eauto 8.
Qed.

Lemma push_succ_reserves_stack_derivation :
  forall g fr o pre x suf v frs w rhs,
    fr = Fr (Loc o pre (NT x :: suf)) v
    -> llPredict g x (lstackOf (fr, frs)) w = PredSucc rhs
    -> stack_recognize g (fr, frs) w
    -> stack_recognize g (Fr (Loc (Some x) [] rhs) [], fr :: frs) w.
Proof.
  intros g fr o pre x suf v frs w rhs heq hl hs; subst; sis.
  eapply stack_recognize_inv in hs.
  destruct hs as [wpremid [wsuf [heq [hg ht]]]]; subst.
  apply gamma_recognize_nonterminal_head in hg.
  destruct hg as [rhs' [wpre [wmid [heq [hin [hg hg']]]]]]; subst.
  rewrite <- app_assoc; constructor; auto.
  eapply llPredict_succ_viable_prefix in hl; eauto.
  - destruct hl as [vp [vs [wpre' [wsuf' [heq [heq' [hg'' [hg''' hall]]]]]]]].
    pose proof hg as hg''''.
    eapply hall with (viable_prefix' := rhs')
                     (viable_suffix' := (suf ++ flat_map rsuf (map loc frs)))
                     (wsuf' := wmid ++ wsuf) in hg; clear hall; eauto.
    subst.
    simpl in heq'.
    rewrite <- app_assoc in heq'.
    apply app_inv_head in heq'.
    subst.
  unfold llPredict in hl.
  
  
  
Admitted.

Lemma step_preserves_stack_recognize :
  forall g av av' stk stk' w w' u u',
    stack_recognize g stk w
    -> step g (Pst av stk w u) = StepK (Pst av' stk' w' u')
    -> stack_recognize g stk' w'.
Proof.
  intros g av av' stk stk' w w' u u' hi hs.
  unfold step in hs; dmeqs h; tc; inv hs; sis.
  - eapply return_preserves_stack_recognize; eauto.
  - eapply consume_preserves_stack_recognize; eauto.
  - eapply push_succ_reserves_stack_derivation; eauto.
  - admit.

Inductive unprocessed_syms_recognize_suffix (g : grammar) wpre (stk : parser_stack) (w : list token) : Prop :=
| USRS :
    forall (wsuf : list token),
      stack_recognize g stk wsuf
      -> w = wpre ++ wsuf
      -> unprocessed_syms_recognize_suffix g wpre stk w.
    
(* to do : prove that the above property is a parser invariant *)


Lemma parser_doesn't_reject_valid_input :
  forall g ys w v s,
    gamma_derivation g ys w v
    -> parse g ys w <> Reject s.
Proof.
  intros g ys w v s hg; unfold not; intros hp.
  unfold parse in hp.
Admitted.

Lemma multistep_complete' :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (wsuf w : list token)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g (Pst av stk wsuf u)))
         (v      : forest)
         (sr     : step_result)
         (hs     : step g (Pst av stk wsuf u) = sr),
    tri = meas g (Pst av stk wsuf u)
    -> no_left_recursion g
    -> stack_wf g stk
    -> unavailable_nts_invar g (Pst av stk wsuf u)
    -> unique_gamma_derivation g (bottomFrameSyms stk) w v
    -> match sr as res return (step g (Pst av stk wsuf u) = res -> parse_result)
       with
       | StepAccept sv =>
         fun _ => if u then Accept sv else Ambig sv
       | StepReject s =>
         fun _ => Reject s
       | StepK st' =>
         fun hs => multistep g st' (StepK_st_acc g _ st' a' hs)
       | StepError s => fun _ => Error s
       end hs = Accept v.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros av stk wsuf w u a' v sr hs heq hn hw hu hun.
  destruct sr as [v' | s | [av' stk' wsuf' u'] | s]; subst.
  - apply step_StepAccept_facts in hs.
    destruct hs as [[o [pre [v'' [heq heq']]]] hnil]; subst.
    unfold bottomFrameSyms in hun; simpl in hun; rewrite app_nil_r in hun.
    (* we need an invariant stating that the stack 
       captures a unique derivation *)
    admit.
  - admit.
  - rewrite multistep_unfold.
    eapply IH; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_unavailable_nts_invar; eauto.
    + apply step_preserves_bottomFrameSyms_invar in hs.
      rewrite <- hs; eauto.
  - (* lemma *)
    exfalso.
    destruct s.
    + eapply stack_wf_no_invalid_state; eauto.
    + apply step_left_recursion_detection_sound in hs; auto.
      eapply hn; eauto.
    + destruct p.
      * eapply step_never_returns_SpInvalidState; eauto.
        simpl; auto.
      * eapply step_never_returns_SpLeftRecursion; eauto.
        simpl; auto.
Admitted.

Lemma multistep_complete :
  forall (g      : grammar)
         (st     : parser_state)
         (w      : list token)
         (v      : forest)
         (a      : Acc lex_nat_triple (meas g st)),
    (* might need some more parser invariants here *)
    no_left_recursion g
    -> stack_wf g st.(stack)
    -> unavailable_nts_invar g st
    -> unique_gamma_derivation g (bottomFrameSyms st.(stack)) w v
    -> multistep g st a = Accept v.
Proof.
  intros g [av stk wsuf u] w v a hn hw hu hu'; sis.
  rewrite multistep_unfold.
  eapply multistep_complete'; eauto.
Qed.

Theorem parser_complete :
  forall g ys w v,
    no_left_recursion g
    -> unique_gamma_derivation g ys w v
    -> parse g ys w = Accept v.
Proof.
  intros g ys w v hn hu.
  unfold parse.
  eapply multistep_complete with (w := w); eauto.
  - (* lemma *)
    constructor.
  - apply unavailable_nts_invar_starts_true.
Qed.
    