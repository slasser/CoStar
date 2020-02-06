Require Import Arith Bool List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Prediction_complete.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.

Inductive frames_wf (g : grammar) : list prefix_frame -> list suffix_frame -> Prop :=
| WF_bottom :
    forall pre suf v,
      frames_wf g [PF pre v] [SF suf]
| WF_upper :
    forall x pre pre' suf suf' p_frs s_frs v v',
    In (x, rev pre' ++ suf') g
    -> frames_wf g (PF pre v :: p_frs) 
                   (SF (NT x :: suf) :: s_frs)
    -> frames_wf g (PF pre' v' :: PF pre v :: p_frs) 
                   (SF suf' :: SF (NT x :: suf) :: s_frs).

Hint Constructors frames_wf.

Ltac inv_fw hw  hi hw' := 
  inversion hw as [? ? ? | ? ? ? ? ? ? ? ? ? hi hw']; subst; clear hw.

Lemma frames_wf__suffix_frames_wf :
  forall g p_frs s_frs,
    frames_wf g p_frs s_frs
    -> suffix_frames_wf g s_frs.
Proof.
  intros g pfrs sfrs hw; induction hw; eauto.
Qed.

Lemma return_preserves_frames_wf_invar :
  forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x v v',
    p_ce     = PF pre' v'
    -> s_ce  = SF []
    -> p_cr  = PF pre v
    -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
    -> frames_wf g (p_cr' :: p_frs) (s_cr' :: s_frs).
Proof.
  intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x v v'
         ? ? ? ? ? ? hw; subst; inv_fw hw hi hw'; rew_anr.
  inv_fw hw' hi' hw''; auto.
  econstructor; eauto; sis; apps.
Qed.

Lemma consume_preserves_frames_wf_invar :
  forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf a l v,
    p_fr     = PF pre v
    -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
    -> s_fr  = SF (T a :: suf)
    -> s_fr' = SF suf
    -> frames_wf g (p_fr :: p_frs) (s_fr :: s_frs) 
    -> frames_wf g (p_fr' :: p_frs) (s_fr' :: s_frs).
Proof.
  intros g ? ? ? ? p_frs s_frs pre suf a l v ? ? ? ? hw; subst; 
    inv_fw hw hi hw'; auto.
  econstructor; eauto; sis; apps.
Qed.

Lemma push_preserves_frames_wf_invar :
  forall g p_cr p_ce s_cr s_ce p_frs s_frs x rhs pre suf v,
    p_cr     = PF pre v
    -> p_ce  = PF [] []
    -> s_cr  = SF (NT x :: suf)
    -> s_ce  = SF rhs
    -> In (x, rhs) g
    -> frames_wf g (p_cr :: p_frs) (s_cr :: s_frs) 
    -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs).
Proof.
  intros g ? ? ? ? p_frs s_frs x rhs pre suf v ? ? ? ? hi hf; subst; auto.
Qed.    

Definition stacks_wf g p_stk s_stk := 
  match p_stk, s_stk with
  | (p_fr, p_frs), (s_fr, s_frs) => frames_wf g (p_fr :: p_frs) (s_fr :: s_frs)
  end.

Lemma step_preserves_stacks_wf_invar :
  forall g ps ps' ss ss' ts ts' av av' u u',
    stacks_wf g ps ss
    -> step g ps ss ts av u = StepK ps' ss' ts' av' u'
    -> stacks_wf g ps' ss'.
Proof.
  intros g (pfr, pfrs) (pfr', pfrs') (sfr, sfrs) (sfr', sfrs')
         ts ts' av av' u u' hw hs; red; red in hw.
  unfold step in hs; dmeqs h; tc; inv hs.
  - eapply return_preserves_frames_wf_invar; eauto. 
  - eapply consume_preserves_frames_wf_invar; eauto. 
  - eapply push_preserves_frames_wf_invar; eauto. 
    eapply llPredict_succ_in_grammar; eauto.
  - eapply push_preserves_frames_wf_invar; eauto.
    eapply llPredict_ambig_in_grammar; eauto.
Qed.

Lemma step_preserves_bottomFrameSyms_invar :
  forall g p_stk p_stk' s_stk s_stk' ts ts' av av' u u',
    stacks_wf g p_stk s_stk
    -> step g p_stk s_stk ts av u = StepK p_stk' s_stk' ts' av' u'
    -> bottomFrameSyms p_stk s_stk = bottomFrameSyms p_stk' s_stk'.
Proof.
  intros g (p_fr, p_frs) p_stk' (s_fr, s_frs) s_stk' ts ts' av av' u u' hw hs.
  unfold step in hs; dms; inv hs; tc; unfold bottomFrameSyms;
    destruct p_frs; destruct s_frs; sis; apps; inv_fw hw hi hw'; inv hw'. 
Qed.

(* The stronger parser soundness theorems -- one for unique derivations, one for
   ambiguous derivations, appear below. *)

Inductive frames_derivation (g : grammar) :
  list prefix_frame -> list suffix_frame -> list token -> list token -> Prop :=
| FD_nil :
    forall wsuf,
    frames_derivation g [] [] [] wsuf
| FD_bottom  :
    forall pre suf wpre wsuf v,
      gamma_derivation g (rev pre) wpre (rev v)
      -> frames_derivation g [PF pre v] [SF suf] wpre wsuf
| FD_upper :
    forall p_cr p_frs s_cr s_frs x pre' suf suf' v' wpre wmid wsuf,
      SF (NT x :: suf) = s_cr
      -> In (x, rev pre' ++ suf') g
      -> gamma_derivation g (rev pre') wmid (rev v')
      -> frames_derivation g (p_cr :: p_frs)
                             (s_cr :: s_frs)
                             wpre (wmid ++ wsuf)
      -> frames_derivation g (PF pre' v' :: p_cr :: p_frs)
                             (SF suf'    :: s_cr :: s_frs)
                             (wpre ++ wmid) wsuf.

Hint Constructors frames_derivation.

Ltac inv_fd hf hf':=
  let heq := fresh "heq" in
  let hi  := fresh "hi"  in
  let hg  := fresh "hg"  in
  inversion hf as [ ?
                  | ? ? ? ? ? hg 
                  | ? ? ? ? ? ? ? ? ? ? ? ? heq hi hg hf']; subst; clear hf.

Lemma fd_inv_cons :
  forall g p_fr s_fr p_frs s_frs pre suf w wsuf v,
    p_fr    = PF pre v
    -> s_fr = SF suf
    -> frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) w wsuf
    -> exists wpre wmid,
        w = wpre ++ wmid
        /\ gamma_derivation g (rev pre) wmid (rev v)
        /\ frames_derivation g p_frs s_frs wpre (wmid ++ wsuf).
Proof.
  intros g ? ? p_frs s_frs pre suf w wsuf v ? ? hf; subst; inv hf; eauto.
  exists []; eexists; repeat split; eauto.
Qed.

Lemma return_preserves_frames_derivation :
  forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x v v' wpre wsuf,
    p_ce     = PF pre' v'
    -> s_ce  = SF []
    -> p_cr  = PF pre v
    -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> frames_derivation g (p_ce :: p_cr :: p_frs)
                           (s_ce :: s_cr :: s_frs)
                            wpre wsuf
    -> frames_derivation g (p_cr' :: p_frs)
                           (s_cr' :: s_frs)
                            wpre wsuf.
Proof.
  intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x v v' wpre wsuf
         ? ? ? ? ? ? hf; subst; inv_fd hf hf'.
  inv heq; rewrite app_nil_r in *; inv_fd hf' hf''.
  - constructor; sis.
    apply gamma_derivation_app; auto.
    rew_nil_r wmid; eauto.
  - rewrite <- app_assoc; econstructor; eauto; sis; apps.
    apply gamma_derivation_app; auto.
    rew_nil_r wmid; eauto.
Qed.

Lemma consume_preserves_frames_derivation :
  forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf a l v wpre wsuf,
    p_fr     = PF pre v
    -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
    -> s_fr  = SF (T a :: suf)
    -> s_fr' = SF suf
    -> frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                            wpre ((a, l) :: wsuf)
    -> frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs) 
                           (wpre ++ [(a, l)]) wsuf.
Proof.
  intros g ? ? ? ? p_frs s_frs pre suf a l v wpre wsuf
         ? ? ? ? hf; subst; inv hf.
  - constructor; sis.
    apply gamma_derivation_app; auto.
    rew_nil_r [(a, l)]; auto.
  - rewrite <- app_assoc; econstructor; eauto; sis; apps.
    apply gamma_derivation_app; auto.
    rew_nil_r [(a, l)]; auto.
Qed.

Lemma push_preserves_frames_derivation :
  forall g p_cr p_ce s_cr s_ce p_frs s_frs x rhs pre suf wpre wsuf v,
    p_cr     = PF pre v
    -> p_ce  = PF [] []
    -> s_cr  = SF (NT x :: suf)
    -> s_ce  = SF rhs
    -> In (x, rhs) g
    -> frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) 
                            wpre wsuf
    -> frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) 
                            wpre wsuf.
Proof.
  intros g ? ? ? ? p_frs s_frs x rhs pre suf wpre wsuf v ? ? ? ? hi hf; subst.
  rew_nil_r wpre; eauto.
Qed.    

Definition stack_prefix_derivation g w p_stk s_stk wsuf :=
  match p_stk, s_stk with
  | (p_fr, p_frs), (s_fr, s_frs) =>
    exists wpre,
    w = wpre ++ wsuf
    /\ frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) wpre wsuf
  end.

Lemma step_preserves_stack_prefix_derivation :
  forall g w ps ps' ss ss' ts ts' av av' u u',
    stack_prefix_derivation g w ps ss ts
    -> step g ps ss ts av u = StepK ps' ss' ts' av' u'
    -> stack_prefix_derivation g w ps' ss' ts'.
Proof.
  intros g w (pfr, pfrs) (pfr', pfrs') (sfr, sfrs) (sfr', sfrs')
         ts ts' av av' u u' hf hs; red; red in hf.
  destruct hf as (wpre & heq & hf); subst.
  unfold step in hs; dmeqs h; tc; inv hs.
  - eexists; split; eauto.
    eapply return_preserves_frames_derivation; eauto.
  - eexists; split.
    + rewrite cons_app_singleton; rewrite app_assoc; eauto.
    + eapply consume_preserves_frames_derivation; eauto.
  - eexists; split; eauto.
    eapply push_preserves_frames_derivation; eauto.
    eapply llPredict_succ_in_grammar; eauto.
  - eexists; split; eauto.
    eapply push_preserves_frames_derivation; eauto.
    eapply llPredict_ambig_in_grammar; eauto.
Qed.

(* Invariant for proving the "unambiguous" version of the parser soundness
   lemma. The processed stack symbols and the semantic values stored
   in each frame comprise a unique partial derivation for the tokens that
   have been consumed. *)
Inductive unique_frames_derivation (g : grammar) :
  list prefix_frame -> list suffix_frame -> list token -> list token -> Prop :=
| USD_bottom :
    forall pre suf wpre wsuf v,
      gamma_derivation g (rev pre) wpre (rev v)
      -> (forall wpre' wsuf' v',
             wpre' ++ wsuf' = wpre ++ wsuf
             -> gamma_derivation g (rev pre) wpre' (rev v')
             -> gamma_recognize g suf wsuf'
             -> wpre' = wpre /\ wsuf' = wsuf /\ rev v' = rev v)
      -> unique_frames_derivation g [PF pre v] [SF suf] wpre wsuf
| USD_upper :
    forall p_cr p_ce s_cr s_ce p_frs s_frs pre pre' suf suf' x wpre wmid wsuf v v',
      PF pre v            = p_cr
      -> SF (NT x :: suf) = s_cr
      -> PF pre' v'       = p_ce 
      -> SF suf'          = s_ce
      -> unique_frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) 
                                     wpre (wmid ++ wsuf)
      -> In (x, rev pre' ++ suf') g
      -> gamma_derivation g (rev pre') wmid (rev v')
      -> (forall wmid' wsuf' v'',
             wmid' ++ wsuf' = wmid ++ wsuf
             -> gamma_derivation g (rev pre') wmid' (rev v'')
             -> gamma_recognize g (suf' ++ suf ++ unprocTailSyms s_frs) wsuf'
             -> wmid' = wmid /\ wsuf' = wsuf /\ rev v'' = rev v')
      (* Here's the interesting part -- all pushes are unique *)
      -> (forall rhs,
             In (x, rhs) g
             -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms s_frs) (wmid ++ wsuf)
             -> rhs = rev pre' ++ suf')
      -> unique_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
                                     (wpre ++ wmid) wsuf.
 
Hint Constructors unique_frames_derivation.

Ltac inv_ufd hu  ha hg hi hpu hu' :=
  let hp  := fresh "hp"  in
  let hp' := fresh "hp'" in
  let hs  := fresh "hs"  in
  let hs' := fresh "hs'" in
  inversion hu as [ ? ? ? ? ? hg ha 
                  | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? 
                    hp hs hp' hs' hu' hi hg ha hpu
                  ]; subst; clear hu.

(* factor out repetition *)
Lemma return_preserves_unique_frames_derivation :
  forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x wpre wsuf v v',
    p_ce     = PF pre' v'
    -> s_ce  = SF []
    -> p_cr  = PF pre v
    -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> unique_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
                                   wpre wsuf
    -> unique_frames_derivation g (p_cr' :: p_frs) (s_cr' :: s_frs) wpre wsuf.
Proof.
  intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x wpre wsuf v v' 
         ? ? ? ? ? ? hu; subst. 
  inv_ufd hu ha hg hi hpu hu'; inv hp; inv hs; inv hp'; inv hs'; sis; 
    rewrite app_nil_r in *.
  inv_ufd hu' ha' hg' hi' hpu' hu''; sis; try rewrite app_nil_r in *.
  - apply USD_bottom; sis.
    + apply gamma_derivation_app; auto.
      rew_nil_r wmid; eauto.
    + intros wpre' wsuf' v'' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as (w & w' & v''' & v'''' & ? & heq' & hd & hd'); subst.
      repeat rewrite <- app_assoc in heq.
      apply gamma_derivation_singleton_nt in hd'.
      destruct hd' as (ys & sts & hi' & heq'' & hd'); subst.
      eapply ha' with (v' := rev v''') in heq; 
        try rewrite rev_involutive in *; subst; eauto.
      * destruct heq as (? & heq & ?); subst.
        assert (ys = rev pre').
        { rewrite <- heq in hpu; apply hpu in hi'; auto.
          apply gamma_recognize_app; auto.
          eapply gamma_derivation__gamma_recognize; eauto. }
        subst.
        eapply ha with (v'' := rev sts) in heq; 
          try rewrite rev_involutive in *; eauto.
        destruct heq as (? & ? & ?); subst; auto.
      * repeat (econstructor; eauto).
        eapply gamma_derivation__gamma_recognize; eauto.
  - inv hp'; inv hs'. 
    rewrite <- app_assoc; eapply USD_upper; eauto; sis; apps.
    + apply gamma_derivation_app; auto.
      rew_nil_r wmid; eauto.
    + intros wpre' wsuf' v'' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as (w & w' & v''' & v'''' & ? & ? & hd & hd'); subst.
      apply gamma_derivation_singleton_nt in hd'.
      destruct hd' as (ys & sts & hi'' & heq'' & hd'); subst.
      repeat rewrite <- app_assoc in heq.
      eapply ha' with (v'' := rev v''') in heq; 
        try rewrite rev_involutive in *; subst; eauto.
      * destruct heq as (? & heq & ?); subst.
        assert (ys = rev pre').
        { rewrite <- heq in hpu; apply hpu in hi''; auto.
          apply gamma_recognize_app; auto.
          eapply gamma_derivation__gamma_recognize; eauto. }
        subst; eapply ha with (v'' := rev sts) in heq; 
          try rewrite rev_involutive in *; eauto.
        destruct heq as (? & ? & ?); subst; auto.
      * repeat (econstructor; eauto).
        eapply gamma_derivation__gamma_recognize; eauto.
Qed.

(* factor out repetition *)
Lemma consume_preserves_unique_frames_derivation :
  forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf a l wpre wsuf v,
    p_fr     = PF pre v
    -> s_fr  = SF (T a :: suf)
    -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
    -> s_fr' = SF suf
    -> unique_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                                   wpre ((a, l) :: wsuf)
    -> unique_frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs) 
                                  (wpre ++ [(a, l)]) wsuf.
Proof.
  intros g ? ? ? ? p_frs s_frs pre suf a l wpre wsuf v ? ? ? ? hu; subst.
  inv_ufd hu ha hg hi hpu hu'.
  - constructor.
    + apply gamma_derivation_app; auto.
      rew_nil_r [(a, l)]; eauto.
    + intros wpre' wsuf' v' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v'' [v''' [? [heq' [hd hd']]]]]]]; subst.
      apply gamma_derivation_singleton_t in hd'. 
      destruct hd' as (l' & ? & ?); subst.
      repeat rewrite <- app_assoc in heq.
      eapply ha with (v' := rev v'') in heq; 
        try rewrite rev_involutive in *; eauto.
      destruct heq as [? [heq'' ?]]; subst.
      inv heq''; auto. 
  - inv hp'; inv hs'; rewrite <- app_assoc; econstructor; eauto; sis; apps.
    + apply gamma_derivation_app; auto.
      rew_nil_r [(a, l)]; eauto.
    + intros wpre' wsuf' v' heq hd hr; subst; sis.
      apply gamma_derivation_split in hd.
      destruct hd as [w [w' [v'' [v''' [? [heq' [hd hd']]]]]]]; subst.
      apply gamma_derivation_singleton_t in hd'. 
      destruct hd' as (l' & ? & ?); subst.
      repeat rewrite <- app_assoc in heq.
      eapply ha with (v'' := rev v'') in heq; 
        try rewrite rev_involutive in *; eauto.
      destruct heq as [? [heq'' ?]]; subst.
      inv heq''; auto. 
Qed.

Lemma push_succ_preserves_unique_frames_derivation :
  forall g p_cr p_ce s_cr s_ce p_frs s_frs x pre suf rhs wpre wsuf v,
    p_cr    = PF pre v
    -> s_cr = SF (NT x :: suf)
    -> p_ce = PF [] []
    -> s_ce = SF rhs
    -> no_left_recursion g
    -> stacks_wf g (p_cr, p_frs) (s_cr, s_frs)
    -> llPredict g x (s_cr, s_frs) wsuf = PredSucc rhs
    -> unique_frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) wpre wsuf
    -> unique_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) wpre wsuf.
Proof.
  intros g ? ? ? ? p_frs s_frs x pre suf rhs wpre wsuf v ? ? ? ? hn hw hl hu; subst.
  assert (heq: wpre = wpre ++ []) by apps; rewrite heq.
  econstructor; eauto; sis.
  - eapply llPredict_succ_in_grammar; eauto.
  - intros wmid' wsuf' v'' heq' hd hr; sis; subst.
    inv hd; auto.
  - intros; eapply llPredict_succ_at_most_one_rhs_applies in hl; eauto.
    red. eapply frames_wf__suffix_frames_wf; eauto.
Qed.

Definition unique_stack_prefix_derivation g w p_stk s_stk wsuf u :=
  match p_stk, s_stk with
  | (p_fr, p_frs), (s_fr, s_frs) =>
    u = true
    -> exists wpre,
        w = wpre ++ wsuf
        /\ unique_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) wpre wsuf
  end.

Lemma step_preserves_unique_stack_prefix_derivation_invar :
  forall g w p_stk p_stk' s_stk s_stk' ts ts' av av' u u',
    no_left_recursion g
    -> stacks_wf g p_stk s_stk
    -> unique_stack_prefix_derivation g w p_stk s_stk ts u
    -> step g p_stk s_stk ts av u = StepK p_stk' s_stk' ts' av' u'
    -> unique_stack_prefix_derivation g w p_stk' s_stk' ts' u'.
Proof.
  intros g w (p_fr, p_frs) (p_fr', p_frs') (s_fr, s_frs) (s_fr', s_frs') 
         ts ts' av av' u u' hn hw hu hs; red; red in hu; intros hu'.
  unfold step in hs; dmeqs h; inv hs; tc;
    destruct hu as (wpre & heq & hu); subst; auto. 
  - exists wpre; split; auto.
    eapply return_preserves_unique_frames_derivation; eauto.
  - eexists; split.
    + rewrite cons_app_singleton; rewrite app_assoc; eauto.
    + eapply consume_preserves_unique_frames_derivation; eauto.
  - exists wpre; split; auto.
    eapply push_succ_preserves_unique_frames_derivation; eauto.
Qed.

Lemma unique_stack_prefix_derivation_invar_starts_true :
  forall g ys ts,
    unique_stack_prefix_derivation g ts (PF [] [], []) (SF ys, []) ts true. 
Proof.
  intros g ys ts; red; intros _.
  exists []; split; auto.
  constructor; auto.
  intros wpre' wsuf' v' heq hd hr; sis.
  inv hd; auto.
Qed.

Lemma multistep_sound_unambig' :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (p_stk  : prefix_stack)
         (s_stk  : suffix_stack)
         (u      : bool)
         (a'     : Acc lex_nat_triple (meas g s_stk wsuf av))
         (v      : forest),
    tri = meas g s_stk wsuf av
    -> no_left_recursion g
    -> stacks_wf g p_stk s_stk
    -> unique_stack_prefix_derivation g w p_stk s_stk wsuf u
    -> multistep g p_stk s_stk wsuf av u a' = Accept v
    -> gamma_derivation g (bottomFrameSyms p_stk s_stk) w v
       /\ (forall v',
              gamma_derivation g (bottomFrameSyms p_stk s_stk) w v'
              -> v' = v).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros w wsuf av p_stk s_stk u a' v ? hn hw hu hm; subst.
  apply multistep_accept_cases in hm.
  destruct hm as [[hf hu'] | he]; subst.
  - apply step_StepAccept_facts in hf.
    destruct hf as (? & ? & (pre & ?)); subst.
    unfold bottomFrameSyms; simpl; rewrite app_nil_r.
    red in hu.
    destruct hu as (wpre & ? & hu); subst; auto.
    inv_ufd hu ha hg hi hpu hu'; try rewrite rev_involutive in hg; 
      rewrite app_nil_r in *; split; auto.
    intros v' hd.
    assert (heq : v' = rev (rev v')) by (rewrite rev_involutive; auto).
    rewrite heq in hd. 
    eapply ha in hd; eauto; apps.
    destruct hd as (? & ? & heq'); repeat rewrite rev_involutive in heq'; auto.
  - destruct he as (ps' & ss' & ts' & av' & u' & a'' & hs & hm).
    eapply IH with (w := w) in hm; eauto.
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + eapply step_meas_lt; eauto.
    + eapply step_preserves_stacks_wf_invar; eauto. 
    + eapply step_preserves_unique_stack_prefix_derivation_invar; eauto.
Qed.

Lemma multistep_sound_unambig :
  forall (g      : grammar)
         (w wsuf : list token)
         (av     : NtSet.t)
         (p_stk  : prefix_stack)
         (s_stk  : suffix_stack)
         (u      : bool)
         (a      : Acc lex_nat_triple (meas g s_stk wsuf av))
         (v      : forest),
    no_left_recursion g
    -> stacks_wf g p_stk s_stk
    -> unique_stack_prefix_derivation g w p_stk s_stk wsuf u
    -> multistep g p_stk s_stk wsuf av u a = Accept v
    -> gamma_derivation g (bottomFrameSyms p_stk s_stk) w v
       /\ (forall v',
              gamma_derivation g (bottomFrameSyms p_stk s_stk) w v'
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
  eapply multistep_sound_unambig in hp; try red; eauto.
  apply unique_stack_prefix_derivation_invar_starts_true.
Qed.

(* now for the ambiguous case *)

(* Invariant for proving the "ambiguous" version of the parser soundness
   theorem. The processed stack symbols and semantic values constructed
   for them comprise a correct partial derivation for the tokens consumed,
   and there exists a different semantic value for a (possibly different)
   prefix of the complete token sequence. *)
Inductive ambiguous_frames_derivation (g : grammar) :
  list prefix_frame -> list suffix_frame -> list token -> list token -> Prop :=
| AFD_push :
    forall p_cr p_ce s_cr s_ce p_frs s_frs pre pre' suf suf' x alt_rhs wpre wmid wsuf v v',
    PF pre v            = p_cr
    -> SF (NT x :: suf) = s_cr
    -> PF pre' v'       = p_ce
    ->  SF suf'         = s_ce
    -> frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) wpre (wmid ++ wsuf)
    -> In (x, rev pre' ++ suf') g
    -> gamma_derivation g (rev pre') wmid (rev v')
    -> In (x, alt_rhs) g
    -> rev pre' ++ suf' <> alt_rhs
    -> gamma_recognize g (alt_rhs ++ suf ++ unprocTailSyms s_frs) (wmid ++ wsuf)
    -> ambiguous_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
                                     (wpre ++ wmid) wsuf
| AFD_sem :
    forall p_fr s_fr p_frs s_frs pre suf wpre wmid wmid' wsuf wsuf' v v',
      PF pre v  = p_fr
      -> SF suf = s_fr
      -> frames_derivation g p_frs s_frs wpre (wmid ++ wsuf)
      -> gamma_derivation g (rev pre) wmid (rev v)
      -> gamma_derivation g (rev pre) wmid' (rev v')
      -> gamma_recognize g (suf ++ unprocTailSyms s_frs) wsuf'
      -> wmid' ++ wsuf' = wmid ++ wsuf
      -> rev v' <> rev v
      -> ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs)
                                       (wpre ++ wmid) wsuf
| AFD_tail :
    forall p_fr s_fr p_frs s_frs pre suf wpre wmid wsuf v,
      PF pre v  = p_fr
      -> SF suf = s_fr
      -> ambiguous_frames_derivation g p_frs s_frs wpre (wmid ++ wsuf)
      -> gamma_derivation g (rev pre) wmid (rev v)
      -> ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs)
                                       (wpre ++ wmid) wsuf.

Hint Constructors ambiguous_frames_derivation.

Ltac inv_afd ha  ha' heq hf hg hg' hi hi' hneq hr :=
  let hp  := fresh "hp"  in
  let hs  := fresh "hs"  in
  let hp' := fresh "hp'" in
  let hs' := fresh "hs'" in
  inversion ha as
      [ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? hp hs hp' hs' hf hi hg hi' hneq hr
      | ? ? ? ? ? ? ? ? ? ? ? ? ? hp hs hf hg hd' hr heq hneq
      | ? ? ? ? ? ? ? ? ? ? hp hs ha' hg]; subst; clear ha.

Lemma return_preserves_ambiguous_frames_derivation :
  forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x wpre wsuf v v',
    p_ce     = PF pre' v'
    -> s_ce  = SF []
    -> p_cr  = PF pre v
    -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
    -> ambiguous_frames_derivation
         g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) wpre wsuf
    -> ambiguous_frames_derivation
         g (p_cr' :: p_frs) (s_cr' :: s_frs) wpre wsuf.
Proof.
  intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x wpre wsuf v v' 
         ? ? ? ? ? ? hw ha; subst.
  inv_afd ha  ha' heq hf hg hg' hi hi' hneq hr; inv hp; inv hs; sis.
  - (* ambig push case *)
    inv hp'; inv hs'; rew_anr.
    eapply fd_inv_cons in hf; eauto.
    destruct hf as (wp & wp' & heq & hf & hg'); subst.
    apply gamma_recognize_split in hr.
    destruct hr as (w & w' & heq & hr & hr'); subst.
    apply gamma_recognize__exists_gamma_derivation in hr.
    destruct hr as (v_alt & hr).
    rewrite <- app_assoc.
    eapply AFD_sem with (v     := Node x (rev v') :: v)
                        (v'    := Node x v_alt :: v)
                        (wmid' := wp' ++ w); eauto; sis; apps.
    + apply gamma_derivation_app; auto.
      rew_nil_r wmid; eauto.
    + apply gamma_derivation_app; eauto.
      rew_nil_r w; eauto.
    + repeat rewrite <- app_assoc in *.
      rewrite heq; auto.
    + unfold not; intros heq'.
      apply app_inj_tail in heq'; destruct heq' as [_ hh]; inv hh.
      eapply trees_eq__gammas_eq_words_eq with
          (ys := rev pre') in hr; eauto; firstorder.
  - (* sem case *)
    eapply fd_inv_cons in hf; eauto.
    destruct hf as (wp & wp' & heq' & hf' & hg'); subst.
    rewrite <- app_assoc.
    eapply AFD_sem with (wmid' := wp' ++ wmid')
                        (v     := Node x (rev v') :: v)
                        (v'    := Node x (rev v'0) :: v); eauto; sis; apps.
    + apply gamma_derivation_app; auto.
      inv hw; rew_anr.
      rew_nil_r wmid; eauto.
    + apply gamma_derivation_app; auto.
      inv hw; rew_anr; rew_nil_r wmid'; eauto.
    + repeat rewrite <- app_assoc.
      rewrite heq; auto.
    + unfold not; intros heq'.
      apply app_inj_tail in heq'; destruct heq' as [_ hh]; inv hh; tc.
  - (* tail case *)
    inv_afd ha' ha'' heq hf hg' hg'' hi hi' hneq hr; sis. 
    + (* caller push case *)
      inv hp'; inv hs'.
      rewrite <- app_assoc; eapply AFD_push; eauto; sis; apps.
      apply gamma_derivation_app; auto.
      inv hw; rew_anr; rew_nil_r wmid; eauto.
    + (* caller sem case *)
      inv hp; inv hs.
      inv_gr hr wmid'' wsuf'' hs hr'.
      inv_sr hs hi hg''.
      apply gamma_recognize__exists_gamma_derivation in hg''.
      destruct hg'' as [vy hvy].
      rewrite <- app_assoc.
      eapply AFD_sem with (wmid' := wmid' ++ wmid'')
                          (v'    := Node x vy :: _); eauto; sis.
      * apps.
      * apply gamma_derivation_app; auto.
        inv hw; rew_anr. 
        rew_nil_r wmid; eauto.
      * apply gamma_derivation_app; eauto.
        rew_nil_r wmid''; eauto.
      * apps.
      * unfold not; intros heq'; sis.
        apply app_inj_tail in heq'; firstorder.
    + inv hp; inv hs.
      rewrite <- app_assoc.
      eapply AFD_tail; eauto.
      * rewrite <- app_assoc; auto.
      * apply gamma_derivation_app; auto.
        inv hw; rew_anr; rew_nil_r wmid; eauto.
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

Definition ambiguous_prefix_derivation g w st :=
  match st with
  | Pst _ (fr, frs) wsuf u =>
    u = false
    -> exists wpre,
        w = wpre ++ wsuf
        /\ ambiguous_frames_derivation g (fr :: frs) wpre wsuf
  end.

Lemma apd_starts_true :
  forall g ys ts,
    ambiguous_prefix_derivation g ts (mkInitState g ys ts).
Proof.
  intros g ys ts.
  unfold mkInitState; simpl.
  intros hc; inv hc.
Qed.

Lemma step_preserves_apd :
  forall g w st st',
    no_left_recursion g
    -> stack_wf g (Parser.stack st)
    -> frames_prefix_derivation g w st
    -> ambiguous_prefix_derivation g w st
    -> step g st = StepK st'
    -> ambiguous_prefix_derivation g w st'.
Proof.
  intros g w [av (fr,frs) wsuf u] [av' (fr',frs') wsuf' u'] hn hw hd ha hs.
  red; red in ha.
  intros hu.
  unfold step in hs; dmeqs h; inv hs; tc.
  - (* return *)
    destruct ha as [wpre [heq ha]]; subst; sis; auto.
    exists wpre; eapply return_preserves_ambiguous_frames_derivation in ha; eauto.
  - (* consume *)
    destruct ha as [wpre [heq ha]]; subst; sis; auto.
    exists (wpre ++ [(t,l1)]); split; auto.
    + apps.
    + eapply consume_preserves_ambiguous_frames_derivation; eauto.
  - (* unambiguous push *)
    destruct ha as [wpre [heq ha]]; subst; sis; auto.
    eexists; split; eauto.
    rew_nil_r wpre.
    eapply AFD_tail; eauto.
  - (* ambiguous push *)
    destruct u.
    + (* u is true -- stack derivation is unique up to this point *)
      red in hd.
      destruct hd as [wpre [heq hd]]; subst.
      exists wpre; split; auto.
      clear ha.
      rew_nil_r wpre.
      eapply llPredict_ambig_rhs_unproc_stack_syms' in h4; eauto.
      destruct h4 as [hr [rhs' [hi [hneq hr']]]].
      eapply AFD_push; eauto.
      simpl; auto.
    + destruct ha as [wpre [heq ha]]; subst; sis; auto.
      eexists; split; eauto.
      rew_nil_r wpre.
      eapply AFD_tail; eauto.
Qed.

Lemma multistep_sound_ambig' :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (u      : bool)
         (a'     : Acc lex_nat_triple (Parser.meas g (Pst av stk wsuf u)))
         (v      : forest),
    tri = Parser.meas g (Pst av stk wsuf u)
    -> no_left_recursion g
    -> stack_wf g stk
    -> frames_prefix_derivation g w (Pst av stk wsuf u)
    -> ambiguous_prefix_derivation g w (Pst av stk wsuf u)
    -> multistep g (Pst av stk wsuf u) a' = Ambig v
    -> gamma_derivation g (bottomFrameSyms stk) w v
       /\ (exists v',
              gamma_derivation g (bottomFrameSyms stk) w v'
              /\ v' <> v).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros w wsuf av stk u a' v heq hn hw hf hi hm; subst.
  apply multistep_ambig_cases in hm.
  destruct hm as [[hs hu] | he].
  - simpl in hu; subst.
    apply step_StepAccept_facts in hs.
    destruct hs as [[xo [rpre [v' [heq]]]] heq']; subst.
    unfold bottomFrameSyms; simpl; rewrite app_nil_r.
    red in hi.
    destruct hi as [wpre [heq ha]]; subst; auto.
    clear IH. clear a'. clear hlt.
    inv ha.
    + inv H1; sis. unfold unprocTailSyms' in *; sis.
      rewrite app_nil_r in *; subst.
      inv H2; sis.
      inv H5; sis.
      rewrite app_nil_r in *. 
      firstorder.
    + inv H2.
  - destruct he as [st' [a'' [hf' hm]]].
    destruct st' as [av' stk' wsuf'].
    eapply IH with (w := w) in hm; eauto. 
    + erewrite step_preserves_bottomFrameSyms_invar; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_frames_prefix_derivation; eauto.
      simpl; auto.
    + eapply step_preserves_apd; eauto.
      simpl; auto.
Qed.

Lemma multistep_sound_ambig :
  forall (g      : grammar)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (u      : bool)
         (a      : Acc lex_nat_triple (Parser.meas g (Pst av stk wsuf u)))
         (v      : forest),
    no_left_recursion g
    -> stack_wf g stk
    -> frames_prefix_derivation g w (Pst av stk wsuf u)
    -> ambiguous_prefix_derivation g w (Pst av stk wsuf u)
    -> multistep g (Pst av stk wsuf u) a = Ambig v
    -> gamma_derivation g (bottomFrameSyms stk) w v
       /\ (exists v',
              gamma_derivation g (bottomFrameSyms stk) w v'
              /\ v' <> v).
Proof.
  intros; eapply multistep_sound_ambig'; eauto.
Qed.

Theorem parse_sound_ambig :
  forall (g  : grammar)
         (ys : list symbol)
         (ts : list token)
         (v  : forest),
    no_left_recursion g
    -> parse g ys ts = Ambig v
    -> gamma_derivation g ys ts v
       /\ (exists v',
              gamma_derivation g ys ts v'
              /\ v' <> v).
Proof.
  intros g ys ts v hn hp.
  unfold parse in hp.
  eapply multistep_sound_ambig in hp; eauto.
  - constructor.
  - (* lemma *)
    exists []; split; eauto.
    rew_nil_r ([] : list token); eauto.
  - apply apd_starts_true.
Qed.