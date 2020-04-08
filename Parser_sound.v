Require Import Arith Bool List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
(*Require Import GallStar.Prediction.
Require Import GallStar.Prediction_error_free.
Require Import GallStar.Prediction_complete. *)
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.

Module ParserSoundFn (Import D : Defs.T).

  Module Export P := ParserFn D.

  Inductive frames_wf (g : grammar) : list prefix_frame -> list suffix_frame -> Prop :=
  | WF_bottom :
      forall pre suf v,
        frames_wf g [PF pre v] [SF None suf]
  | WF_upper :
      forall x o pre pre' suf suf' p_frs s_frs v v',
        In (x, rev pre' ++ suf') g
        -> frames_wf g (PF pre v :: p_frs) 
                     (SF o (NT x :: suf) :: s_frs)
        -> frames_wf g (PF pre' v' :: PF pre v :: p_frs) 
                     (SF (Some x) suf' :: SF o (NT x :: suf) :: s_frs).

  Hint Constructors frames_wf : core.

  Ltac inv_fw hw  hi hw' := 
    inversion hw as [? ? ? | ? ? ? ? ? ? ? ? ? ? hi hw']; subst; clear hw.

  Lemma frames_wf__suffix_frames_wf :
    forall g p_frs s_frs,
      frames_wf g p_frs s_frs
      -> suffix_frames_wf g s_frs.
  Proof.
    intros g pfrs sfrs hw; induction hw; eauto.
  Qed.

  Lemma return_preserves_frames_wf_invar :
    forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x o o' v v',
      p_ce     = PF pre' v'
      -> s_ce  = SF o' []
      -> p_cr  = PF pre v
      -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
      -> frames_wf g (p_cr' :: p_frs) (s_cr' :: s_frs).
  Proof.
    intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x o o' v v'
           ? ? ? ? ? ? hw; subst; inv_fw hw hi hw'; rew_anr.
    inv_fw hw' hi' hw''; auto.
    econstructor; eauto; sis; apps.
  Qed.

  Lemma consume_preserves_frames_wf_invar :
    forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf o a l v,
      p_fr     = PF pre v
      -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
      -> s_fr  = SF o (T a :: suf)
      -> s_fr' = SF o suf
      -> frames_wf g (p_fr :: p_frs) (s_fr :: s_frs) 
      -> frames_wf g (p_fr' :: p_frs) (s_fr' :: s_frs).
  Proof.
    intros g ? ? ? ? p_frs s_frs pre suf o a l v ? ? ? ? hw; subst; 
      inv_fw hw hi hw'; auto.
    econstructor; eauto; sis; apps.
  Qed.

  Lemma push_preserves_frames_wf_invar :
    forall g p_cr p_ce s_cr s_ce p_frs s_frs o x rhs pre suf v,
      p_cr     = PF pre v
      -> p_ce  = PF [] []
      -> s_cr  = SF o (NT x :: suf)
      -> s_ce  = SF (Some x) rhs
      -> In (x, rhs) g
      -> frames_wf g (p_cr :: p_frs) (s_cr :: s_frs) 
      -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs).
  Proof.
    intros g ? ? ? ? p_frs s_frs o x rhs pre suf v ? ? ? ? hi hf; subst; auto.
  Qed.    

  Definition stacks_wf g p_stk s_stk := 
    match p_stk, s_stk with
    | (p_fr, p_frs), (s_fr, s_frs) => frames_wf g (p_fr :: p_frs) (s_fr :: s_frs)
    end.

  Lemma step_preserves_stacks_wf_invar :
    forall g cm ps ps' ss ss' ts ts' av av' un un' ca ca',
      stacks_wf g ps ss
      -> cache_stores_target_results g cm ca
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> stacks_wf g ps' ss'.
  Proof.
    intros g cm (pfr, pfrs) (pfr', pfrs') (sfr, sfrs) (sfr', sfrs')
           ts ts' av av' un un' ca ca' hw hc hs; red; red in hw.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eapply return_preserves_frames_wf_invar; eauto. 
    - eapply consume_preserves_frames_wf_invar; eauto. 
    - eapply push_preserves_frames_wf_invar; eauto.
      eapply adaptivePredict_succ_in_grammar; eauto.
    - eapply push_preserves_frames_wf_invar; eauto.
      eapply adaptivePredict_ambig_in_grammar; eauto.
  Qed.

  Lemma stacks_wf__suffix_stack_wf :
    forall g p_stk s_stk,
      stacks_wf g p_stk s_stk
      -> suffix_stack_wf g s_stk. 
  Proof.
    intros g (pfr, pfrs) (sfr, sfrs) hw.
    eapply frames_wf__suffix_frames_wf; eauto.
  Qed.

  Lemma step_preserves_bottomFrameSyms_invar :
    forall g cm p_stk p_stk' s_stk s_stk' ts ts' av av' un un' ca ca',
      stacks_wf g p_stk s_stk
      -> step g cm p_stk s_stk ts av un ca = StepK p_stk' s_stk' ts' av' un' ca'
      -> bottomFrameSyms p_stk s_stk = bottomFrameSyms p_stk' s_stk'.
  Proof.
    intros g cm (p_fr, p_frs) p_stk' (s_fr, s_frs) s_stk' ts ts' av av' un un' ca ca' hw hs.
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
        -> frames_derivation g [PF pre v] [SF None suf] wpre wsuf
  | FD_upper :
      forall p_cr p_frs s_cr s_frs o x pre' suf suf' v' wpre wmid wsuf,
        SF o (NT x :: suf) = s_cr
        -> In (x, rev pre' ++ suf') g
        -> gamma_derivation g (rev pre') wmid (rev v')
        -> frames_derivation g (p_cr :: p_frs)
                               (s_cr :: s_frs)
                               wpre (wmid ++ wsuf)
        -> frames_derivation g (PF pre' v'       :: p_cr :: p_frs)
                               (SF (Some x) suf' :: s_cr :: s_frs)
                               (wpre ++ wmid) wsuf.

  Hint Constructors frames_derivation : core.

  Ltac inv_fd hf hf':=
    let heq := fresh "heq" in
    let hi  := fresh "hi"  in
    let hg  := fresh "hg"  in
    inversion hf as [ ?
                    | ? ? ? ? ? hg 
                    | ? ? ? ? ? ? ? ? ? ? ? ? ? heq hi hg hf']; subst; clear hf.

  Lemma fd_inv_cons :
    forall g p_fr s_fr p_frs s_frs o pre suf w wsuf v,
      p_fr    = PF pre v
      -> s_fr = SF o suf
      -> frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) w wsuf
      -> exists wpre wmid,
          w = wpre ++ wmid
          /\ gamma_derivation g (rev pre) wmid (rev v)
          /\ frames_derivation g p_frs s_frs wpre (wmid ++ wsuf).
  Proof.
    intros g ? ? p_frs s_frs o pre suf w wsuf v ? ? hf; subst; inv hf; eauto.
    exists []; eexists; repeat split; eauto.
  Qed.

  Lemma return_preserves_frames_derivation :
    forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf o o' x v v' wpre wsuf,
      p_ce     = PF pre' v'
      -> s_ce  = SF o' []
      -> p_cr  = PF pre v
      -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> frames_derivation g (p_ce :: p_cr :: p_frs)
                             (s_ce :: s_cr :: s_frs)
                             wpre wsuf
      -> frames_derivation g (p_cr' :: p_frs)
                             (s_cr' :: s_frs)
                             wpre wsuf.
  Proof.
    intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf o o' x v v' wpre wsuf
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
    forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf o a l v wpre wsuf,
      p_fr     = PF pre v
      -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
      -> s_fr  = SF o (T a :: suf)
      -> s_fr' = SF o suf
      -> frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                           wpre ((a, l) :: wsuf)
      -> frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs) 
                           (wpre ++ [(a, l)]) wsuf.
  Proof.
    intros g ? ? ? ? p_frs s_frs pre suf o a l v wpre wsuf
           ? ? ? ? hf; subst; inv hf.
    - constructor; sis.
      apply gamma_derivation_app; auto.
      rew_nil_r [(a, l)]; auto.
    - rewrite <- app_assoc; econstructor; eauto; sis; apps.
      apply gamma_derivation_app; auto.
      rew_nil_r [(a, l)]; auto.
  Qed.

  Lemma push_preserves_frames_derivation :
    forall g p_cr p_ce s_cr s_ce p_frs s_frs o x rhs pre suf wpre wsuf v,
      p_cr     = PF pre v
      -> p_ce  = PF [] []
      -> s_cr  = SF o (NT x :: suf)
      -> s_ce  = SF (Some x) rhs
      -> In (x, rhs) g
      -> frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) 
                           wpre wsuf
      -> frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) 
                           wpre wsuf.
  Proof.
    intros g ? ? ? ? p_frs s_frs o x rhs pre suf wpre wsuf v ? ? ? ? hi hf; subst.
    rew_nil_r wpre; eauto.
  Qed.    

  Definition stack_prefix_derivation g w p_stk s_stk wsuf :=
    match p_stk, s_stk with
    | (p_fr, p_frs), (s_fr, s_frs) =>
      exists wpre,
      w = wpre ++ wsuf
      /\ frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) wpre wsuf
    end.

  Lemma step_preserves_stack_prefix_derivation_invar :
    forall g cm w ps ps' ss ss' ts ts' av av' un un' ca ca',
      cache_stores_target_results g cm ca
      -> stack_prefix_derivation g w ps ss ts
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> stack_prefix_derivation g w ps' ss' ts'.
  Proof.
    intros g cm w (pfr, pfrs) (pfr', pfrs') (sfr, sfrs) (sfr', sfrs')
           ts ts' av av' un un' ca ca' hc hf hs; red; red in hf.
    destruct hf as (wpre & heq & hf); subst.
    unfold step in hs; dmeqs h; tc; inv hs.
    - eexists; split; eauto.
      eapply return_preserves_frames_derivation; eauto.
    - eexists; split.
      + rewrite cons_app_singleton; rewrite app_assoc; eauto.
      + eapply consume_preserves_frames_derivation; eauto.
    - eexists; split; eauto.
      eapply push_preserves_frames_derivation; eauto.
      eapply adaptivePredict_succ_in_grammar; eauto.
    - eexists; split; eauto.
      eapply push_preserves_frames_derivation; eauto.
      eapply adaptivePredict_ambig_in_grammar; eauto.
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
        -> unique_frames_derivation g [PF pre v] [SF None suf] wpre wsuf
  | USD_upper :
      forall p_cr p_ce s_cr s_ce p_frs s_frs pre pre' suf suf' o x wpre wmid wsuf v v',
        PF pre v              = p_cr
        -> SF o (NT x :: suf) = s_cr
        -> PF pre' v'         = p_ce 
        -> SF (Some x) suf'   = s_ce
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
  
  Hint Constructors unique_frames_derivation : core.

  Ltac inv_ufd hu  ha hg hi hpu hu' :=
    let hp  := fresh "hp"  in
    let hp' := fresh "hp'" in
    let hs  := fresh "hs"  in
    let hs' := fresh "hs'" in
    inversion hu as [ ? ? ? ? ? hg ha 
                    | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?  
                      hp hs hp' hs' hu' hi hg ha hpu
                    ]; subst; clear hu.

  (* factor out repetition *)
  Lemma return_preserves_unique_frames_derivation :
    forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf o o' x wpre wsuf v v',
      p_ce     = PF pre' v'
      -> s_ce  = SF o' []
      -> p_cr  = PF pre v
      -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> unique_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
                                  wpre wsuf
      -> unique_frames_derivation g (p_cr' :: p_frs) (s_cr' :: s_frs) wpre wsuf.
  Proof.
    intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf o o' x wpre wsuf v v' 
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
    forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf o a l wpre wsuf v,
      p_fr     = PF pre v
      -> s_fr  = SF o (T a :: suf)
      -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
      -> s_fr' = SF o suf
      -> unique_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                                  wpre ((a, l) :: wsuf)
      -> unique_frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs) 
                                  (wpre ++ [(a, l)]) wsuf.
  Proof.
    intros g ? ? ? ? p_frs s_frs pre suf o a l wpre wsuf v ? ? ? ? hu; subst.
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
    forall g cm p_cr p_ce s_cr s_ce p_frs s_frs o x pre suf rhs wpre wsuf ca ca' v,
      p_cr    = PF pre v
      -> s_cr = SF o (NT x :: suf)
      -> p_ce = PF [] []
      -> s_ce = SF (Some x) rhs
      -> no_left_recursion g
      -> stacks_wf g (p_cr, p_frs) (s_cr, s_frs)
      -> cache_stores_target_results g cm ca
      -> adaptivePredict g cm x (s_cr, s_frs) wsuf ca = (PredSucc rhs, ca')
      -> unique_frames_derivation g (p_cr :: p_frs)
                                    (s_cr :: s_frs) wpre wsuf
      -> unique_frames_derivation g (p_ce :: p_cr :: p_frs)
                                    (s_ce :: s_cr :: s_frs) wpre wsuf.
  Proof.
    intros g cm ? ? ? ? p_frs s_frs o x pre suf rhs wpre wsuf ca ca' v ? ? ? ?
           hn hw hc hp hu; subst.
    assert (heq: wpre = wpre ++ []) by apps; rewrite heq.
    econstructor; eauto; sis.
    - eapply adaptivePredict_succ_in_grammar; eauto. 
    - intros wmid' wsuf' v'' heq' hd hr; sis; subst; inv hd; auto.
    - intros rhs' hi hr'.
      eapply adaptivePredict_succ_at_most_one_rhs_applies in hp; eauto.
      eapply frames_wf__suffix_frames_wf; eauto.
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
    forall g cm w p_stk p_stk' s_stk s_stk' ts ts' av av' un un' ca ca',
      no_left_recursion g
      -> stacks_wf g p_stk s_stk
      -> cache_stores_target_results g cm ca
      -> unique_stack_prefix_derivation g w p_stk s_stk ts un
      -> step g cm p_stk s_stk ts av un ca = StepK p_stk' s_stk' ts' av' un' ca'
      -> unique_stack_prefix_derivation g w p_stk' s_stk' ts' un'.
  Proof.
    intros g cm w (p_fr, p_frs) (p_fr', p_frs') (s_fr, s_frs) (s_fr', s_frs') 
           ts ts' av av' un un' ca ca' hn hw hc hu hs; red; red in hu; intros hu'.
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
      unique_stack_prefix_derivation g ts (PF [] [], []) (SF None ys, []) ts true. 
  Proof.
    intros g ys ts; red; intros _.
    exists []; split; auto.
    constructor; auto.
    intros wpre' wsuf' v' heq hd hr; sis.
    inv hd; auto.
  Qed.

  Lemma multistep_sound_unambig' :
    forall (g      : grammar)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (w wsuf : list token)
           (av     : NtSet.t)
           (p_stk  : prefix_stack)
           (s_stk  : suffix_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a'     : Acc lex_nat_triple (meas g s_stk wsuf av))
           (v      : forest),
      tri = meas g s_stk wsuf av
      -> no_left_recursion g
      -> stacks_wf g p_stk s_stk
      -> unique_stack_prefix_derivation g w p_stk s_stk wsuf un
      -> multistep g cm p_stk s_stk wsuf av un ca hc a' = Accept v
      -> gamma_derivation g (bottomFrameSyms p_stk s_stk) w v
         /\ (forall v',
                gamma_derivation g (bottomFrameSyms p_stk s_stk) w v'
                -> v' = v).
  Proof.
    intros g cm tri a.
    induction a as [tri hlt IH].
    intros w wsuf av p_stk s_stk un ca hc a' v ? hn hw hu hm; subst.
    apply multistep_accept_cases in hm.
    destruct hm as [[hf hu'] | he]; subst.
    - apply step_StepAccept_facts in hf.
      destruct hf as (? & o & ? & (pre & ?)); subst.
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
    - destruct he as (ps' & ss' & ts' & av' & un' & ca' & hc' & a'' & hs & hm).
      eapply IH with (w := w) in hm; eauto.
      + erewrite step_preserves_bottomFrameSyms_invar; eauto.
      + eapply step_meas_lt with (ca := ca); eauto. 
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto. 
      + eapply step_preserves_unique_stack_prefix_derivation_invar with (ca := ca); eauto.
  Qed.

  Lemma multistep_sound_unambig :
    forall (g      : grammar)
           (cm     : closure_map)
           (w wsuf : list token)
           (av     : NtSet.t)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (ha     : Acc lex_nat_triple (meas g ss wsuf av))
           (v      : forest),
      no_left_recursion g
      -> stacks_wf g ps ss
      -> unique_stack_prefix_derivation g w ps ss wsuf un
      -> multistep g cm ps ss wsuf av un ca hc ha = Accept v
      -> gamma_derivation g (bottomFrameSyms ps ss) w v
         /\ (forall v',
                gamma_derivation g (bottomFrameSyms ps ss) w v'
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
      forall p_cr p_ce s_cr s_ce p_frs s_frs pre pre' suf suf' o x alt_rhs wpre wmid wsuf v v',
        PF pre v              = p_cr
        -> SF o (NT x :: suf) = s_cr
        -> PF pre'   v'       = p_ce
        -> SF (Some x) suf'  = s_ce
        -> frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) wpre (wmid ++ wsuf)
        -> In (x, rev pre' ++ suf') g
        -> gamma_derivation g (rev pre') wmid (rev v')
        -> In (x, alt_rhs) g
        -> rev pre' ++ suf' <> alt_rhs
        -> gamma_recognize g (alt_rhs ++ suf ++ unprocTailSyms s_frs) (wmid ++ wsuf)
        -> ambiguous_frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
                                       (wpre ++ wmid) wsuf
  | AFD_sem :
      forall p_fr s_fr p_frs s_frs o pre suf wpre wmid wmid' wsuf wsuf' v v',
        PF pre v    = p_fr
        -> SF o suf = s_fr
        -> frames_derivation g p_frs s_frs wpre (wmid ++ wsuf)
        -> gamma_derivation g (rev pre) wmid (rev v)
        -> gamma_derivation g (rev pre) wmid' (rev v')
        -> gamma_recognize g (suf ++ unprocTailSyms s_frs) wsuf'
        -> wmid' ++ wsuf' = wmid ++ wsuf
        -> rev v' <> rev v
        -> ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs)
                                       (wpre ++ wmid) wsuf
  | AFD_tail :
      forall p_fr s_fr p_frs s_frs o pre suf wpre wmid wsuf v,
        PF pre v    = p_fr
        -> SF o suf = s_fr
        -> ambiguous_frames_derivation g p_frs s_frs wpre (wmid ++ wsuf)
        -> gamma_derivation g (rev pre) wmid (rev v)
        -> ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs)
                                       (wpre ++ wmid) wsuf.

  Hint Constructors ambiguous_frames_derivation : core.

  Ltac inv_afd ha  ha' heq hf hg hg' hi hi' hneq hr :=
    let hp  := fresh "hp"  in
    let hs  := fresh "hs"  in
    let hp' := fresh "hp'" in
    let hs' := fresh "hs'" in
    inversion ha as
        [ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? hp hs hp' hs' hf hi hg hi' hneq hr
        | ? ? ? ? ? ? ? ? ? ? ? ? ? ? hp hs hf hg hd' hr heq hneq
        | ? ? ? ? ? ? ? ? ? ? ? hp hs ha' hg]; subst; clear ha.

  Lemma return_preserves_ambiguous_frames_derivation_invar :
    forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf o o' x wpre wsuf v v',
      p_ce     = PF pre' v'
      -> s_ce  = SF o' []
      -> p_cr  = PF pre v
      -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
      -> s_cr  = SF o (NT x :: suf)
      -> s_cr' = SF o suf
      -> frames_wf g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs)
      -> ambiguous_frames_derivation
           g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) wpre wsuf
      -> ambiguous_frames_derivation
           g (p_cr' :: p_frs) (s_cr' :: s_frs) wpre wsuf.
  Proof.
    intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf o o' x wpre wsuf v v' 
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

  Lemma consume_preserves_ambiguous_frames_derivation_invar :
    forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf o a l v wpre wsuf,
      p_fr     = PF pre v
      -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
      -> s_fr  = SF o (T a :: suf)
      -> s_fr' = SF o suf
      -> ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                                     wpre ((a, l) :: wsuf)
      -> ambiguous_frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs)
                                     (wpre ++ [(a, l)]) wsuf.
  Proof.
    intros g ? ? ? ? p_frs s_frs pre suf o a l v wpre wsuf
           ? ? ? ? ha; subst.
    inv_afd ha ha' heq hf hg hg' hi hi' hneq hr; sis.
    - (* push case *)
      inv hp'; inv hs'; rewrite <- app_assoc.
      eapply AFD_push; eauto; sis; apps.
      apply gamma_derivation_app; auto.
      rew_nil_r ([(a, l)]); eauto.
    - (* sem case *)
      inv hp; inv hs.
      inv_gr hr wmid'' wsuf'' hs hr'.
      inversion hs as [a' l' |]; subst; clear hs.
      rewrite <- app_assoc.
      eapply AFD_sem with
          (wmid' := wmid' ++ [(a, l')])
          (v'    := Leaf a l' :: v'); eauto; sis; apps.
      + apply gamma_derivation_app; auto.
        rew_nil_r ([(a, l)]); eauto.
      + apply gamma_derivation_app; auto.
        rew_nil_r ([(a, l')]); eauto.
      + unfold not; intros heq'.
        apply app_inj_tail in heq'; destruct heq'; tc.
    - (* tail case *)
      inv hp; inv hs; rewrite <- app_assoc.
      eapply AFD_tail; eauto; sis; apps.
      apply gamma_derivation_app; auto.
      rew_nil_r ([(a, l)]); auto.
  Qed.

  (* to do : these next lemmas should probably be in Prediction *)

  (* refactor *)
  Lemma llPredict'_ambig_rhs_leads_to_successful_parse' :
    forall g orig_sps wsuf wpre curr_sps rhs,
      all_suffix_stacks_wf g curr_sps
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
    induction wsuf as [| (a,l) wsuf' IH]; intros wpre curr_sps rhs ha hi hl; sis; tc.
    - (* lemma *)
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
      assert (hi''' : In csp'' curr_sps).
      { eapply filter_tail_in; eauto. }
      apply hi in hi'''.
      destruct hi''' as [orig_sp' [hi''' hm']].
      exists orig_sp; exists csp'; exists orig_sp'; exists csp'';
      exists csp''.(prediction); repeat split; auto.
      + eapply mcms'_preserves_label; eauto.
      + assert (hi'''' : In csp' (filter finalConfig curr_sps)).
        { rewrite hf'; apply in_eq. }
        eapply filter_In in hi''''; destruct hi''''; auto.
      + eapply mcms'_preserves_label; eauto.
      + assert (hi'''' : In csp'' (filter finalConfig curr_sps)). 
        { rewrite hf'; apply in_cons; auto. }
        eapply filter_In in hi''''; destruct hi''''; auto.
    - destruct curr_sps as [| csp csps]; tc.
      destruct (allPredictionsEqual _ _); tc.
      destruct (llTarget _ _ _) as [? | sps'] eqn:ht; tc.
      eapply IH with (wpre := wpre ++ [(a,l)]) in hl.
      + destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi' [heq [hm' [hf [hi'' [heq' [hm'' [hf' hn]]]]]]]]]]]]]; subst.
        rewrite <- app_assoc in *; sis.
        exists osp; exists fsp; exists osp'; exists fsp';
        exists osp'.(prediction); repeat split; eauto.
      + eapply llTarget_preserves_suffix_stacks_wf_invar; eauto.
      + eapply llTarget_preserves_subparsers_sound_invar; eauto.
  Qed.

    Lemma llPredict_ambig_rhs_unproc_stack_syms' :
    forall g cr ce o x suf frs w rhs,
      cr    = SF o (NT x :: suf)
      -> ce = SF (Some x) rhs
      -> no_left_recursion g
      -> suffix_stack_wf g (cr, frs)
      -> llPredict g x (cr, frs) w = PredAmbig rhs
      -> gamma_recognize g (rhs ++ suf ++ unprocTailSyms frs) w
         /\ (exists rhs',
                In (x, rhs') g
                /\ rhs' <> rhs
                /\ gamma_recognize g (rhs' ++ suf ++ unprocTailSyms frs) w).
  
  Proof.
    intros g cr ce o x suf frs w rhs ? ? hn hw hl; subst; sis.
    pose proof hl as hl'; apply llPredict_ambig_in_grammar in hl'.
    unfold llPredict in hl.
    destruct (startState _ _ _) as [m | sps] eqn:hs; tc.
    eapply llPredict'_ambig_rhs_leads_to_successful_parse'
      with (orig_sps := sps) (wpre := []) in hl; sis.
    - destruct hl as [osp [fsp [osp' [fsp' [rhs' [hi [heq [hm [hf [hi' [heq' [hm' [hf' hn']]]]]]]]]]]]]; subst.
      split.
      + eapply mcms'_final_config in hm; auto.
        eapply closure_ussr_backwards with (sp' := osp) (w := w) in hs; eauto.
        * destruct hs as [init_sp [av' [hi'' [hc hg]]]].
          (* lemma? *)
          unfold initSps in hi''.
          apply in_map_iff in hi''.
          destruct hi'' as [rhs [heq hi'']]; subst; sis.
          apply closure_multistep_preserves_label in hc; sis; subst; auto.
        * (* lemma *)
          red. intros init_sp hi''.
          eapply initSps_preserves_suffix_stack_wf_invar; eauto.
      + exists osp'.(prediction); repeat split; auto.
        * eapply startState_sp_prediction_in_rhssForNt
            with (sp' := osp') in hs; eauto.
          apply rhssForNt_in_iff in hs; auto.
        * eapply mcms'_final_config in hm'; auto.
          eapply closure_ussr_backwards with (sp' := osp') (w := w) in hs; auto.
          -- destruct hs as [init_sp [av' [hi'' [hc hg]]]].
             (* lemma? *)
             unfold initSps in hi''.
             apply in_map_iff in hi''.
             destruct hi'' as [rhs [heq hi'']]; subst; sis.
             apply closure_multistep_preserves_label in hc; sis; subst; auto.
          -- red; intros init_sp hi''.
             eapply initSps_preserves_suffix_stack_wf_invar; eauto.
    - eapply startState_preserves_stacks_wf_invar; eauto. 
    - red. intros sp' hi; sis.
      exists sp'; split; auto.
      eapply closure_func_refines_closure_multistep_backward in hi; eauto.
      + destruct hi as [av'' [sp [hi hc]]].
        assert (hst : stable_config sp'.(stack)).
        { eapply stable_config_after_closure_multistep; eauto. }
        destruct sp' as [pred ([suf'], frs')]; inv hst; auto.
      + intros sp hi'; eapply initSps_preserves_suffix_stack_wf_invar; eauto.
  Qed.

  Definition ambiguous_stack_prefix_derivation g w p_stk s_stk wsuf u :=
    match p_stk, s_stk with
    | (p_fr, p_frs), (s_fr, s_frs) =>
      u = false
      -> exists wpre,
          w = wpre ++ wsuf
          /\ ambiguous_frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) wpre wsuf
    end.

  Lemma ambiguous_stack_prefix_derivation_invar_starts_true :
    forall g ys ts,
      ambiguous_stack_prefix_derivation g ts (PF [] [], []) (SF None ys, []) ts true.
  Proof.
    intros g ys ts hc; inv hc.
  Qed.

    Lemma step_preserves_ambiguous_stack_prefix_derivation_invar :
    forall g cm w ps ps' ss ss' ts ts' av av' un un' ca ca',
      no_left_recursion g
      -> stacks_wf g ps ss
      -> stack_prefix_derivation g w ps ss ts
      -> ambiguous_stack_prefix_derivation g w ps ss ts un
      -> step g cm ps ss ts av un ca = StepK ps' ss' ts' av' un' ca'
      -> ambiguous_stack_prefix_derivation g w ps' ss' ts' un'.
  Proof.
    intros g cm w (p_fr, p_frs) (p_fr', p_frs') (s_fr, s_frs) (s_fr', s_frs') 
           ts ts' av av' un un' ca ca' hn hw hp ha hs; red; red in ha; intros hu.
    unfold step in hs; dmeqs h; inv hs; tc.
    - (* return *)
      destruct ha as (wpre & heq & ha); subst; sis; auto.
      exists wpre.
      eapply return_preserves_ambiguous_frames_derivation_invar in ha; eauto.
    - (* consume *)
      destruct ha as (wpre & heq & ha); subst; sis; auto.
      eexists; split.
      + rewrite cons_app_singleton; rewrite app_assoc; eauto.
      + eapply consume_preserves_ambiguous_frames_derivation_invar; eauto.
    - (* unambiguous push *)
      destruct ha as (wpre & heq & ha); subst; sis; auto. 
      eexists; split; eauto.
      rew_nil_r wpre; eapply AFD_tail; eauto.
    - (* ambiguous push *)
      destruct hp as (wpre & heq & hd); subst.
      exists wpre; split; auto.
      rew_nil_r wpre.
      eapply adaptivePredict_ambig_llPredict_ambig in h4; eauto.
      pose proof h4 as h4'; apply llPredict_ambig_in_grammar in h4'.
      eapply llPredict_ambig_rhs_unproc_stack_syms' in h4; eauto.
      + destruct h4 as [hr [rhs' [hi [hneq hr']]]].
        eapply AFD_push; eauto.
      + eapply frames_wf__suffix_frames_wf; eauto.
  Qed.

  Lemma multistep_sound_ambig' :
    forall (g      : grammar)
           (cm     : closure_map)
           (tri    : nat * nat * nat)
           (a      : Acc lex_nat_triple tri)
           (w wsuf : list token)
           (av     : NtSet.t)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a'     : Acc lex_nat_triple (meas g ss wsuf av))
           (v      : forest),
      tri = meas g ss wsuf av
      -> no_left_recursion g
      -> stacks_wf g ps ss
      -> stack_prefix_derivation g w ps ss wsuf
      -> ambiguous_stack_prefix_derivation g w ps ss wsuf un
      -> multistep g cm ps ss wsuf av un ca hc a' = Ambig v
      -> gamma_derivation g (bottomFrameSyms ps ss) w v
         /\ (exists v',
                gamma_derivation g (bottomFrameSyms ps ss) w v'
                /\ v' <> v).
  Proof.
    intros g cm tri a.
    induction a as [tri hlt IH].
    intros w wsuf av ps ss un ca hc a' v ? hn hw hd ha hm; subst.
    apply multistep_ambig_cases in hm.
    destruct hm as [[hs hu] | he]; subst.
    - apply step_StepAccept_facts in hs.
      destruct hs as (? & ? & ? & (pre & ?)); subst.
      unfold bottomFrameSyms; simpl; rewrite app_nil_r.
      red in ha.
      destruct ha as [wpre [heq ha]]; subst; auto; rew_anr.
      clear IH. clear a'. clear hlt.
      (* lemma *)
      inv_afd ha  ha' heq hf hg hg' hi hi' hneq hr.
      + inv hp; inv hs; rew_anr; subst.
        inv hr; inv hf; rew_anr; sis.
        rewrite rev_involutive in *.
        firstorder.
      + inv ha'.
    - destruct he as (ps' & ss' & ts' & av' & un' & ca' & hc' & a'' & hs & hm).
      eapply IH with (w := w) in hm; eauto.
      + erewrite step_preserves_bottomFrameSyms_invar; eauto.
      + eapply step_meas_lt with (ca := ca); eauto.
      + eapply step_preserves_stacks_wf_invar with (ca := ca); eauto.
      + eapply step_preserves_stack_prefix_derivation_invar with (ca := ca); eauto.
      + eapply step_preserves_ambiguous_stack_prefix_derivation_invar; eauto.
  Qed.

  Lemma multistep_sound_ambig :
    forall (g      : grammar)
           (cm     : closure_map)
           (w wsuf : list token)
           (av     : NtSet.t)
           (ps     : prefix_stack)
           (ss     : suffix_stack)
           (un     : bool)
           (ca     : cache)
           (hc     : cache_stores_target_results g cm ca)
           (a      : Acc lex_nat_triple (meas g ss wsuf av))
           (v      : forest),
      no_left_recursion g
      -> stacks_wf g ps ss
      -> stack_prefix_derivation g w ps ss wsuf
      -> ambiguous_stack_prefix_derivation g w ps ss wsuf un
      -> multistep g cm ps ss wsuf av un ca hc a = Ambig v
      -> gamma_derivation g (bottomFrameSyms ps ss) w v
         /\ (exists v',
                gamma_derivation g (bottomFrameSyms ps ss) w v'
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
    - exists []; eauto. 
    - apply ambiguous_stack_prefix_derivation_invar_starts_true.
  Qed.

End ParserSoundFn.
