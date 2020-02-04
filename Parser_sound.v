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

(* The stronger parser soundness theorems -- one for unique derivations, one for
   ambiguous derivations, appear below. *)

Inductive frames_derivation (g : grammar) :
  list prefix_frame -> list suffix_frame -> list token -> Prop :=
| FD_bottom  :
    forall pre suf wpre v,
      gamma_derivation g (rev pre) wpre (rev v)
      -> frames_derivation g [PF pre v] [SF suf] wpre
| FD_upper :
    forall p_cr p_frs s_cr s_frs x pre' suf suf' v' wpre wmid,
      SF (NT x :: suf) = s_cr
      -> In (x, rev pre' ++ suf') g
      -> gamma_derivation g (rev pre') wmid (rev v')
      -> frames_derivation g (p_cr :: p_frs)
                             (s_cr :: s_frs)
                             wpre
      -> frames_derivation g (PF pre' v' :: p_cr :: p_frs)
                             (SF suf'    :: s_cr :: s_frs)
                             (wpre ++ wmid).

Hint Constructors frames_derivation.

Ltac inv_fd hf hf':=
  let heq := fresh "heq" in
  let hi  := fresh "hi"  in
  let hg  := fresh "hg"  in
  inversion hf as [ ? ? ? ? hg 
                  | ? ? ? ? ? ? ? ? ? ? ? heq hi hg hf']; subst; clear hf.

Lemma return_preserves_frames_derivation :
  forall g p_ce p_cr p_cr' s_ce s_cr s_cr' p_frs s_frs pre pre' suf x v v' wpre,
    p_ce     = PF pre' v'
    -> s_ce  = SF []
    -> p_cr  = PF pre v
    -> p_cr' = PF (NT x :: pre) (Node x (rev v') :: v)
    -> s_cr  = SF (NT x :: suf)
    -> s_cr' = SF suf
    -> frames_derivation g (p_ce :: p_cr :: p_frs)
                           (s_ce :: s_cr :: s_frs)
                            wpre
    -> frames_derivation g (p_cr' :: p_frs)
                           (s_cr' :: s_frs)
                            wpre.
Proof.
  intros g ? ? ? ? ? ? p_frs s_frs pre pre' suf x v v' wpre
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
  forall g p_fr p_fr' s_fr s_fr' p_frs s_frs pre suf a l v wpre,
    p_fr     = PF pre v
    -> p_fr' = PF (T a :: pre) (Leaf a l :: v)
    -> s_fr  = SF (T a :: suf)
    -> s_fr' = SF suf
    -> frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) 
                            wpre
    -> frames_derivation g (p_fr' :: p_frs) (s_fr' :: s_frs) 
                           (wpre ++ [(a, l)]).
Proof.
  intros g ? ? ? ? p_frs s_frs pre suf a l v wpre
         ? ? ? ? hf; subst; inv hf.
  - constructor; sis.
    apply gamma_derivation_app; auto.
    rew_nil_r [(a,l)]; auto.
  - rewrite <- app_assoc; econstructor; eauto; sis; apps.
    apply gamma_derivation_app; auto.
    rew_nil_r [(a,l)]; auto.
Qed.

Lemma push_preserves_frames_derivation :
  forall g p_cr p_ce s_cr s_ce p_frs s_frs x rhs pre suf wpre v,
    p_cr     = PF pre v
    -> p_ce  = PF [] []
    -> s_cr  = SF (NT x :: suf)
    -> s_ce  = SF rhs
    -> In (x, rhs) g
    -> frames_derivation g (p_cr :: p_frs) (s_cr :: s_frs) 
                            wpre
    -> frames_derivation g (p_ce :: p_cr :: p_frs) (s_ce :: s_cr :: s_frs) 
                            wpre.
Proof.
  intros g ? ? ? ? p_frs s_frs x rhs pre suf wpre v ? ? ? ? hi hf; subst.
  rew_nil_r wpre; eauto.
Qed.    

Definition frames_prefix_derivation g w p_stk s_stk wsuf :=
  match p_stk, s_stk with
  | (p_fr, p_frs), (s_fr, s_frs) =>
    exists wpre,
    w = wpre ++ wsuf
    /\ frames_derivation g (p_fr :: p_frs) (s_fr :: s_frs) wpre
  end.

Lemma step_preserves_frames_prefix_derivation :
  forall g w ps ps' ss ss' ts ts' av av' u u',
    frames_prefix_derivation g w ps ss ts
    -> step g ps ss ts av u = StepK ps' ss' ts' av' u'
    -> frames_prefix_derivation g w ps' ss' ts'.
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
    -> stack_wf g (Parser.stack st)
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

Lemma multistep_sound_unambig' :
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
         (a      : Acc lex_nat_triple (Parser.meas g (Pst av stk wsuf u)))
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
    stack_wf g (Parser.stack st)
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