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

Definition unprocTailSyms' (frs : list frame) :=
  unprocTailSyms (map loc frs).

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

(* Note: using st here, as opposed to the deconstructed components, seems to work well *)
Inductive unique_stack_prefix_derivation g st w : Prop :=
| USPD :
    forall av stk wpre wsuf u,
      st = Pst av stk wsuf u
      -> wpre ++ wsuf = w
      -> gamma_derivation g (procStackSyms stk) wpre (stackVals stk)
      -> (u = true
          -> (forall wpre' wsuf' v',
                 wpre' ++ wsuf' = w
                 -> gamma_derivation g (procStackSyms stk) wpre' v'
                 -> gamma_recognize g (unprocStackSyms' stk) wsuf'
                 -> wpre' = wpre /\ wsuf' = wsuf /\ v' = (stackVals stk)))
      -> unique_stack_prefix_derivation g st w.

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
Qed.  

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
  - apply lex_nat_triple_wf.
  - constructor. (* how do I get auto to take care of this? *)
  - apply stack_prefix_derivation_init. 
Qed.


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

    
  list token -> parser_stack -> list token -> 
Inductive
stack_prefix_derivation (g : grammar) (stk : parser_stack)
(wsuf w : list token) : Prop :=
    SPD : forall wpre : list token,
          stack_derivation g stk wpre ->
          wpre ++ wsuf = w ->
          stack_prefix_derivation g stk wsuf w

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
    