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
    + admit.
    + inv hu. 
      inv H1.
      apply lhs_mem_allNts_true in H0. 
      tc.
  - destruct st' as [av' stk' w' u']. 
    eapply IH with (y := meas g (Pst av' stk' w' u')); eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto. 
    + eapply step_preserves_ussr; eauto.
Admitted.
Print Assumptions ussr_implies_multistep_doesn't_reject.



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
    