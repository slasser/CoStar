Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Parser_error_free.
Require Import Prediction.
Require Import GallStar.Tactics.
Import ListNotations.

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

Inductive stack_recognize (g : grammar) : parser_stack -> list token -> Prop :=
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
    