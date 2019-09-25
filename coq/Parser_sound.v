Require Import Arith List.
Require Import GallStar.Defs. 
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Import ListNotations.

Fixpoint bottomFrame' (h : frame) (t : list frame) : frame :=
  match t with
  | []        => h
  | fr :: frs => bottomFrame' fr frs
  end.

Definition bottomFrame (stk : p_stack) : frame :=
  let (h, t) := stk in bottomFrame' h t.

Definition bottomFrameSyms (stk : p_stack) : list symbol :=
  let fr := bottomFrame stk
  in  fr.(loc).(rpre) ++ fr.(loc).(rsuf).

Ltac induct_list_length xs := 
  remember (List.length xs) as l;
  generalize dependent xs;
  induction l as [l IHl] using lt_wf_ind;
  intros xs Hl; subst.

Ltac induct_stackScore g av stk :=
  remember (stackScore (locStackOf stk) 
                       (1 + (maxRhsLength g))
                       (NtSet.cardinal av)) 
    as sc;
  generalize dependent stk;
  generalize dependent av;
  induction sc as [sc IHsc] using lt_wf_ind;
  intros av stk Hsc; subst.

Ltac induct_stackHeight stk :=
  remember (stackHeight stk) as ht;
  induction ht as [ht IHht] using lt_wf_ind;
  intros stk Hht; subst.

Lemma multistep_unfold :
  forall g st a,
    multistep g st a = 
    match step g st as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _  => Accept sv
    | StepReject s  => fun _  => Reject s
    | StepK st'     => fun hs =>
                         multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s   => fun _  => Error s
    end eq_refl.
Proof.
  intros; destruct a; auto.
Qed.              

Lemma multistep_cases' :
  forall (g   : grammar)
         (st  : parser_state)
         (a   : Acc lex_nat_triple (Parser.meas g st))
         (sr  : step_result)
         (pr  : parse_result)
         (heq : step g st = sr),
    match sr as res return (step g st = res -> parse_result) with
    | StepAccept sv => fun _ => Accept sv
    | StepReject s => fun _  => Reject s
    | StepK st' => fun hs => multistep g st' (StepK_st_acc g st st' a hs)
    | StepError s => fun _ => Error s
    end heq = pr
    -> match pr with
       | Accept f => sr = StepAccept f
                     \/ exists st' a', sr = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Reject s => sr = StepReject s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Reject s
       | Error s  => sr = StepError s
                     \/ exists st' a', sr = StepK st'
                                       /\ multistep g st' a' = Error s
       end.
Proof.
  intros g st a sr pr heq.
  destruct pr; destruct sr; subst;
    try solve [ intros; tc | intros h; inv h; auto | intros h; right; eauto ].
Qed.

Lemma multistep_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (Parser.meas g st))
         (pr  : parse_result),
    multistep g st a = pr
    -> match pr with
       | Accept f => step g st = StepAccept f
                     \/ exists st' a', step g st = StepK st' 
                                       /\ multistep g st' a' = Accept f
       | Reject s => step g st = StepReject s
                     \/ exists st' a', step g st = StepK st'
                                       /\ multistep g st' a' = Reject s
       | Error s  => step g st = StepError s
                     \/ exists st' a', step g st = StepK st'
                                       /\ multistep g st' a' = Error s
       end.
Proof.
  intros g st a pr hm; subst.
  rewrite multistep_unfold.
  eapply multistep_cases'; eauto.
Qed.

Lemma multistep_accept_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (Parser.meas g st))
         (f  : forest),
    multistep g st a = Accept f
    -> step g st = StepAccept f
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Accept f.
Proof.
  intros g st a f hm; subst.
  destruct (multistep_cases g st a (Accept f)); auto.
Qed.

Lemma step_StepAccept_facts :
  forall g av stk ts v,
    step g (Pst av stk ts) = StepAccept v
    -> (exists xo rpre v',
           stk = (Fr (Loc xo rpre []) v', [])
           /\ v' = v)
       /\ ts = [].
Proof.
  intros g av stk ts v hs.
  unfold step in hs; dms; tc.
  inv hs; repeat eexists; eauto.
Qed.

Inductive stack_wf (g : grammar) : p_stack -> Prop :=
| WF_nil :
    forall pre suf v,
      stack_wf g (Fr (Loc None pre suf) v, [])
| WF_cons :
    forall x xo' pre pre' suf suf' v v' frs,
      In (x, pre ++ suf) g
      -> stack_wf g (Fr (Loc xo' pre' (NT x :: suf')) v', frs) 
      -> stack_wf g (Fr (Loc (Some x) pre suf) v, 
                     Fr (Loc xo' pre' (NT x :: suf')) v' :: frs).

Hint Constructors stack_wf.

Inductive stack_derivation (g : grammar) : p_stack -> list token -> Prop :=
| SD_nil :
    forall xo pre suf v w,
      gamma_derivation g pre w v
      -> stack_derivation g (Fr (Loc xo pre suf) v, []) w
| SD_cons :
    forall xo pre suf v fr' frs wpre wsuf,
      gamma_derivation g pre wsuf v
      -> stack_derivation g (fr', frs) wpre
      -> stack_derivation g (Fr (Loc xo pre suf) v, fr' :: frs) (wpre ++ wsuf).

Hint Constructors stack_derivation.

Ltac inv_sd hsd wpre wsuf hgd hsd' := inversion hsd as [? ? ? ? wpre hgd | ? ? ? ? ? ? wpre wsuf hgd hsd']; subst; clear hsd.

(* MAYBE NOT NECESSARY 
Lemma stack_derivation_accept_impl_gamma_derivation :
  forall fr stk g wpre av ts v,
  bottom_frame fr stk
  -> stack_derivation g stk wpre v
  -> step g (Pst av stk ts) = StepAccept v
  -> gamma_derivation g fr.(loc).(rpre) wpre v.
Proof.
  intros fr stk g wpre av ts v hb hsdp hf.
  apply step_StepAccept_facts in hf.
  destruct hf as [[xo [rpre [v' [heq heq']]]] hnil].
  subst.
  inv hb.
  inv hsdp.
  simpl; auto.
Qed.
 *)

Inductive stack_derivation_invar (g : grammar) (stk : p_stack) (wsuf w : list token) : Prop :=
| SD_invar :
    forall wpre,
      stack_derivation g stk wpre
      -> wpre ++ wsuf = w
      -> stack_derivation_invar g stk wsuf w.

Ltac inv_sdi wpre hsd := match goal with
                         | H : stack_derivation_invar _ _ _ _ |- _ =>
                           inversion H as [wpre hsd ?]; subst; clear H
                         end.

Lemma gamma_derivation_app :
  forall g ys1 w1 v1,
    gamma_derivation g ys1 w1 v1
    -> forall ys2 w2 v2,
      gamma_derivation g ys2 w2 v2
      -> gamma_derivation g (ys1 ++ ys2) (w1 ++ w2) (v1 ++ v2).
Proof.
  intros g ys1 w1 v1 hg.
  induction hg; intros ys2 w2 v2 hg2; simpl in *; auto.
  rewrite <- app_assoc.
  constructor; auto.
Qed.

Lemma app_nil_r' : forall A (xs : list A), xs = xs ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Ltac rew_nilr xs := replace xs with (xs ++ []) by apply app_nil_r'.

Lemma stack_derivation_cases :
  forall g fr frs w,
    stack_derivation g (fr, frs) w
    -> match frs with
       | []          => gamma_derivation g fr.(loc).(rpre) w fr.(sem)
       | fr' :: frs' =>
         exists wpre wsuf,
         wpre ++ wsuf = w
         /\ stack_derivation g (fr', frs') wpre
         /\ gamma_derivation g fr.(loc).(rpre) wsuf fr.(sem)
       end.
Proof.
  intros g fr frs w hsd.
  destruct frs as [| fr' frs]; inv hsd; auto.
  repeat eexists; repeat split; auto.
Qed.

Lemma derivation_app_nil_r :
  forall g ys w v,
    gamma_derivation g ys w [v] = gamma_derivation g (ys ++ []) (w ++ []) [v].
Proof.
  intros g ys w v.
  assert (happ : w = w ++ []) by (rewrite <- app_nil_r'; auto); rewrite happ; clear happ.
Abort.

Lemma forest_app_singleton_node : 
  forall g x ys ys' w w' v v',
    In (x, ys') g
    -> gamma_derivation g ys w v
    -> gamma_derivation g ys' w' v'
    -> gamma_derivation g (ys ++ [NT x]) (w ++ w') (v ++ [Node x v']).
Proof.
  intros g x ys ys' w w' v v' hi hg hg'.
  apply gamma_derivation_app; auto.
  assert (happ : w' = w' ++ []) by (rewrite <- app_nil_r'; auto); rewrite happ; clear happ.
  repeat (econstructor; eauto).
Qed.

Lemma cons_app_singleton :
  forall A (x : A) (ys : list A),
    x :: ys = [x] ++ ys.
Proof.
  auto.
Qed.

Lemma terminal_head_gamma_derivation :
  forall g a l ys w v,
    gamma_derivation g ys w v
    -> gamma_derivation g (T a :: ys) ((a, l) :: w) (Leaf l :: v).
Proof.
  intros g a l ys w v hg.
  assert (happ : (a, l) :: w = [(a, l)] ++ w) by (rewrite cons_app_singleton; auto).
  rewrite happ; clear happ.
  constructor; auto.
Qed.

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

Lemma in_rhssForNt_production_in_grammar :
  forall g x ys,
    In ys (rhssForNt g x)
    -> In (x, ys) g.
Proof.
  intros g x ys hin.
  induction g as [| (x', ys') g]; sis; tc.
  destruct (nt_eq_dec x' x); subst; auto.
  inv hin; auto.
Qed.

Lemma llPredict_succ_arg_result_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredSucc ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply PredSucc_result_in_rhssForNt in hp.
  apply in_rhssForNt_production_in_grammar; auto.
Qed.

Lemma llPredict_ambig_arg_result_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredAmbig ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply in_rhssForNt_production_in_grammar.
  eapply PredAmbig_result_in_rhssForNt; eauto.
Qed.

Lemma step_preserves_stack_wf_invar :
  forall g av av' stk stk' ts ts',
    step g (Pst av stk ts) = StepK (Pst av' stk' ts')
    -> stack_wf g stk 
    -> stack_wf g stk'.
Proof.
  intros g av av' stk stk' ts ts' hs hw.
  unfold step in hs.
  repeat (dmeq h); inv hs; tc.
  - (* return *)
    inv hw.
    inv H10; constructor; auto.
    rewrite <- app_assoc; auto.
  - inv hw; auto.
    constructor; auto.
    rewrite <- app_assoc; auto.
  - constructor; simpl; auto.
    eapply llPredict_succ_arg_result_in_grammar; eauto.
  - constructor; simpl; auto. 
    eapply llPredict_ambig_arg_result_in_grammar; eauto.
Qed.    

Lemma multistep_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (w wsuf : list token)
         (av     : NtSet.t)
         (stk    : p_stack)
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
Print Assumptions parser_sound.
  