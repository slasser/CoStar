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

Inductive stack_derivation (g : grammar) : p_stack -> list token -> forest -> Prop :=
| SD_nil :
    forall xo pre suf w v,
    gamma_derivation g pre w v
    -> stack_derivation g (Fr (Loc xo pre suf) v, []) w v
| SD_cons :
    forall xo pre suf w w' v v' fr frs,
      gamma_derivation g pre w' v'
      -> stack_derivation g (fr, frs) w v
      -> stack_derivation g (Fr (Loc xo pre suf) v', fr :: frs) (w ++ w') (v ++ v').

Inductive stack_wf (g : grammar) : p_stack -> Prop :=
| WF_nil :
    forall pre suf v,
      stack_wf g (Fr (Loc None pre suf) v, [])
| WF_cons :
    forall x pre suf suf' v fr frs,
      In (x, pre ++ suf) g
      -> fr.(loc).(rsuf) = NT x :: suf'
      -> stack_wf g (fr, frs) 
      -> stack_wf g (Fr (Loc (Some x) pre suf) v, fr :: frs).

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
    forall wpre vpre,
      stack_derivation g stk wpre vpre
      -> wpre ++ wsuf = w
      -> stack_derivation_invar g stk wsuf w.

Lemma return_preserves_stack_derivation_invar :
  forall g callee caller caller' frs x xo xo_cr pre pre_cr suf_cr v v_cr wsuf w,
    stack_wf g (callee, caller :: frs)
    -> callee  = Fr (Loc xo pre []) v
    -> caller  = Fr (Loc xo_cr pre_cr (NT x :: suf_cr)) v_cr
    -> caller' = Fr (Loc xo_cr (pre_cr ++ [NT x]) suf_cr) (v_cr ++ [Node x v])
    -> stack_derivation_invar g (callee, caller :: frs) wsuf w
    -> stack_derivation_invar g (caller', frs) wsuf w.
Proof.
  intros g ce cr cr' frs x xo xo_cr pre pre_cr suf_cr v v_cr wsuf w hwf hce hcr hcr' hi; subst.
  inv hi.
  inv H.
  inv hwf.
  destruct frs.
  - econstructor; eauto. 
    eapply SD_nil. 
    simpl in *.
    admit.
  - simpl in *. 
    econstructor; eauto. 
    eapply SD_cons; eauto.
    
Admitted.

Lemma step_preserves_stack_derivation_invar :
  forall g av av' stk stk' wsuf wsuf' w,
    stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> step g (Pst av stk wsuf) = StepK (Pst av' stk' wsuf')
    -> stack_derivation_invar g stk' wsuf' w.
Proof.
  intros g av av' stk stk' wsuf wsuf' w hw hi hs.
  unfold step in hs.
  destruct stk as (fr, frs).
  destruct fr as [(xo, rpre, rsuf) v].
  destruct rsuf.
  - destruct frs as [| fr_cr frs].
    + destruct wsuf; tc.
    + destruct fr_cr as [(xo_cr, pre_cr, suf_cr) v_cr].
      destruct suf_cr as [| [a | x] suf_cr]; tc.
      inv hs.
      eapply return_preserves_stack_derivation_invar; eauto.
      admit.
  - destruct s as [a | x].
    + destruct wsuf as [| (a', l) wsuf]; tc.
      destruct (t_eq_dec a' a); tc; subst.
      inv hs.
      (* consuming a token preserves invariant *)
      admit.
    + destruct (NtSet.mem x av); tc.
      dmeq hpred; tc.
      * inv hs.
        (* push preserves invariant *)
        admit.
      * inv hs.
        (* push preserves invariant *)
        admit.
Admitted.

Lemma multistep_sound :
  forall (g    : grammar)
         (w wsuf : list token)
         (av   : NtSet.t)
         (stk  : p_stack)
         (a    : Acc lex_nat_triple (Parser.meas g (Pst av stk wsuf)))
         (v    : forest),
    stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> multistep g (Pst av stk wsuf) a = Accept v
    -> gamma_derivation g (bottomFrameSyms stk) w v.
Proof.
  intros g w wsuf.
  induct_list_length wsuf.
  intros av stk a v hw hs hm.
  apply multistep_accept_cases in hm.
  destruct hm as [hf | he].
  - (* the parser state is in a "final configuration" *)
    apply step_StepAccept_facts in hf.
    destruct hf as [[xo [rpre [v' [heq]]]] heq']; subst.
    inv hs.
    simpl in *.
    unfold bottomFrameSyms; simpl.
    inv H.
    repeat rewrite app_nil_r; auto.
  - (* parser is in a non-final configuration *)
    destruct he as [st' [a' [hf hm]]].
    destruct st' as [av' stk' wsuf'].
    assert (hl : length wsuf' < length wsuf) by admit.
    assert (hex : exists fr', bottom_frame fr' stk') by admit.
    apply step_preserves_stack_derivation_invar with (w := w) in hf; auto.
    destruct hex as [fr' hb'].
    eapply IHl with (m := length wsuf')
                    (wsuf := wsuf')
                    (av := av')
                    (stk := stk') in hl; eauto; clear IHl.
    + assert (bottomFrameSyms stk = bottomFrameSyms stk') by admit. 
      rewrite H; auto.
    + (* step preserves stack well-formedness *)
      admit.
Admitted.

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
  - unfold bottomFrameSyms; auto.
  - eapply SD_invar with (wpre := []); auto.
    repeat constructor.
Qed.

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
  