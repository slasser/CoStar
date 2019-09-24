Require Import Arith List.
Require Import GallStar.Defs. 
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.

Import ListNotations.

Definition stackSize (stk : p_stack) : nat := 
  match stk with
  | (fr, frs) => length (fr :: frs)
  end.

Program Fixpoint bottomFrame (stk : p_stack) {measure (stackSize stk)} : frame :=
  match stk with
  | (fr, [])       => fr
  | (_, fr :: frs) => bottomFrame (fr, frs)
  end.

Inductive bottom_frame : frame -> p_stack -> Prop :=
| BF_nil :
    forall fr,
      bottom_frame fr (fr, [])
| BF_cons :
    forall b_fr fr1 fr2 frs,
    bottom_frame b_fr (fr2, frs)
    -> bottom_frame b_fr (fr1, fr2 :: frs).

Lemma test :
  forall stk a b c,
    stk = (a, [b; c]) -> bottom_frame c stk.
Proof.
  intros stk a b c heq; subst; repeat constructor.
Qed.

Lemma bottomFrame_rew :
  forall (stk : p_stack),
    bottomFrame stk =
    match stk with
    | (fr, [])       => fr
    | (_, fr :: frs) => bottomFrame (fr, frs)
    end.
Proof.
  intros stk.
  unfold bottomFrame.
  rewrite Wf.fix_sub_eq.
  - destruct stk as (fr, frs).
    simpl.
    destruct frs as [| fr' frs']; auto.
  - intros.
    destruct x as (fr, frs).
    destruct frs as [| fr' frs']; auto.
Qed.
Print Assumptions bottomFrame_rew. (* proof_irrelevance *)

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

Definition frame_derivation_invar g fr : Prop :=
  exists wpre, gamma_derivation g fr.(loc).(rpre) wpre fr.(sem).

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

Inductive stack_derivation_invar (g : grammar) (stk : p_stack) (wsuf w : list token) : Prop :=
| SD_invar :
    forall wpre vpre,
      stack_derivation g stk wpre vpre
      -> wpre ++ wsuf = w
      -> stack_derivation_invar g stk wsuf w.

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
      (* return to caller frame preserves invariant *)
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
         (v    : forest)
         (fr   : frame),
    bottom_frame fr stk
    -> stack_wf g stk
    -> stack_derivation_invar g stk wsuf w
    -> multistep g (Pst av stk wsuf) a = Accept v
    -> gamma_derivation g (fr.(loc).(rpre) ++ fr.(loc).(rsuf)) w v.
Proof.
  intros g w wsuf.
  induct_list_length wsuf.
  intros av stk a v fr hb hw hsd hm.
  apply multistep_accept_cases in hm.
  destruct hm as [hs | he].
  - (* the parser state is in a "final configuration" *)
    apply step_StepAccept_facts in hs.
    destruct hs as [[xo [rpre [v' [heq]]]] heq']; subst.
    inv hb.
    inv hsd.
    simpl in *.
    inv H.
    repeat rewrite app_nil_r; auto.
  - (* parser is in a non-final configuration *)
    destruct he as [st' [a' [hs hm]]].
    destruct st' as [av' stk' wsuf'].
    assert (hl : length wsuf' < length wsuf) by admit.
    assert (hex : exists fr', bottom_frame fr' stk') by admit.
    apply step_preserves_stack_derivation_invar with (w := w) in hs; auto.
    destruct hex as [fr' hb'].
    eapply IHl with (m := length wsuf')
                    (wsuf := wsuf')
                    (av := av')
                    (stk := stk')
                    (fr  := fr') in hl; eauto; clear IHl.
    + assert (fr.(loc).(rpre) ++ fr.(loc).(rsuf) =
              fr'.(loc).(rpre) ++ fr'.(loc).(rsuf)) by admit.
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
  eapply multistep_sound with (w := ts)
                              (fr := Fr (Loc None [] ss) []) in hp; try (constructor; eauto).
  - simpl in *; auto.
  - apply SD_invar with (wpre := []) (vpre := []); auto.
    repeat constructor.
Qed.

(*
Lemma return_preserves_stack_derivation_invar :
  forall g xo rpre rpre2 x rsuf v1 v2 frs w1 w2 w3,
    stack_derivation_invar g (Fr (Loc xo rpre (NT x :: rsuf
    stack_derivation g (Fr (Loc xo rpre (NT x :: rsuf)) v, frs) w1 (w2 ++ w3)
    -> In (x, rpre2) g
    -> gamma_derivation g rpre2 w2 v2
    -> stack_derives_prefix g (Fr (Loc xo (rpre ++ [NT x]) rsuf) (v1 ++ [Node x v2]), frs) (w1 ++ w2) w3.
Proof.
  intros g xo rpre rpre2 x rsuf v1 v2 frs w1 w2 w3 hi hin hg.
  inv hi.
  - constructor.
    apply bar; auto.
    assert (happ : w2 = w2 ++ []) by (apply app_nil_r'); rewrite happ.
    repeat econstructor; eauto.
  - rewrite <- app_assoc; constructor.
    + apply bar; auto.
      assert (happ : w2 = w2 ++ []) by (apply app_nil_r').
      rewrite happ; repeat econstructor; eauto.
    + rewrite <- app_assoc; auto.
Qed.
 *)

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

(*
Lemma foo :
  forall g xo rpre rpre2 x rsuf v1 v2 frs w1 w2 w3,
    stack_derives_prefix g (Fr (Loc xo rpre (NT x :: rsuf)) v1, frs) w1 (w2 ++ w3)
    -> In (x, rpre2) g
    -> gamma_derivation g rpre2 w2 v2
    -> stack_derives_prefix g (Fr (Loc xo (rpre ++ [NT x]) rsuf) (v1 ++ [Node x v2]), frs) (w1 ++ w2) w3.
Proof.
  intros g xo rpre rpre2 x rsuf v1 v2 frs w1 w2 w3 hi hin hg.
  inv hi.
  - constructor.
    apply bar; auto.
    assert (happ : w2 = w2 ++ []) by (apply app_nil_r'); rewrite happ.
    repeat econstructor; eauto.
  - rewrite <- app_assoc; constructor.
    + apply bar; auto.
      assert (happ : w2 = w2 ++ []) by (apply app_nil_r').
      rewrite happ; repeat econstructor; eauto.
    + rewrite <- app_assoc; auto.
Qed.
 *)

(*
Lemma foo' :
  forall g xo pre a suf v frs wpre l wsuf',
    stack_derives_prefix g
                         (Fr (Loc xo pre (T a :: suf)) v, frs)
                         wpre
                         ((a, l) :: wsuf')
    -> stack_derives_prefix g
                            (Fr (Loc xo (pre ++ [T a]) suf) (v ++ [Leaf l]), frs)
                            (wpre ++ [(a, l)])
                            wsuf'.
Proof.
  intros g xo pre a suf v frs wpre l wsuf' hinv.
  inv hinv.
  - constructor.
    apply bar; auto.
    (* lemma *)
    assert (happ : [(a, l)] = [(a, l)] ++ []) by (apply app_nil_r'); rewrite happ; clear happ.
        assert (happ : [Leaf l] = [Leaf l] ++ []) by (apply app_nil_r'); rewrite happ; clear happ.
        econstructor; eauto.
        constructor.
        constructor.
  - rewrite <- app_assoc.
    constructor.
    + apply bar; auto.
      assert (happ : [(a, l)] = [(a, l)] ++ []) by (apply app_nil_r'); rewrite happ; clear happ.
      assert (happ : [Leaf l] = [Leaf l] ++ []) by (apply app_nil_r'); rewrite happ; clear happ.
      econstructor; eauto.
      constructor.
      constructor.
    + rewrite <- app_assoc; auto.
Qed.
*)
  
Lemma step_preserves_inv :
  forall g av av' stk stk' wpre wsuf wsuf',
    stack_wf g stk
    -> stack_derives_prefix g stk wpre wsuf
    -> step g (Pst av stk wsuf) = StepK (Pst av' stk' wsuf')
    -> exists wpre',
      wpre ++ wsuf = wpre' ++ wsuf'
      /\ stack_derives_prefix g stk' wpre' wsuf'.
Proof.
  intros g av av' stk stk' wpre wsuf wsuf' hwf hi hs.
  unfold step in hs.
  destruct stk as (fr, frs).
  destruct fr as [(xo, rpre, rsuf) v].
  destruct rsuf.
  - destruct frs as [| fr_cr frs].
    + destruct wsuf; tc.
    + destruct fr_cr as [(xo_cr, rpre_cr, rsuf_cr) v_cr].
      destruct rsuf_cr as [| [a | x] rsuf_cr]; tc.
      (* return case *)
      inv hs.
      inv hwf.
      inv hi.
      rename wpre0 into wpre.
      exists (wpre ++ wpre'); split; auto.
      eapply foo; eauto.
      rewrite app_nil_r; auto.
  - destruct s as [a | x].
    + destruct wsuf as [| (a', l) wsuf]; tc.
      destruct (t_eq_dec a' a); tc; subst.
      inv hs.
      exists (wpre ++ [(a, l)]).
      split.
      * rewrite <- app_assoc; auto.
      * eapply foo'; eauto. 
    + destruct (NtSet.mem x av); tc.
      dmeq hpred; tc.
      * inv hs.
        exists wpre; split; auto.
        assert (happ : wpre = wpre ++ []) by apply app_nil_r'; rewrite happ.
        constructor; auto.
        constructor.
      * inv hs.
        exists wpre; split; auto.
        assert (happ : wpre = wpre ++ []) by apply app_nil_r'.
        rewrite happ; constructor; auto.
        constructor.
Qed.
    

(*
(* maybe we need a four-place derivation relation including a remainder? *)
Lemma foo :
  forall g bfr bfr' av av' stk stk' ts ts' vsuf,
    bottom_frame bfr stk
    -> bottom_frame bfr' stk'
    -> step g (Pst av stk ts) = StepK (Pst av' stk' ts')
    -> gamma_derivation g bfr'.(loc).(rsuf) ts' vsuf
    -> exists w v,
        bfr.(sem) ++ v = bfr'.(sem) ++ vsuf
        /\ gamma_derivation g bfr.(loc).(rsuf) (w ++ ts) v.
Proof.
  intros g bfr bfr' av av' stk stk' ts ts' vsuf hbf hbf' hs hg.
  unfold step in hs.
  destruct stk as (fr, frs).
  destruct fr as [[xo pre suf] v].
  destruct suf as [| [a | x] suf_tl].
  - destruct frs as [| fr_cr frs].
    + destruct ts; tc.
    + destruct fr_cr as [[xo_cr pre_cr suf_cr] v_cr].
      (* we should know that the frame derivation invariant holds in the callee *)
      assert (hgd : exists w, gamma_derivation g pre w v) by admit.
      destruct hgd as [w hgd].
      destruct suf_cr as [| [a | x] suf_tl_cr]; tc.
      (* we should also know that (x, pre ++ suf) is a grammar production *)
      assert (hpr : In (x, pre) g) by admit.
      inv hs.
      inv hbf.
      destruct frs.
      * inv hbf'; inv H1.
        simpl in *.
        exists w; exists (Node x v :: vsuf).
        split.
        -- rewrite <- app_assoc; auto.
        -- constructor; auto.
           econstructor; eauto.
      * inv hbf'; inv H1.
        assert (bfr' = bfr) by admit; subst.
        exists nil; eexists; split; eauto.
  - destruct ts as [| (a', l) ts_tl]; tc.
    destruct (t_eq_dec a' a); tc; subst.
    inv hs.
    destruct frs.
    + inv hbf; inv hbf'.
      simpl in *.
      exists []; exists (Leaf l :: vsuf); split.
      * rewrite <- app_assoc; auto.
      * simpl.
        admit.
    + inv hbf; inv hbf'.
      assert (bfr = bfr') by admit; subst.
Abort.

Lemma multistep_sound :
  forall (g   : grammar)
         (ts  : list token)
         (av  : NtSet.t)
         (stk : p_stack)
         (a   : Acc lex_nat_triple (meas g (Pst av stk ts)))
         (v   : forest)
         (fr  : frame),
    bottom_frame fr stk
(*    -> frame_derivation_invar g fr *)
    -> multistep g (Pst av stk ts) a = Accept v
    -> exists vsuf,
      v = fr.(sem) ++ vsuf
      /\ gamma_derivation g fr.(loc).(rsuf) ts vsuf.
Proof.
Abort.
*)

Lemma multistep_sound :
  forall (g   : grammar)
         (ts  : list token)
         (av  : NtSet.t)
         (stk : p_stack)
         (a   : Acc lex_nat_triple (meas g (Pst av stk ts)))
         (v   : forest)
         (fr  : frame),
    bottom_frame fr stk
(*    -> frame_derivation_invar g fr *)
    -> multistep g (Pst av stk ts) a = Accept v
    -> exists vsuf,
      v = fr.(sem) ++ vsuf
      /\ gamma_derivation g fr.(loc).(rsuf) ts vsuf.
Proof.
  intros g ts.
  induct_list_length ts.
  intros av stk a v fr hbf hm.
  apply multistep_accept_cases in hm.
  destruct hm as [hs | he].
  - (* the parser state is in a "final configuration" *)
    apply step_StepAccept_facts in hs.
    destruct hs as [[xo [rpre [v' [heq]]]] heq']; subst.
    inv hbf.
    exists []; split; simpl; [rewrite app_nil_r; auto | constructor].
  - (* parser is in a non-final configuration *)
    destruct he as [st' [a' [hs hm]]].
    destruct st' as [av' stk' ts'].
    assert (hl : length ts' < length ts) by admit.
    assert (hex : exists fr', bottom_frame fr' stk') by admit.
    destruct hex as [fr' hbf'].
    eapply IHl with (m := length ts')
                    (ts := ts')
                    (av := av')
                    (stk := stk')
                    (fr  := fr') in hl; eauto.
    destruct hl as [vsuf [heq hgd]]; subst.
    clear IHl.
    eapply foo; eauto.
    (* I think the induction hypotheses will give me this one. I might also
       have to prove that "step" preserves whatever invariant I used in the
       previous goal. *)
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
  eapply multistep_sound with (fr := Fr (Loc None [] ss) []) in hp.
  - destruct hp as [vsuf [heq hgd]]; subst; simpl in *; auto.
  - constructor; auto.
Qed.
  