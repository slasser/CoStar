Require Import Arith List Logic.JMeq.
Require Import GallStar.Defs. 
Require Import GallStar.Lex.
Require Import GallStar.Parser.
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
    | StepAccept sv => fun _ : step g st = StepAccept sv => Accept sv
    | StepReject s => fun _ : step g st = StepReject s => Reject s
    | StepK st' =>
      fun Hs : step g st = StepK st' =>
        multistep g st' (StepK_st_acc g st st' a Hs)
    | StepError s => fun _ : step g st = StepError s => Error s
    end eq_refl.
Proof.
  intros; destruct a; auto.
Qed.              

Lemma multistep_cases' :
  forall (g   : grammar)
         (st  : parser_state)
         (a   : Acc lex_nat_triple (meas g st))
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
  destruct pr; destruct sr; subst; try solve [intros; congruence].
  - intros h; inv h; auto.
  - intros h; right; eauto.
  - intros h; inv h; auto.
  - intros h; right; eauto.
  - intros h; right; eauto.
  - intros h; inv h; auto.
Qed.

Lemma multistep_cases :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
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

Lemma multistep_accept :
  forall (g : grammar)
         (st : parser_state)
         (a  : Acc lex_nat_triple (meas g st))
         (f  : forest),
    multistep g st a = Accept f
    -> step g st = StepAccept f
       \/ exists st' a', step g st = StepK st' 
                         /\ multistep g st' a' = Accept f.
Proof.
  intros g st a f hm; subst.
  destruct (multistep_cases g st a (Accept f)); auto.
Qed.

Lemma multistep_sound :
  forall (g   : grammar)
         (ts  : list token)
         (av  : NtSet.t)
         (stk : p_stack)
         a
         (trs : forest),
    multistep g (Pst av stk ts) a = Accept trs
    -> exists trs_suf,
      trs = (bottomFrame stk).(sem) ++ trs_suf
      /\ gamma_derivation g (bottomFrame stk).(loc).(rsuf) ts trs_suf.
Proof.
  (* nested induction on lexicographic components of the multistep measure *)
  intros g ts; induct_list_length ts.
  intros av stk; induct_stackScore g av stk.
  (*remember (stackHeight stk) as ht eqn:Hht.
  generalize dependent stk.
  induction ht as [ht IHht] using lt_wf_ind.
  intros stk IHsc Hht; subst. *)
  intros a trs hm.
  apply multistep_accept in hm.
  destruct hm as [hs | he].
  - clear IHl; clear IHsc.
    (* prove that if some "partial derivation" invariant holds of the parser state,
       this goal is provable *)
    admit.
  - destruct he as [st' [a' [hs hm]]].
    (* I think the induction hypotheses will give me this one. I might also
       have to prove that "step" preserves whatever invariant I used in the
       previous goal. *)
    admit.
Admitted.

Theorem parser_sound :
  forall (g : grammar)
         (ss : list symbol)
         (ts : list token)
         (trs : forest),
    parse g ss ts = Accept trs -> gamma_derivation g ss ts trs.
Proof.
  intros g ss ts trs Hp.
  unfold parse in Hp.
  apply multistep_sound in Hp.
  destruct Hp as [trs_suf [Heq Hd]]; subst; simpl in *; auto.
Qed.
  