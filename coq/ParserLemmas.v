Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.GeneralLemmas.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Import ListNotations.

(* Lemmas for unfolding / inverting calls to step and multistep *)

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

(* A well-formedness invariant for the parser stack *)

Inductive stack_wf (g : grammar) : parser_stack -> Prop :=
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

Inductive stack_derivation (g : grammar) : parser_stack -> list token -> Prop :=
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