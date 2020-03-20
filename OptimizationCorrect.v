Require Import GallStar.Lex.
Require Import GallStar.Parser_complete.
Require Import GallStar.Tactics.

Module OptimizationCorrectFn (Import D : Defs.T).

  Module Export PC := ParserCompleteFn D.
(*
(* need invariants about the closure map and cache *)
  Lemma multistep_equiv_multistep_opt' :
    forall g tri (a : Acc lex_nat_triple tri) cm ps ss ts av un ca a' r r',
      tri = meas g ss ts av
      -> multistep g ps ss ts av un a' = r
      -> multistep_opt g cm ps ss ts av un ca a' = r'
      -> r = r'.
  Proof.
    intros g tri a'.
    induction a' as [tri hlt IH].
    intros cm ps ss ts av un ca a r r' ? hm hm'.
    rewrite multistep_unfold.
    unfold multistep_opt.
 *)

  Lemma step_stepopt_equiv_acc :
    forall g cm ps ss ts av un ca v,
      step g ps ss ts av un = StepAccept v
      -> step_opt g cm ps ss ts av un ca = StepAccept_opt v.
  Proof.
    intros g cm ps ss ts av un ca v hs.
    unfold step_opt; unfold step in hs; dmeqs h; inv hs; tc.
  Qed.

  Lemma step_stepopt_equiv_error :
    forall g cm ps ss ts av un ca e,
      step_opt g cm ps ss ts av un ca = StepError_opt e
      -> step g ps ss ts av un = StepError e.
  Proof.
    intros. unfold step_opt in *; unfold step in *; dmeqs h; tc.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  
  Lemma step_stepopt_equiv_reject :
    forall g cm ps ss ts av un ca s,
      step g ps ss ts av un = StepReject s
      -> step_opt g cm ps ss ts av un ca = StepReject_opt s
         \/ exists ps' ss' ts' av' un' ca',
          step_opt g cm ps ss ts av un ca = StepK_opt ps' ss' ts' av' un' ca'.
  Proof.
    intros g cm ps ss ts av un ca v hs.
    unfold step_opt; unfold step in hs; dmeqs h; inv hs; tc; eauto 20.
    admit.
  Admitted.
  
  (* need invariants about the closure map and cache *)
  Lemma multistep_equiv_multistep_opt' :
    forall g tri (a : Acc lex_nat_triple tri) cm ps ss ts av un ca a',
      tri = meas g ss ts av
      -> multistep g ps ss ts av un a' = multistep_opt g cm ps ss ts av un ca a'.
  Proof.
    intros g tri a'.
    induction a' as [tri hlt IH].
    intros cm ps ss ts av un ca a ?; subst.
    destruct (multistep _ _ _ _ _ _ _) as [v | v | s | e] eqn:hm;
    destruct (multistep_opt _ _ _ _ _ _ _ _ _) as [v' | v' | s' | e'] eqn:hm'.
    - (* accept accept *)
      apply multistep_accept_cases in hm.
      apply multistep_opt_cases in hm'.
      destruct hm as [[hsa hu] | (? & ? & ? & ? & ? & ? & [hsk hm]) ];
      destruct hm' as [[hsa' hu'] | (? & ? & ? & ? & ? & ? & ? & [hsk' hm'])]. 
      + (* prove correspondence between step and step_opt *)
        eapply step_stepopt_equiv_acc in hsa; eauto.
        rewrite hsa in hsa'. inv hsa'. auto.
      + (* contradiction *)
        admit.
      + (* contradiction *)
        admit.
      + rewrite <- hm; rewrite <- hm'.
        (* prove a correspondence between the continuation values *)
        admit.
  Abort.
    
  (* need invariants about the closure map and cache *)
  Lemma multistep_equiv_multistep_opt :
    forall g cm ps ss ts av un ca a,
      multistep g ps ss ts av un a = multistep_opt g cm ps ss ts av un ca a.
  Proof.
  Abort.
  
  Theorem parse_equiv_parse_opt :
    forall g ys ts,
      parse g ys ts = parse_opt g ys ts.
  Proof.
    intros g ys ts; unfold parse; unfold parse_opt.
  Abort.    
