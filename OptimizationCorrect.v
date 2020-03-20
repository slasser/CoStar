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
        admit.
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
