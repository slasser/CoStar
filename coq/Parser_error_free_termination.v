Require Import List.
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Parser.
Require Import GallStar.Tactics.
Import ListNotations.

(* The parser never reaches an invalid state;
   i.e., impossible states really are impossible *)

Lemma stack_wf_no_invalid_state :
  forall (g : grammar)
         (av : NtSet.t)
         (stk : parser_stack)
         (ts : list token),
    stack_wf g stk
    -> ~ step g (Pst av stk ts) = StepError InvalidState.
Proof.
  intros g av stk ts hwf; unfold not; intros hs.
  unfold step in hs.
  dms; tc; try inv hwf.
Qed.

Lemma multistep_never_reaches_error_state :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (ts     : list token)
         (av     : NtSet.t)
         (stk    : parser_stack)
         (a'     : Acc lex_nat_triple (Parser.meas g (Pst av stk ts))),
    tri = Parser.meas g (Pst av stk ts)
    -> stack_wf g stk
    -> ~ multistep g (Pst av stk ts) a' = Error InvalidState.
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros ts av stk a' heq hwf; unfold not; intros hm; subst.
  apply multistep_invalid_state_cases in hm.
  destruct hm as [hs | hm].
  - eapply stack_wf_no_invalid_state; eauto. 
  - destruct hm as [[av' stk' ts'] [a'' [hs hm]]].
    eapply IH in hm; eauto.
    + apply step_meas_lt; auto.
    + eapply step_preserves_stack_wf_invar; eauto.
Qed.

Lemma parser_never_reaches_invalid_state :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token),
    ~ parse g ss ts = Error InvalidState.
Proof.
  intros g ss ts; unfold not; intros hp.
  unfold parse in hp.
  apply multistep_never_reaches_error_state
    with (tri := Parser.meas g (mkInitState g ss ts)) in hp; auto.
  apply lex_nat_triple_wf.
Qed.


(* TODO -- The parser only returns a LeftRecursion error
   if the grammar is left-recursive *)

Inductive nullable_gamma' (g : grammar) : list symbol -> Prop :=
| NullableNil'  : 
    nullable_gamma' g []
| NullableCons' : 
    forall x ys tl,
      In (x, ys) g
      -> nullable_gamma' g ys
      -> nullable_gamma' g tl
      -> nullable_gamma' g (NT x :: tl).

Inductive nullable_path (g : grammar) :
  symbol -> symbol -> Prop :=
| DirectPath : forall x z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT z :: suf
    -> nullable_gamma g pre
    -> nullable_path g (NT x) (NT z)
| IndirectPath : forall x y z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT y :: suf
    -> nullable_gamma g pre
    -> nullable_path g (NT y) (NT z)
    -> nullable_path g (NT x) (NT z).

Inductive path (g : grammar) :
  symbol -> symbol -> Prop :=
| DirectPath' : forall x z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT z :: suf
    -> path g (NT x) (NT z)
| IndirectPath' : forall x y z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT y :: suf
    -> path g (NT y) (NT z)
    -> path g (NT x) (NT z).

Hint Constructors nullable_path.

Definition left_recursive g sym :=
  nullable_path g sym sym.

Definition no_left_recursion g :=
  forall (x : nonterminal),
    ~ left_recursive g (NT x).

Inductive nullable_frames_path (g : grammar) : nonterminal -> nonterminal -> list frame -> Prop :=
| NFP : 
    forall top_fr mid_frs bot_fr x y suf suf',
      bot_fr.(loc).(rsuf) = NT x :: suf
      -> List.Forall (fun mf => nullable_gamma g mf.(loc).(rpre)) mid_frs
      -> nullable_gamma g top_fr.(loc).(rpre)
      -> top_fr.(loc).(rsuf) = NT y :: suf'
      -> nullable_frames_path g x y (top_fr :: mid_frs ++ [bot_fr]).
(*
Lemma multistep_left_recursion_detection_sound :
  forall (g : grammar)
         (tri : nat * nat * nat)
         (a : Acc lex_nat_triple tri)
         (av : NtSet.t) 
         fr frs
         (ts : list token)
         (a' : Acc lex_nat_triple (meas g (Pst av (fr, frs) ts)))
         (x : nonterminal),
    stack_wf g (fr, frs)
    -> tri = meas g (Pst av (fr, frs) ts)
    -> multistep g (Pst av (fr, frs) ts) a' = Error (LeftRecursion x)
    -> (~ NtSet.In x av
        /\ (exists pre s suf,
               fr.(loc).(rpre) ++ fr.(loc).(rsuf) = pre ++ s :: suf
               /\ nullable_gamma g pre
               /\ (s = NT x \/ nullable_path g s (NT x))))
       \/ left_recursive g (NT x).
Proof.
  intros g tri a'.
  induction a' as [tri hlt IH].
  intros av fr frs ts a x hw heq hm; subst.
  apply multistep_left_recursion_cases in hm.
  destruct hm as [hs | hm].
  - admit.
  - destruct hm as [[av' (fr', frs') ts'] [a'' [hs hm]]].
    eapply IH in hm; clear IH; clear hlt; auto.
    + destruct hm as [hnin | hlr]; auto.
      clear a a''.
      destruct hnin as [hnin [pre [s [suf [heq [hng hor]]]]]]; subst.
      destruct hor as [heq' | hnp]; subst.
      * unfold step in hs; repeat dmeq heq; tc; inv hs; subst; sis.
        -- rewrite <- app_assoc in heq.
           simpl in *.
           inv hw.
           destruct (NF.eq_dec x n); subst.
           ++ ND.fsetdec.
           ++ left. split.
              ** ND.fsetdec.
              ** rewrite app_nil_r in *.
Abort.           

Lemma multistep_left_recursion_detection_sound :
  forall (g : grammar)
         (tri : nat * nat * nat)
         (a : Acc lex_nat_triple tri)
         (av : NtSet.t) 
         fr frs
         (ts : list token)
         (a' : Acc lex_nat_triple (meas g (Pst av (fr, frs) ts)))
         (x : nonterminal),
    tri = meas g (Pst av (fr, frs) ts)
    -> multistep g (Pst av (fr, frs) ts) a' = Error (LeftRecursion x)
    -> (exists fr' pre s suf,
           In fr' (fr :: frs)
           /\ fr'.(loc).(rsuf) = pre ++ s :: suf
           /\ ~ NtSet.In x av
           /\ (s = NT x
               \/ nullable_path g s (NT x)))
       \/ left_recursive g (NT x).
Proof.
  intros g tri a'.
  induction a' as [tri hlt IH].
  intros av fr frs ts a x heq hm; subst.
  apply multistep_left_recursion_cases in hm.
  destruct hm as [hs | hm].
  - admit.
  - destruct hm as [[av' (fr', frs') ts'] [a'' [hs hm]]].
    eapply IH in hm; clear IH; clear hlt; eauto.
    + destruct hm as [hex | hlr]; auto.
      destruct hex as [fr'' [pre [s [suf [hin [heq [hnin hor]]]]]]].
      destruct hor as [heq' | hnp]; subst.
      * destruct hin as [hh | ht]; subst.
Abort.


Lemma multistep_left_recursion_detection_sound :
  forall g av stk ts a x,
    multistep g (Pst av stk ts) a = Error (LeftRecursion x)
    -> (In x (lhss g) /\ ~ NtSet.In x av)
       \/ left_recursive g (NT x).
Admitted.
 *)



Lemma multistep_left_recursion_detection_sound :
  forall (g      : grammar)
         (tri    : nat * nat * nat)
         (a      : Acc lex_nat_triple tri)
         (st     : parser_state)
         (a'     : Acc lex_nat_triple (meas g st))
         (x      : nonterminal),
    tri = meas g st
    -> stack_wf g st.(stack)
    -> unavailable_nts_are_open_calls_invar g st
    -> multistep g st a' = Error (LeftRecursion x)
    -> left_recursive g (NT x).
Proof.
  intros g tri a.
  induction a as [tri hlt IH].
  intros st a' x heq hw hu hm; subst.
  apply multistep_left_recursion_cases in hm.
  destruct hm as [hs | [st' [a'' [hs hm]]]].
  - clear IH.
    destruct st as [av (fr, frs) ts].
    apply step_LeftRecursion_facts in hs.
    destruct hs as [hnin [suf heq]]; subst.
    unfold unavailable_nts_are_open_calls_invar in hu.
    unfold nt_unavailable in hu.
    (* I'll need to change the definition of allNts
       so that it includes right-hand nonterminals *)
    assert (hand : In x (lhss g) /\ ~ NtSet.In x av) by admit.
    apply hu in hand; clear hu.
    destruct hand as [hng [frs_pre [fr_cr [frs_suf [suf_cr [heq' [hp heq'']]]]]]]; subst.
    simpl in hw.
    (* Next prove that fr :: frs_pre ++ fr_cr is well-formed
       Then prove that there's a nullable path from x to x. 
       Change the wf definition so it's over lists.
       That will let you prove that it holds of sublists. *)
    admit.
  - eapply IH with (y := meas g st'); eauto.
    + eapply step_meas_lt; eauto.
    + (* redefine invariants to get rid of these destructs *)
      destruct st; destruct st'.
      eapply step_preserves_stack_wf_invar; eauto.
    + eapply step_preserves_unavailable_nts_invar; eauto.
Admitted.

Lemma parse_left_recursion_detection_sound :
  forall g ss ts x,
    parse g ss ts = Error (LeftRecursion x)
    -> left_recursive g (NT x).
Proof.
  intros g ss ts x hp; unfold parse in hp.
  eapply multistep_left_recursion_detection_sound in hp; eauto.
  - apply lex_nat_triple_wf.
  - (* lemma? *)
    constructor.
  - (* lemma *)
    unfold mkInitState.
    unfold unavailable_nts_are_open_calls_invar; simpl.
    intros x' hu.
    exfalso.
    eapply all_nts_available_no_nt_unavailable; eauto.
Qed.
  
Lemma parser_doesn't_find_left_recursion_in_non_left_recursive_grammar :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token)
         (x  : nonterminal),
    no_left_recursion g
    -> ~ parse g ss ts = Error (LeftRecursion x).
Proof.
  intros g ss ts x hn; unfold not; intros hp.
  apply parse_left_recursion_detection_sound in hp; firstorder.
Qed.

Theorem parser_terminates_without_error :
  forall (g  : grammar)
         (ss : list symbol)
         (ts : list token)
         (e  : error_type),
    no_left_recursion g
    -> ~ parse g ss ts = Error e.
Proof.
  intros g ss ts e; unfold not; intros hp.
  destruct e.
  - (* invalid state case *)
    eapply parser_never_reaches_invalid_state; eauto.
  - (* prediction error case *)
    admit.
  - (* left recursion case *)
    apply parser_doesn't_find_left_recursion_in_non_left_recursive_grammar; auto.
Admitted.