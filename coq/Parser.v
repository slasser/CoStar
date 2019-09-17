Require Import FMaps Omega PeanoNat String. 
Require Import GallStar.Defs.
Require Import GallStar.Lex.
Require Import GallStar.Prediction.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Import ListNotations.
Open Scope list_scope.

Record frame := Fr { loc : location
                   ; sem : forest
                   }.                               

Definition p_stack := (frame * list frame)%type.

Definition locStackOf (stk : p_stack) : location_stack :=
  let (fr, frs) := stk in (fr.(loc), map loc frs).
  
Record parser_state    := Pst { avail  : NtSet.t
                              ; stack  : p_stack               
                              ; tokens : list token
                              }.

Inductive step_result := StepAccept : forest -> list token -> step_result
                       | StepReject : string -> step_result
                       | StepK      : parser_state -> step_result
                       | StepError  : string -> step_result.

Inductive parse_result := Accept : forest -> list token -> parse_result
                        | Reject : string -> parse_result
                        | Error  : string -> parse_result.

Definition step (g : grammar) (st : parser_state) : step_result :=
  match st with
  | Pst av (fr, frs) ts =>
    match fr with
    | Fr (Loc x pre suf) sv =>
      match suf with
      | [] => 
        match frs with
        | [] => StepAccept sv ts
        | (Fr (Loc x_cr pre_cr suf_cr) sv_cr) :: frs_tl =>
          match suf_cr with
          | []                 => StepError "impossible"
          | T _ :: _           => StepError "impossible"
          | NT x' :: suf_cr_tl => 
            let cr' := Fr (Loc x_cr (pre_cr ++ [NT x]) suf_cr_tl)
                          (sv_cr ++ [Node x sv])
            in  StepK (Pst (NtSet.add x av) (cr', frs_tl) ts)
          end
        end
      | T a :: suf_tl =>
        match ts with
        | []               => StepReject "input exhausted"
        | (a', l) :: ts_tl =>
          if t_eq_dec a' a then 
            let fr' := Fr (Loc x (pre ++ [T a]) suf_tl) (sv ++ [Leaf l])
            in  StepK (Pst (allNts g) (fr', frs) ts_tl)
          else
            StepReject "token mismatch"
        end
      | NT x :: suf_tl => 
        if NtSet.mem x av then
          match llPredict g x (locStackOf (fr, frs)) ts with
          | PredSucc rhs =>
            let callee := Fr (Loc x [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          (* maybe flip a bit indicating ambiguity? *)
          | PredAmbig rhs =>
            let callee := Fr (Loc x [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          | PredReject    => StepReject "prediction found no viable right-hand sides"
          | PredError msg => StepError msg
          end
        else
          StepError "left recursion detected"
      end
    end
  end.

(*Definition headFrameSize (fr : parser_frame) : nat :=
  List.length fr.(syms).

Definition headFrameScore (fr : parser_frame) (b : nat) (e : nat) : nat :=
  headFrameSize fr * (b ^ e).

Definition tailFrameSize (fr : parser_frame) : nat :=
  match fr.(syms) with
  | [] => 0
  | _ :: syms' => List.length syms'
  end.

Definition tailFrameScore (fr : parser_frame) (b : nat) (e : nat) : nat :=
  tailFrameSize fr * (b ^ e).

Fixpoint tailFramesScore (frs : list parser_frame) (b : nat) (e : nat) : nat :=
  match frs with
  | [] => 0
  | fr :: frs' => tailFrameScore fr b e + tailFramesScore frs' b (1 + e)
  end.

Definition stackScore (stk : parser_stack) (b : nat) (e : nat) : nat :=
  let (hf, tfs) := stk
  in  headFrameScore hf b e + tailFramesScore tfs b (1 + e).

Definition stackHeight (stk : parser_stack) : nat :=
  let (_, frs) := stk in List.length frs.
 *)

Definition meas (g : grammar) (st : parser_state) : nat * nat * nat :=
  match st with
  | Pst av stk ts =>
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (List.length ts, stackScore (locStackOf stk) (1 + m) e, stackHeight stk)
  end.

(*
Lemma meas_unfold : 
  forall st tbl, meas st tbl = (List.length st.(tokens), 
                                stackScore st.(stack) (1 + maxEntryLength tbl) (NtSet.cardinal st.(avail)),
                                stackHeight st.(stack)).
Proof. 
  auto.
Qed.
 *)

(*
Definition nat_triple_lex : relation (nat * nat * nat) :=
  triple_lex nat nat nat lt lt lt.

Lemma headFrameScore_nil :
  forall fr b e,
    fr.(syms) = [] -> headFrameScore fr b e = 0.
Proof.
  intros fr b e Hfr.
  unfold headFrameScore. unfold headFrameSize.
rewrite Hfr; auto.
Qed.

Lemma tailFrameScore_cons :
  forall fr sym gamma b e,
    fr.(syms) = sym :: gamma -> tailFrameScore fr b e = List.length gamma * (b ^ e).
Proof.
  intros fr sym gamma b e Hfr.
  unfold tailFrameScore. unfold tailFrameSize.
  rewrite Hfr; auto.
Qed.

Lemma stackScore_head_frame_nil :
  forall fr frs b e, 
    fr.(syms) = [] 
    -> stackScore (fr, frs) b e = tailFramesScore frs b (1 + e).
Proof.
  intros fr frs b e Hfr.  
  unfold stackScore. unfold headFrameScore. unfold headFrameSize.
  rewrite Hfr; simpl; auto.
Qed.

Lemma stackScore_pre_return :
  forall fr fr' sym gamma frs b e, 
    fr.(syms) = nil
    -> fr'.(syms) = sym :: gamma
    -> stackScore (fr, fr' :: frs) b e = 
       (List.length gamma * b ^ (1 + e)) + tailFramesScore frs b (2 + e).
Proof.
  intros fr fr' sym gamma frs b e Hfr Hfr'.
  rewrite stackScore_head_frame_nil; auto.
  simpl.
  erewrite tailFrameScore_cons; eauto.
Qed.

Lemma post_return_state_lt_pre_return_state :
  forall st st' ts callee caller caller' frs x gamma av tbl,
    st = parserState av (callee, caller :: frs) ts
    -> st' = parserState (NtSet.add x av) (caller', frs) ts
    -> callee.(syms) = []
    -> caller.(syms) = NT x :: gamma
    -> caller'.(syms) = gamma
    -> nat_triple_lex (meas st' tbl) (meas st tbl).
Proof.
  intros st st' ts callee caller caller' frs x gamma av tbl Hst Hst' Hnil Hcons Htl; subst.
  unfold meas; simpl.
  rewrite headFrameScore_nil with (fr := callee); simpl; auto.
  erewrite tailFrameScore_cons; eauto.
  unfold headFrameScore. unfold headFrameSize.
  destruct (NtSet.mem x av) eqn:Hm.
  - (* x is already in av, so the cardinality stays the same *)
    rewrite add_cardinal_1; auto.
    pose proof nonzero_exponents_lt_stackScore_le as Hle. 
    specialize (Hle (List.length caller'.(syms))
                  (S (maxEntryLength tbl)) 
                  (NtSet.cardinal av)
                  (S (NtSet.cardinal av))
                  (S (NtSet.cardinal av))
                  (S (S (NtSet.cardinal av)))
                  frs).
    apply le_lt_or_eq in Hle.
    + destruct Hle as [Hlt | Heq]; subst.
      * apply triple_snd_lt; auto.
      * rewrite Heq.
        apply triple_thd_lt; auto.
    + split; auto.
      eapply mem_true_cardinality_gt_0; eauto.
    + split; auto.
      omega.
  - (* x isn't in av, so the cardinality increase by 1 *)
    rewrite add_cardinal_2; auto.
    apply triple_thd_lt; auto.
Qed.

Lemma gamma_in_table_length_in_entryLengths :
  forall k gamma tbl,
    In (k, gamma) (ParseTable.elements tbl)
    -> In (List.length gamma) (entryLengths tbl).
Proof.
  intros k gamma tbl Hin.
  unfold entryLengths.
  induction (ParseTable.elements tbl) as [| (k', gamma') prs IH]; inv Hin; simpl in *.
  - inv H; auto.
  - apply IH in H; auto.
Qed.

Module Export PF := WFacts ParseTable.

Lemma pt_findA_In :
  forall (k : ParseTable.key) (gamma : list symbol) (l : list (ParseTable.key * list symbol)),
    findA (PF.eqb k) l = Some gamma
    -> In (k, gamma) l.
Proof.
  intros.
  induction l.
  - inv H.
  - simpl in *.
    destruct a as (k', gamma').
    destruct (PF.eqb k k') eqn:Heq.
    + inv H.
      unfold PF.eqb in *.
      destruct (PF.eq_dec k k').
      * subst; auto.
      * inv Heq.
    + right; auto.
Qed.

Lemma find_Some_gamma_in_table :
  forall k (gamma : list symbol) tbl,
    ParseTable.find k tbl = Some gamma -> In (k, gamma) (ParseTable.elements tbl).
  intros k gamma tbl Hf.
  rewrite elements_o in Hf.
  apply pt_findA_In in Hf; auto.
Qed.

Lemma tbl_lookup_result_le_max :
  forall k tbl gamma,
    ParseTable.find k tbl = Some gamma
    -> List.length gamma <= maxEntryLength tbl.
Proof.
  intros k tbl gamma Hf.
  unfold maxEntryLength.
  apply list_element_le_listMax.
  apply gamma_in_table_length_in_entryLengths with (k := k).
  apply find_Some_gamma_in_table; auto.
Qed.  

Lemma tbl_lookup_result_lt_max_plus_1 :
  forall k tbl gamma,
    ParseTable.find k tbl = Some gamma
    -> List.length gamma < 1 + maxEntryLength tbl.
Proof.
  intros k tbl gamma Hf.
  apply (tbl_lookup_result_le_max k tbl gamma) in Hf; omega.
Qed.

Lemma post_push_state_lt_pre_push_st :
  forall st st' ts callee caller frs x gamma_caller gamma_callee av tbl,
    st = parserState av (caller, frs) ts
    -> st' = parserState (NtSet.remove x av) (callee, caller :: frs) ts
    -> caller.(syms) = NT x :: gamma_caller
    -> callee.(syms)  = gamma_callee
    -> ParseTable.find (x, peek ts) tbl = Some gamma_callee
    -> NtSet.mem x av = true
    -> nat_triple_lex (meas st' tbl) (meas st tbl).
Proof.
  intros st st' ts callee caller frs x gamma_caller gamma_callee av tbl Hst Hst' Hcaller Hcallee Hfind Hmem; subst.
  apply triple_snd_lt; simpl.
  rewrite remove_cardinal_1; auto.
  unfold headFrameScore. unfold headFrameSize.
  unfold tailFrameScore. unfold tailFrameSize. rewrite Hcaller.
  simpl.
rewrite plus_assoc. 
apply plus_lt_compat_r.
apply plus_lt_compat_r.
assert (remove_cardinal_minus_1 : forall x s,
           NtSet.mem x s = true
           -> NtSet.cardinal (NtSet.remove x s) = 
              NtSet.cardinal s - 1).
       
{ intros x' s Hm.
  replace (NtSet.cardinal s) with (S (NtSet.cardinal (NtSet.remove x' s))).
  - omega.
  - apply remove_cardinal_1; auto. }
rewrite remove_cardinal_minus_1; auto.
apply less_significant_value_lt_more_significant_digit.
  - eapply tbl_lookup_result_lt_max_plus_1; eauto.
  - erewrite <- remove_cardinal_1; eauto. 
    omega.
Qed.

Lemma step_meas_lt :
  forall tbl st st',
    step tbl st = StepK st'
    -> nat_triple_lex (meas st' tbl) (meas st tbl).
Proof.
  intros tbl st st' Hs.
  unfold step in Hs.
  destruct st as [av [fr frs] ts].
  destruct fr as [gamma sv].
  destruct gamma as [| [y | x] gamma'].
  - (* return from the current frame *)
    destruct frs as [| caller frs']; try congruence.
    destruct caller as [gamma_caller sv_caller]. 
    destruct gamma_caller as [| [y | x] gamma_caller']; try congruence.
    inv Hs.
    eapply post_return_state_lt_pre_return_state; simpl; eauto.
    simpl; auto.
  - (* terminal case *) 
    destruct ts as [| (y', l) ts']; try congruence.
    destruct (t_eq_dec y' y); try congruence.
    inv Hs.
    apply triple_fst_lt; simpl; auto.
  - (* nonterminal case -- push a new frame onto the stack *)
    destruct (NtSet.mem x av) eqn:Hm; try congruence.
    destruct (ParseTable.find (x, peek ts) tbl) as [gamma |] eqn:Hf; try congruence.
    inv Hs.
    eapply post_push_state_lt_pre_push_st; eauto.
    simpl; eauto.
Qed.
 *)

Lemma state_lt_after_return :
  forall g st st' ts callee caller caller' frs x x' suf_cr_tl av,
    st = Pst av (callee, caller :: frs) ts
    -> st' = Pst (NtSet.add x av) (caller', frs) ts
    -> callee.(loc).(rsuf)  = []
    -> caller.(loc).(rsuf)  = NT x' :: suf_cr_tl
    -> caller'.(loc).(rsuf) = suf_cr_tl
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' ts ce cr cr' frs x x' suf_cr_tl av
         Hst hst' Hce Hcr Hcr'; subst.
  unfold meas. unfold locStackOf.
  pose proof (stackScore_le_after_return (loc ce) (loc cr) (loc cr')
                                         x x' (rsuf (loc cr')) av (map loc frs)
                                         (1 + maxRhsLength g)) as Hle.
  apply le_lt_or_eq in Hle; auto; destruct Hle as [Hlt | Heq].
  - apply triple_snd_lt; auto.
  - rewrite Heq; apply triple_thd_lt; auto.
Defined.

Lemma state_lt_after_push :
  forall g st st' ts callee caller frs x suf_tl gamma av,
    st = Pst av (caller, frs) ts
    -> st' = Pst (NtSet.remove x av) (callee, caller :: frs) ts
    -> caller.(loc).(rsuf) = NT x :: suf_tl
    -> callee.(loc).(rsuf) = gamma
    -> In gamma (rhssForNt g x)
    -> NtSet.In x av
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' ts ce cr frs x suf_tl gamma av
         Hst Hst' Hcr Hce Hi Hm; subst.
  apply triple_snd_lt.
  eapply stackScore_lt_after_push; eauto.
Defined.

Lemma PredSucc_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredSucc gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma Hf.
  eapply PredSucc_result_in_rhssForNt; eauto.
Defined.

Lemma PredAmbig_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredAmbig gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma.
  eapply PredAmbig_result_in_rhssForNt; eauto.
Defined.

Lemma step_meas_lt :
  forall g st st',
    step g st = StepK st'
    -> lex_nat_triple (meas g st') (meas g st).
Proof.
  intros g st st' Hs.
  unfold step in Hs.
  destruct st as [av [fr frs] ts].
  destruct fr as [[x pre suf] sv].
  destruct suf as [| [a | y] suf_tl].
  - (* return from the current frame *)
    destruct frs as [| caller frs_tl]; tc.
    destruct caller as [[x_cr pre_cr suf_cr] sv_cr].
    destruct suf_cr as [| [a | x'] suf_cr_tl]; tc.
    inv Hs.
    eapply state_lt_after_return with (x' := x'); simpl; eauto.
    simpl; auto.
  - (* terminal case *) 
    destruct ts as [| (a', l) ts_tl]; tc.
    destruct (t_eq_dec a' a); tc; subst.
    inv Hs.
    apply triple_fst_lt; simpl; auto.
  - (* nonterminal case -- push a new frame onto the stack *)
    destruct (NtSet.mem y av) eqn:Hm; tc.
    apply NtSet.mem_spec in Hm.
    destruct (llPredict g y _ ts) as [gamma|gamma| |msg] eqn:Hp; tc.
    + inv Hs.
      apply PredSucc_result_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
    + inv Hs.
      apply PredAmbig_result_in_rhssForNt in Hp.
      eapply state_lt_after_push; eauto.
      simpl; auto.
Defined.

Lemma StepK_st_acc :
  forall g st st' (a : Acc lex_nat_triple (meas g st)),
    step g st = StepK st' -> Acc lex_nat_triple (meas g st').
Proof.
  intros g st st' a Hs.
  eapply Acc_inv; eauto.
  apply step_meas_lt; auto.
Defined.

Fixpoint multistep (g  : grammar) 
                   (st : parser_state)
                   (a  : Acc lex_nat_triple (meas g st)) :
                   parse_result :=
  match step g st as res return step g st = res -> _ with
  | StepAccept sv ts => fun _  => Accept sv ts
  | StepReject s     => fun _  => Reject s
  | StepError s      => fun _  => Error s
  | StepK st'        => fun Hs => multistep g st' (StepK_st_acc _ _ _ a Hs)
  end eq_refl.