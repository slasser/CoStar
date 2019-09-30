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

Definition parser_stack := (frame * list frame)%type.

Definition locStackOf (stk : parser_stack) : location_stack :=
  let (fr, frs) := stk in (fr.(loc), map loc frs).
  
Record parser_state    := Pst { avail  : NtSet.t
                              ; stack  : parser_stack     
                              ; tokens : list token
                              }.

Inductive error_type :=
| InvalidState    : error_type
| PredictionError : string -> error_type
| LeftRecursion   : nonterminal -> error_type.

Inductive step_result := StepAccept : forest -> step_result
                       | StepReject : string -> step_result
                       | StepK      : parser_state -> step_result
                       | StepError  : error_type -> step_result.

Inductive parse_result := Accept : forest -> parse_result
                        | Reject : string -> parse_result
                        | Error  : error_type -> parse_result.

Definition step (g : grammar) (st : parser_state) : step_result :=
  match st with
  | Pst av (fr, frs) ts =>
    match fr with
    | Fr (Loc xo pre suf) sv =>
      match suf with
      | [] => 
        match frs with
        (* empty stack --> accept *)
        | [] => 
          match ts with
          | []     => StepAccept sv
          | _ :: _ => StepReject "stack exhausted, tokens remain"
          end
        (* nonempty stack --> return to caller frame *)
        | (Fr (Loc xo_cr pre_cr suf_cr) sv_cr) :: frs_tl =>
          match suf_cr with
          | []                 => StepError InvalidState
          | T _ :: _           => StepError InvalidState
          | NT x :: suf_cr_tl => 
            let cr' := Fr (Loc xo_cr (pre_cr ++ [NT x]) suf_cr_tl)
                          (sv_cr ++ [Node x sv])
            in  StepK (Pst (NtSet.add x av) (cr', frs_tl) ts)
          end
        end
      (* terminal case --> consume a token *)
      | T a :: suf_tl =>
        match ts with
        | []               => StepReject "input exhausted"
        | (a', l) :: ts_tl =>
          if t_eq_dec a' a then 
            let fr' := Fr (Loc xo (pre ++ [T a]) suf_tl) (sv ++ [Leaf l])
            in  StepK (Pst (allNts g) (fr', frs) ts_tl)
          else
            StepReject "token mismatch"
        end
      (* nonterminal case --> push a frame onto the stack *)
      | NT x :: suf_tl => 
        if NtSet.mem x av then
          match llPredict g x (locStackOf (fr, frs)) ts with
          | PredSucc rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          (* maybe flip a bit indicating ambiguity? *)
          | PredAmbig rhs =>
            let callee := Fr (Loc (Some x) [] rhs) []
            in  StepK (Pst (NtSet.remove x av) (callee, fr :: frs) ts)
          | PredReject    => StepReject "prediction found no viable right-hand sides"
          | PredError msg => StepError (PredictionError msg)
          end
        else
          StepError (LeftRecursion x)
      end
    end
  end.

Definition meas (g : grammar) (st : parser_state) : nat * nat * nat :=
  match st with
  | Pst av stk ts =>
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (List.length ts, stackScore (locStackOf stk) (1 + m) e, stackHeight stk)
  end.

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
  destruct fr as [[xo pre suf] sv].
  destruct suf as [| [a | y] suf_tl].
  - (* return from the current frame *)
    destruct frs as [| caller frs_tl].
    + destruct ts; tc.
    + destruct caller as [[xo_cr pre_cr suf_cr] sv_cr].
      destruct suf_cr as [| [a | x] suf_cr_tl]; tc.
      inv Hs.
      eapply state_lt_after_return; simpl; eauto.
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
  | StepAccept sv    => fun _  => Accept sv
  | StepReject s     => fun _  => Reject s
  | StepError e      => fun _  => Error e
  | StepK st'        => fun Hs => multistep g st' (StepK_st_acc _ _ _ a Hs)
  end eq_refl.

Definition mkInitState (g : grammar) (gamma : list symbol) (ts : list token) : parser_state :=
  Pst (allNts g) (Fr (Loc None [] gamma) [], []) ts.

Definition parse (g : grammar) (gamma : list symbol) (ts : list token) : parse_result :=
  multistep g (mkInitState g gamma ts) (lex_nat_triple_wf _).