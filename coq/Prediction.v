Require Import Arith List Omega PeanoNat Program.Wf String.
Require Import Defs.
Require Import Lemmas.
Require Import Lex.
Require Import Tactics.
Require Import Termination.
Import ListNotations.

Record subparser := Sp { avail      : NtSet.t
                       ; prediction : list symbol
                       ; stack      : l_stack
                       }.

Inductive subparser_move_result :=
| SpMoveSucc   : subparser -> subparser_move_result
| SpMoveDieOff : subparser_move_result
| SpMoveError  : subparser_move_result.

Definition moveSp (tok : token) (sp : subparser) : subparser_move_result :=
  match sp with
  | Sp _ pred stk =>
    match stk with
    (* Subparser is in a final configuration, but an input token remains *)
    | ((_, _, []), []) => SpMoveDieOff
    (* Impossible if the previous call was a closure *)
    | ((_, _, []), _ :: _) => SpMoveError
    (* Impossible if the previous call was a closure *)
    | ((_, _, NT _ :: _), _) => SpMoveError
    | ((x, pre, T a :: suf), locs) =>
      match tok with
      | (a', _) =>
        if t_eq_dec a' a then
          SpMoveSucc (Sp NtSet.empty pred ((x, pre ++ [T a], suf), locs))
        else
          (* token mismatch *)
          SpMoveDieOff
      end
    end
  end.

Inductive move_result :=
| MoveSucc   : list subparser -> move_result
| MoveError  : move_result.

Fixpoint spsAfterMoveOrError (rs : list subparser_move_result) : move_result :=
  match rs with
  | []       => MoveSucc []
  | r :: rs' =>
    match spsAfterMoveOrError rs' with
    | MoveSucc sps =>
      match r with
      | SpMoveSucc sp => MoveSucc (sp :: sps)
      | SpMoveDieOff  => MoveSucc sps
      | SpMoveError   => MoveError
      end
    | MoveError => MoveError
    end
  end.

Definition move (tok : token) (sps : list subparser) : move_result :=
  let rs := map (moveSp tok) sps
  in  spsAfterMoveOrError rs.

Definition meas (g : grammar) (sp : subparser) : nat * nat :=
  match sp with
  | Sp av _ stk =>
    let m := maxRhsLength g in
    let e := NtSet.cardinal av in
    (stackScore stk (1 + m) e, stackHeight stk)
  end.

Inductive sp_closure_step_result :=
| ScsDone  : subparser -> sp_closure_step_result
| ScsCont  : list subparser -> sp_closure_step_result
| ScsError : sp_closure_step_result.

Definition spClosureStep (g : grammar) (sp : subparser) : sp_closure_step_result :=
  match sp with
  | Sp av pred stk =>
    match stk with
    | (fr, frs) =>
      match fr with
      | (x, _, []) =>
        match frs with
        | []              => ScsDone sp
        | caller :: frs' =>
          match caller with
          | (x_caller, pre_caller, suf_caller) =>
            match suf_caller with
            | []                   => ScsError
            | T _ :: _             => ScsError
            | NT x' :: suf_caller' =>
                if nt_eq_dec x' x then
                  let stk' := ((x_caller, pre_caller ++ [NT x], suf_caller'), frs') in
                  let sp' := Sp (NtSet.add x av) pred stk'
                  in  ScsCont [sp']
                else
                  ScsError
              end
            end
          end
        | (_, _, T _ :: _)     => ScsDone sp
        | (_, _, NT y :: suf') =>
          if NtSet.mem y av then
            let rhss  := rhssForNt g y in
            let stks' := map (fun rhs => ((y, [], rhs), fr :: frs)) rhss in
            let sps'  := map (fun stk => Sp (NtSet.remove y av) pred stk) stks' 
            in  ScsCont sps'
          else
            ScsError
      end
    end
  end.

Inductive closure_step_result :=
| CsSucc  : subparser -> closure_step_result
| CsError : closure_step_result.

Definition flat_map' {A B : Type} :
  forall (l : list A) (f : forall x, In x l -> list B), list B.
  refine(fix fm (l : list A) (f : forall x, In x l -> list B) :=
         match l as l' return l = l' -> _ with
         | []     => fun _ => []
         | h :: t => fun Heq => (f h _) ++ (fm t _)
         end eq_refl).
  - subst.
    apply in_eq.
  - subst; intros x Hin.
    assert (Ht : In x (h :: t)).
    { apply in_cons; auto. }
    eapply f; eauto.
Defined.

Definition map' {A B : Type} :
  forall (l : list A) (f : forall x, In x l -> B), list B.
  refine(fix m (l : list A) (f : forall x, In x l -> B) :=
         match l as l' return l = l' -> _ with
         | []     => fun _ => []
         | h :: t => fun Heq => (f h _) :: (m t _)
         end eq_refl).
  - subst.
    apply in_eq.
  - subst; intros x Hin.
    assert (Ht : In x (h :: t)).
    { apply in_cons; auto. }
    eapply f; eauto.
Defined.

(* Here's what didn't work--the fact that the recursive call argument
   is in spps does not appear in the context *)
Program Fixpoint spClosure (g : grammar) (sp : subparser)
                           {measure (meas g sp) (lex_nat_pair)} :
                           list closure_step_result :=
  match spClosureStep g sp with
  | ScsDone sp => [CsSucc sp]
  | ScsError   => [CsError]
  | ScsCont spps => flat_map (fun spp => spClosure g spp) spps
  end.
Next Obligation.
Abort.

Lemma subparser_lt_after_return :
  forall g sp sp' av pred callee caller caller' frs x gamma,
    sp = Sp av pred (callee, caller :: frs)
    -> sp' = Sp (NtSet.add x av) pred (caller', frs)
    -> symbolsToProcess callee  = []
    -> symbolsToProcess caller  = NT x :: gamma
    -> symbolsToProcess caller' = gamma
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' av pred callee caller caller' frs x gamma
         Hsp Hsp' Hcallee Hcaller Hcaller'; subst.
  unfold meas.
  pose proof (stackScore_le_after_return callee caller caller'
                                         x av frs (1 + maxRhsLength g)) as Hle.
  apply le_lt_or_eq in Hle; auto; destruct Hle as [Hlt | Heq].
  - apply pair_fst_lt; auto.
  - rewrite Heq; apply pair_snd_lt; auto.
Defined.

Lemma subparser_lt_after_push :
  forall g sp sp' av pred caller callee frs x y pre suf' rhs,
    sp = Sp av pred (caller, frs)
    -> sp' = Sp (NtSet.remove y av) pred (callee, caller :: frs)
    -> caller = (x, pre, NT y :: suf')
    -> callee = (y, [], rhs)
    ->  NtSet.mem y av = true
    -> In rhs (rhssForNt g y)
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' av pred caller callee frs x y pre suf' rhs
         Hsp Hsp' Hcaller Hcallee Hmem Hin; subst.
  unfold meas.
  apply pair_fst_lt.
  eapply stackScore_lt_after_push; simpl; eauto.
Defined.
  
Lemma subparser_lt_after_step :
  forall g sp sp' sps',
    spClosureStep g sp = ScsCont sps'
    -> In sp' sps'
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' sps' Hstep Hin.
  unfold spClosureStep in Hstep.
  destruct sp as [av pred stk].
  destruct stk as (((x, pre), suf), frs).
  destruct suf as [| sym suf'].
  - destruct frs as [| caller frs']; tc.
    destruct caller as ((x_caller, pre_caller), suf_caller).
    destruct suf_caller as [| [a | x'] suf_caller']; tc.
    destruct (nt_eq_dec x' x); tc; subst.
    inv Hstep.
    apply in_singleton_eq in Hin; subst.
    eapply subparser_lt_after_return; eauto.
    simpl; auto.
  - destruct sym as [a | y]; tc.
    destruct (NtSet.mem y av) eqn:Hmem; tc.
    inv Hstep.
    eapply in_map_iff in Hin.
    destruct Hin as [stk [Heq Hin]]; subst.
    eapply in_map_iff in Hin.
    destruct Hin as [suf [Heq Hin]]; subst.
    eapply subparser_lt_after_push; eauto.
Defined.

(* This does work -- note the alternative flat_map implementation *)
Program Fixpoint spClosure (g : grammar)
                           (sp : subparser)
                           {measure (meas g sp) (lex_nat_pair)} :
                           list closure_step_result :=
  match spClosureStep g sp with
  | ScsDone sp => [CsSucc sp]
  | ScsError   => [CsError]
  | ScsCont spps => flat_map' spps (fun spp Hin => spClosure g spp)
  end.
Next Obligation.
  eapply subparser_lt_after_step; eauto.
Defined.
Next Obligation.
  apply measure_wf.
  apply pair_lex_wf; apply lt_wf.
Defined.

(* Next steps : try to define closure with a single function, implement the main prediction loop *)

Lemma acc_after_return :
  forall (g  : grammar)
         (sp : subparser)
         (av : NtSet.t)
         (pred pre pre' suf_tl : list symbol)
         (callee : l_frame)
         (frs frs_tl : list l_frame)
         (x y y' : nonterminal)
         (stk' : l_stack),
    Acc lex_nat_pair (meas g sp)
    -> sp = Sp av pred (callee, frs)
    -> callee = (y', pre', [])
    -> frs  = (x, pre, NT y :: suf_tl) :: frs_tl
    -> stk' = ((x, pre ++ [NT y], suf_tl), frs_tl)
    -> Acc lex_nat_pair (meas g (Sp (NtSet.add y av) pred stk')).
Proof.
  intros g sp av pred pre pre' suf_tl callee frs fr_tl x y y' stk'
         Hac Hsp hce Hfrs Hstk'; subst.
  eapply Acc_inv; eauto.
  eapply subparser_lt_after_return; eauto.
  simpl; auto.
Defined.

Lemma acc_after_push :
  forall (g : grammar)
         (sp sp' : subparser)
         (av : NtSet.t)
         (pred pre suf_tl : list symbol)
         (fr : l_frame)
         (frs : list l_frame)
         (x y : nonterminal)
         (sps' : list subparser)
         (pushRhs : list symbol -> subparser),
    Acc lex_nat_pair (meas g sp)
    -> sp = Sp av pred (fr, frs)
    -> fr = (x, pre, NT y :: suf_tl)
    -> NtSet.mem y av = true
    -> pushRhs = (fun rhs => Sp (NtSet.remove y av)
                                pred
                                ((y, [], rhs), fr :: frs))
    -> sps' = map pushRhs (rhssForNt g y)
    -> In sp' sps'
    -> Acc lex_nat_pair (meas g sp').
Admitted.

Definition spClosure' :
  forall (g:grammar) (sp : subparser),
    (Acc lex_nat_pair (meas g sp)) -> list (option subparser).
  refine(fix f g sp (a : Acc lex_nat_pair (meas g sp)) {struct a} : list (option subparser) :=
           match sp as sp' return sp = sp' -> _ with
           | Sp av pred (fr, frs) =>
             fun Hsp =>
               match fr as fr' return fr = fr' -> _ with
               | (_, _, []) =>
                 fun Hfr =>
                   match frs as frs' return frs = frs' -> _ with
                   | []                    => fun _ => [Some sp]
                   | (_, _, []) :: _       => fun _ => [None]
                   | (_, _, T _ :: _) :: _ => fun _ => [None]
                   | (x, pre, NT y :: suf') :: frs' =>
                     fun Hfrs =>
                       let stk':= ((x, pre ++ [NT y], suf'), frs')
                       in  f g
                             (Sp (NtSet.add y av) pred stk')
                             (acc_after_return _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                               a Hsp Hfr Hfrs eq_refl)
                   end eq_refl
               | (_, _, T _ :: _)     => fun _ => [Some sp]
               | (x, pre, NT y :: suf') =>
                 fun Hfr =>
                   match NtSet.mem y av as b return NtSet.mem y av = b -> _ with
                   | true =>
                     fun Hm =>
                       let pushRhs := fun rhs => Sp (NtSet.remove y av)
                                                    pred
                                                    ((y, [], rhs), fr :: frs)
                       in
                       let sps' := map pushRhs (rhssForNt g y)
                       in  flat_map' sps'
                                     (fun sp' Hin => f g sp' _)
                   | false => fun _ => [None]
                   end eq_refl
               end eq_refl
           end eq_refl).
  - subst; eapply Acc_inv; eauto.
    assert (In sp' (map pushRhs (rhssForNt g y))) by auto.
    apply in_map_iff in H.
    destruct H as [rhs [Heq Hin']]; subst.
    eapply subparser_lt_after_push; unfold pushRhs; eauto.
Defined.

Inductive prediction_step_result :=
| PstepSucc   : list symbol    -> prediction_step_result
| PstepAmbig  : list symbol    -> prediction_step_result
| PstepReject : string         -> prediction_step_result
| PstepK      : list subparser -> prediction_step_result.
      
Definition allEqual_opt (A : Type) (beq : A -> A -> bool) (x : A) (xs : list A) : option A :=
  if forallb (beq x) xs then Some x else None.

Definition beqGamma (xs ys : list symbol) : bool :=
  if gamma_eq_dec xs ys then true else false.

Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : option (list symbol) :=
  allEqual_opt _ beqGamma sp.(prediction) (map prediction sps).

(* to do -- create a map from symbol list lists (representing remaining symbols to process) to predictions, return true if there's only one key *)
Definition conflicted (sps : list subparser) : bool :=
  true.

Definition llPredictStep (g : grammar) (sps : list subparser) : prediction_step_result :=
  match sps with
  | []      => PstepReject "all subparsers died off"
  | sp :: sps' =>  
    match allPredictionsEqual sp sps' with
    | Some gamma => PstepSucc gamma
    | None       =>
      if conflicted sps then
        PstepAmbig sp.(prediction)
      else
        PstepK (List.concat (map (subparserStep g) sps))
    end
  end.
      

Definition ll1PredictStep (g : grammar) (sps : list subparser_state) : list subparser_state) 