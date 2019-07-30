Require Import Arith List Omega PeanoNat Program.Wf String.
Require Import GallStar.Defs.
Require Import GallStar.Lemmas.
Require Import GallStar.Lex.
Require Import GallStar.Tactics.
Require Import GallStar.Termination.
Require Import GallStar.Utils.
Import ListNotations.
Set Implicit Arguments.

(* Hide an alternative definition of "sum" from NtSet *)
Definition sum := Datatypes.sum.

Record subparser := Sp { avail      : NtSet.t
                       ; prediction : list symbol
                       ; stack      : l_stack
                       }.

Open Scope string_scope.

(* error messages for move and closure operations *)
Definition error_message := string.
Definition mvRetErr := "subparser in return state during move operation".
Definition mvNtErr  := "subparser in NT state during move operation".
Definition clRetErr := "no nonterminal to return to".
Definition clRecErr := "left recursion detected".

Open Scope list_scope.

(* "move" operation *)

(* Step from a subparser to...
   None -- token mismatch
   Some (inl err_msg) -- unreachable/error state
   Some (inr sp')     -- successfully consume a token 
*)
Definition moveSp (tok : token) (sp : subparser) :
  option (sum error_message subparser) :=
  match sp with
  | Sp _ pred stk =>
    match stk with
    | ((_, _, []), [])            => None
    | ((_, _, []), _ :: _)        => Some (inl mvRetErr)
    | ((_, _, NT _ :: _), _)      => Some (inl mvNtErr)
    | ((x, pre, T a :: suf), frs) =>
      match tok with
      | (a', _) =>
        if t_eq_dec a' a then
          Some (inr (Sp NtSet.empty pred ((x, pre ++ [T a], suf), frs)))
        else
          None
      end
    end
  end.

(* Return a list of the subparsers that successfully stepped to a new state,
   or an error message if any subparsers reached an error state *)
Definition move (tok : token) (sps : list subparser) :
  sum error_message (list subparser) :=
  let os := map (moveSp tok) sps in
  let es := extractSomes os      
  in  sumOfListSum es.

(* "closure" operation *)

Definition meas (g : grammar) (sp : subparser) : nat * nat :=
  match sp with
  | Sp av _ stk =>
    let m := maxRhsLength g    in
    let e := NtSet.cardinal av in
    (stackScore stk (1 + m) e, stackHeight stk)
  end.

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

Lemma acc_after_push :
  forall (g : grammar)
         (sp sp' : subparser)
         (av : NtSet.t)
         (pred pre suf_tl : list symbol)
         (fr : l_frame)
         (frs : list l_frame)
         (x y : nonterminal),
    Acc lex_nat_pair (meas g sp)
    -> sp = Sp av pred (fr, frs)
    -> fr = (x, pre, NT y :: suf_tl)
    -> NtSet.mem y av = true
    -> In sp' (map (fun rhs => Sp (NtSet.remove y av)
                                  pred
                                  ((y, [], rhs), fr :: frs))
                   (rhssForNt g y))
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g sp sp' av pred pre suf_tl fr frs x y
         Ha Hsp Hfr Hm Hin; subst.
  eapply Acc_inv; eauto.
  apply in_map_iff in Hin.
  destruct Hin as [rhs [Heq Hin]]; subst.
  eapply subparser_lt_after_push; eauto.
Defined.
 
Fixpoint spc (g : grammar) (sp : subparser)
             (a : Acc lex_nat_pair (meas g sp)) {struct a} :
             list (sum error_message subparser) :=
  match sp as s return sp = s -> _ with
  | Sp av pred (fr, frs) =>
    fun Hs =>
      match fr as hd return fr = hd -> _ with
      | (_, _, []) =>
        fun Hf =>
          match frs as tl return frs = tl -> _ with
          | []                    => fun _ => [inr sp]
          | (_, _, []) :: _       => fun _ => [inl clRetErr]
          | (_, _, T _ :: _) :: _ => fun _ => [inl clRetErr]
          | (x, pre, NT y :: suf') :: frs' =>
            fun Hfrs =>
              let stk':= ((x, pre ++ [NT y], suf'), frs') in
              spc g (Sp (NtSet.add y av) pred stk')
                  (acc_after_return _ a Hs Hf Hfrs eq_refl)
          end eq_refl
      | (_, _, T _ :: _)       => fun _ => [inr sp]
      | (x, pre, NT y :: suf') =>
        fun Hf =>
          match NtSet.mem y av as b return NtSet.mem y av = b -> _ with
          | true =>
            fun Hm =>
              let sps' :=
                  map (fun rhs =>
                         Sp (NtSet.remove y av) pred ((y, [], rhs), fr :: frs))
                      (rhssForNt g y)
              in  dflat_map sps'
                            (fun sp' Hi =>
                               spc g sp' (acc_after_push _ _ a Hs Hf Hm Hi))
                        
          | false => fun _ => [inl clRecErr]
          end eq_refl
      end eq_refl
  end eq_refl.

(* to do : write function that extracts all "success" results from the closure result *)

Definition closure (g : grammar) (sps : list subparser) :
  sum error_message (list subparser) :=
  let es := flat_map (fun sp => spc g sp (lex_nat_pair_wf _)) sps
  in  sumOfListSum es.

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