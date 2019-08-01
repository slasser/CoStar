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

Definition location_stack := (location * list location)%type.

Record subparser := Sp { avail      : NtSet.t
                       ; prediction : list symbol
                       ; stack      : location_stack
                       }.

Open Scope string_scope.

(* error messages for move and closure operations *)
Definition err_msg  := string.
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
  option (sum err_msg subparser) :=
  match sp with
  | Sp _ pred stk =>
    match stk with
    | (Loc _ _ [], [])               => None
    | (Loc _ _ [], _ :: _)           => Some (inl mvRetErr)
    | (Loc _ _ (NT _ :: _), _)       => Some (inl mvNtErr)
    | (Loc x pre (T a :: suf), locs) =>
      match tok with
      | (a', _) =>
        if t_eq_dec a' a then
          Some (inr (Sp NtSet.empty pred (Loc x (pre ++ [T a]) suf, locs)))
        else
          None
      end
    end
  end.

(* Return a list of the subparsers that successfully stepped to a new state,
   or an error message if any subparsers reached an error state *)
Definition move (tok : token) (sps : list subparser) :
  sum err_msg (list subparser) :=
  let os := map (moveSp tok) sps in
  let es := extractSomes os      
  in  sumOfListSum es.

(* "closure" operation *)

Definition meas (g : grammar) (sp : subparser) : nat * nat :=
  match sp with
  | Sp av _ stk =>
    let m := maxRhsLength g in
    let e := NtSet.cardinal av               
    in  (stackScore stk (1 + m) e, stackHeight stk)
  end.

Lemma subparser_lt_after_return :
  forall g sp sp' av pred callee caller caller' locs x x' suf',
    sp = Sp av pred (callee, caller :: locs)
    -> sp' = Sp (NtSet.add x av) pred (caller', locs)
    -> callee.(rsuf)  = []
    -> caller.(rsuf)  = NT x' :: suf'
    -> caller'.(rsuf) = suf'
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' av pred ce cr cr' locs x x' suf' Hsp Hsp' Hce Hcr Hr'; subst.
  unfold meas.
  pose proof (stackScore_le_after_return ce cr cr' x x' cr'.(rsuf)
                                         av locs (1 + maxRhsLength g)) as Hle.
  apply le_lt_or_eq in Hle; auto; destruct Hle as [Hlt | Heq].
  - apply pair_fst_lt; auto.
  - rewrite Heq; apply pair_snd_lt; auto.
Defined.

Lemma acc_after_return :
  forall g sp sp' callee caller caller' av pred pre_ce pre_cr suf_tl locs locs_tl x y z,
    Acc lex_nat_pair (meas g sp)
    -> sp = Sp av pred (callee, locs)
    -> callee = Loc z pre_ce []
    -> locs = caller :: locs_tl
    -> caller = Loc x pre_cr (NT y :: suf_tl)
    -> caller' = Loc x (pre_cr ++ [NT y]) suf_tl
    -> sp' = Sp (NtSet.add y av) pred (caller', locs_tl)
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g sp sp' callee caller caller' av pred pre_ce pre_cr suf_tl
         locs locs_tl x y z Hac Hsp Hce Hl Hcr Hcr' Hsp'; subst.
  eapply Acc_inv; eauto.
  eapply subparser_lt_after_return; eauto.
  simpl; auto.
Defined.

Lemma subparser_lt_after_push :
  forall g sp sp' av pred caller callee locs x y pre suf' rhs,
    sp = Sp av pred (caller, locs)
    -> sp' = Sp (NtSet.remove y av) pred (callee, caller :: locs)
    -> caller = Loc x pre (NT y :: suf')
    -> callee = Loc y [] rhs
    ->  NtSet.mem y av = true
    -> In rhs (rhssForNt g y)
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' av pred cr ce locs x y pre suf' rhs
         Hsp Hsp' Hcr Hce Hmem Hin; subst.
  unfold meas.
  apply pair_fst_lt.
  eapply stackScore_lt_after_push; simpl; eauto.
Defined.

Lemma acc_after_push :
  forall g sp sp' av pred pre suf_tl loc locs x y,
    Acc lex_nat_pair (meas g sp)
    -> sp  = Sp av pred (loc, locs)
    -> loc = Loc x pre (NT y :: suf_tl)
    -> NtSet.mem y av = true
    -> In sp' (map (fun rhs => Sp (NtSet.remove y av)
                                  pred
                                  (Loc y [] rhs, loc :: locs))
                   (rhssForNt g y))
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g sp sp' av pred pre suf_tl loc locs x y Ha Hs Hl Hm Hin; subst.
  eapply Acc_inv; eauto.
  apply in_map_iff in Hin.
  destruct Hin as [rhs [Heq Hin]]; subst.
  eapply subparser_lt_after_push; eauto.
Defined.

(* subparser closure *)
Fixpoint spc (g : grammar) (sp : subparser)
             (a : Acc lex_nat_pair (meas g sp)) {struct a} :
             list (sum err_msg subparser) :=
  match sp as s return sp = s -> _ with
  | Sp av pred (loc, locs) =>
    fun Hs =>
      match loc as l return loc = l -> _ with
      | Loc _ _ [] =>
        fun Hl =>
          match locs as ls return locs = ls -> _ with
          | []                        => fun _  => [inr sp]
          | (Loc _ _ []) :: _         => fun _  => [inl clRetErr]
          | (Loc _ _ (T _ :: _)) :: _ => fun _  => [inl clRetErr]
          | (Loc x pre (NT y :: suf')) :: locs' =>
            fun Hls =>
              let stk':= (Loc x (pre ++ [NT y]) suf', locs') in
              spc g (Sp (NtSet.add y av) pred stk')
                  (acc_after_return _ a Hs Hl Hls eq_refl eq_refl eq_refl)
          end eq_refl
      | Loc _ _ (T _ :: _)       => fun _ => [inr sp]
      | Loc x pre (NT y :: suf') =>
        fun Hl =>
          match NtSet.mem y av as b return NtSet.mem y av = b -> _ with
          | true =>
            fun Hm =>
              let sps' :=
                  map (fun rhs =>
                         Sp (NtSet.remove y av) pred (Loc y [] rhs, loc :: locs))
                      (rhssForNt g y)
              in  dflat_map sps'
                            (fun sp' Hi =>
                               spc g sp' (acc_after_push _ _ a Hs Hl Hm Hi))
                            
          | false => fun _ => [inl clRecErr]
          end eq_refl
      end eq_refl
  end eq_refl.

Definition closure (g : grammar) (sps : list subparser) :
  sum err_msg (list subparser) :=
  let es := flat_map (fun sp => spc g sp (lex_nat_pair_wf _)) sps
  in  sumOfListSum es.

(* LL prediction *)

Inductive prediction_result :=
| PredSucc   : list symbol -> prediction_result
| PredAmbig  : list symbol -> prediction_result
| PredReject :                prediction_result
| PredError  : err_msg     -> prediction_result.

Definition finalConfig (sp : subparser) : bool :=
  match sp with
  | Sp _ _ (Loc _ _ [], []) => true
  | _                       => false
  end.

Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : option (list symbol) :=
  allEqual_opt _ beqGamma sp.(prediction) (map prediction sps).

Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
  match filter finalConfig sps with
  | []         => PredReject
  | sp :: sps' => 
    match allPredictionsEqual sp sps' with
    | Some gamma => PredSucc gamma
    | None       => PredAmbig sp.(prediction)
    end
  end.

Fixpoint llPredict' (g : grammar) (ts : list token) (sps : list subparser) : prediction_result :=
  match ts with
  | []       => handleFinalSubparsers sps
  | t :: ts' =>
    match sps with 
    | []         => PredReject
    | sp :: sps' =>
      match allPredictionsEqual sp sps' with
      | Some gamma => PredSucc gamma
      | None       => 
        match move t sps with
        | inl msg => PredError msg
        | inr mv  =>
          match closure g mv with
          | inl msg => PredError msg
          | inr cl  => llPredict' g ts' cl
          end
        end
      end
    end
  end.

Definition startState (g : grammar) (x : nonterminal) (stk : location_stack) :
  sum err_msg (list subparser) :=
  match stk with
  | (loc, locs) =>
    let init := map (fun rhs => Sp (allNts g) rhs (Loc x [] rhs, loc :: locs))
                    (rhssForNt g x)
    in  closure g init
  end.

Definition llPredict (g : grammar) (x : nonterminal) (stk : location_stack)
                     (ts : list token) : prediction_result :=
  match startState g x stk with
  | inl msg => PredError msg
  | inr sps => llPredict' g ts sps
  end.

