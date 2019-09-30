Require Import Arith List Omega PeanoNat Program.Wf String.
Require Import GallStar.Defs.
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
    | (Loc xo pre (T a :: suf), locs) =>
      match tok with
      | (a', _) =>
        if t_eq_dec a' a then
          Some (inr (Sp NtSet.empty pred (Loc xo (pre ++ [T a]) suf, locs)))
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
  forall g sp sp' callee caller caller' av pred pre_ce pre_cr suf_tl locs locs_tl xo y zo,
    Acc lex_nat_pair (meas g sp)
    -> sp = Sp av pred (callee, locs)
    -> callee = Loc zo pre_ce []
    -> locs = caller :: locs_tl
    -> caller = Loc xo pre_cr (NT y :: suf_tl)
    -> caller' = Loc xo (pre_cr ++ [NT y]) suf_tl
    -> sp' = Sp (NtSet.add y av) pred (caller', locs_tl)
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g sp sp' callee caller caller' av pred pre_ce pre_cr suf_tl
         locs locs_tl xo y zo Hac Hsp Hce Hl Hcr Hcr' Hsp'; subst.
  eapply Acc_inv; eauto.
  eapply subparser_lt_after_return; eauto.
  simpl; auto.
Defined.

Lemma subparser_lt_after_push :
  forall g sp sp' av pred caller callee locs xo y pre suf' rhs,
    sp = Sp av pred (caller, locs)
    -> sp' = Sp (NtSet.remove y av) pred (callee, caller :: locs)
    -> caller = Loc xo pre (NT y :: suf')
    -> callee = Loc (Some y) [] rhs
    ->  NtSet.In y av
    -> In rhs (rhssForNt g y)
    -> lex_nat_pair (meas g sp') (meas g sp).
Proof.
  intros g sp sp' av pred cr ce locs xo y pre suf' rhs
         Hsp Hsp' Hcr Hce Hin Hin'; subst.
  unfold meas.
  apply pair_fst_lt.
  eapply stackScore_lt_after_push; simpl; eauto.
Defined.

Lemma acc_after_push :
  forall g sp sp' av pred pre suf_tl loc locs xo y,
    Acc lex_nat_pair (meas g sp)
    -> sp  = Sp av pred (loc, locs)
    -> loc = Loc xo pre (NT y :: suf_tl)
    -> NtSet.In y av
    -> In sp' (map (fun rhs => Sp (NtSet.remove y av)
                                  pred
                                  (Loc (Some y) [] rhs, loc :: locs))
                   (rhssForNt g y))
    -> Acc lex_nat_pair (meas g sp').
Proof.
  intros g sp sp' av pred pre suf_tl loc locs xo y Ha Hs Hl Hin Hin'; subst.
  eapply Acc_inv; eauto.
  apply in_map_iff in Hin'.
  destruct Hin' as [rhs [Heq Hin']]; subst.
  eapply subparser_lt_after_push; eauto.
Defined.

Definition mem_dec (x : nonterminal) (s : NtSet.t) :
  {~NtSet.In x s} + {NtSet.In x s}.
  destruct (NtSet.mem x s) eqn:Hm.
  - right.
    apply NtSet.mem_spec; auto.
  - left.
    unfold not; intros H.
    apply NtSet.mem_spec in H.
    congruence.
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
          | (Loc xo pre (NT y :: suf')) :: locs' =>
            fun Hls =>
              let stk':= (Loc xo (pre ++ [NT y]) suf', locs') in
              spc g (Sp (NtSet.add y av) pred stk')
                  (acc_after_return _ a Hs Hl Hls eq_refl eq_refl eq_refl)
          end eq_refl
      | Loc _ _ (T _ :: _)       => fun _ => [inr sp]
      | Loc xo pre (NT y :: suf') =>
        fun Hl =>
          match mem_dec y av with
          | left _   => [inl clRecErr]
          | right Hm =>
            let sps' :=
                map (fun rhs =>
                       Sp (NtSet.remove y av) pred (Loc (Some y) [] rhs, loc :: locs))
                    (rhssForNt g y)
            in  dflat_map sps'
                          (fun sp' Hi =>
                             spc g sp' (acc_after_push _ _ a Hs Hl Hm Hi))
          end
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

Definition allPredictionsEqual (sp : subparser) (sps : list subparser) : bool :=
  allEqual _ beqGamma sp.(prediction) (map prediction sps).

Definition handleFinalSubparsers (sps : list subparser) : prediction_result :=
  match filter finalConfig sps with
  | []         => PredReject
  | sp :: sps' => 
    if allPredictionsEqual sp sps' then
      PredSucc sp.(prediction)
    else
      PredAmbig sp.(prediction)
  end.

Fixpoint llPredict' (g : grammar) (ts : list token) (sps : list subparser) : prediction_result :=
  match ts with
  | []       => handleFinalSubparsers sps
  | t :: ts' =>
    match sps with 
    | []         => PredReject
    | sp :: sps' =>
      if allPredictionsEqual sp sps' then
        PredSucc sp.(prediction)
      else
        match move t sps with
        | inl msg => PredError msg
        | inr mv  =>
          match closure g mv with
          | inl msg => PredError msg
          | inr cl  => llPredict' g ts' cl
          end
        end
    end
  end.

Definition startState (g : grammar) (x : nonterminal) (stk : location_stack) :
  sum err_msg (list subparser) :=
  match stk with
  | (loc, locs) =>
    let init := map (fun rhs => Sp (allNts g) rhs (Loc (Some x) [] rhs, loc :: locs))
                    (rhssForNt g x)
    in  closure g init
  end.

Definition llPredict (g : grammar) (x : nonterminal) (stk : location_stack)
                     (ts : list token) : prediction_result :=
  match startState g x stk with
  | inl msg => PredError msg
  | inr sps => llPredict' g ts sps
  end.

(* LEMMAS *)

Lemma handleFinalSubparsers_success_from_subparsers :
  forall sps gamma,
    handleFinalSubparsers sps = PredSucc gamma
    -> exists sp, In sp sps /\ sp.(prediction) = gamma.
Proof.
  intros sps gamma Hh.
  unfold handleFinalSubparsers in Hh.
  dmeq Hf; tc.
  dm; tc.
  inv Hh.
  eexists; split; eauto.
  eapply filter_cons_in; eauto.
Defined.

Lemma handleFinalSubparsers_ambig_from_subparsers :
  forall sps gamma,
    handleFinalSubparsers sps = PredAmbig gamma
    -> exists sp, In sp sps /\ sp.(prediction) = gamma.
Proof.
  intros sps gamma Hh.
  unfold handleFinalSubparsers in Hh.
  dmeq Hf; tc.
  dm; tc.
  inv Hh.
  eexists; split; eauto.
  eapply filter_cons_in; eauto.
Defined.

Lemma move_unfold :
  forall t sps,
    move t sps = 
    let os := map (moveSp t) sps in
    let es := extractSomes os      
    in  sumOfListSum es.
Proof. 
  auto. 
Defined.

Lemma in_sumOfListSum_result_in_input :
  forall A B (es : list (sum A B)) (b : B) (bs : list B),
    sumOfListSum es = inr bs
    -> In b bs
    -> In (inr b) es.
Proof.
  intros A B es b.
  induction es as [| e es' IH]; intros bs Hs Hi.
  - simpl in *. inv Hs. inv Hi.
  - simpl in Hs.
    destruct e as [a | b']; tc.
    destruct (sumOfListSum es') eqn:Htl; tc.
    inv Hs.
    inv Hi.
    + apply in_eq.
    + apply in_cons; eauto.
Defined.

Lemma in_extractSomes_result_in_input :
  forall A (a : A) (os : list (option A)),
    In a (extractSomes os)
    -> In (Some a) os.
Proof.
  intros A a os Hi; induction os as [| o os' IH]; simpl in Hi.
  - inv Hi.
  - destruct o as [a' |].
    + inv Hi.
      * apply in_eq.
      * apply in_cons; auto.
    + apply in_cons; auto.
Defined.

Lemma moveSp_preserves_prediction :
  forall t sp sp',
    moveSp t sp = Some (inr sp')
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros t sp sp' Hm.
  unfold moveSp in Hm.
  destruct sp as [av pred (loc, locs)].
  destruct loc as [x pre suf].
  destruct suf as [| [a | x'] suf_tl]; tc.
  - destruct locs; tc.
  - destruct t as (a', _).
    destruct (t_eq_dec a' a); subst; tc.
    inv Hm; auto.
Defined.

Lemma move_preserves_prediction :
  forall t sp' sps sps',
    move t sps = inr sps'
    -> In sp' sps'
    -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
Proof.
  intros s sp' sps sps' Hm Hin.
  unfold move in Hm.
  eapply in_sumOfListSum_result_in_input in Hm; eauto.
  apply in_extractSomes_result_in_input in Hm.
  eapply in_map_iff in Hm.
  destruct Hm as [sp [Hmsp Hin']].
  eexists; split; eauto.
  eapply moveSp_preserves_prediction; eauto.
Defined.

Lemma spc_unfold_return :
  forall g sp a es av pred stk loc locs x pre caller locs_tl x_cr pre_cr suf_cr y suf_tl_cr,
    spc g sp a = es
    -> sp = Sp av pred stk
    -> stk = (loc, locs)
    -> loc = Loc x pre []
    -> locs = caller :: locs_tl
    -> caller = Loc x_cr pre_cr suf_cr
    -> suf_cr = NT y :: suf_tl_cr
    -> exists a',
        spc g
            (Sp (NtSet.add y av)
                pred
                (Loc x_cr (pre_cr ++ [NT y]) suf_tl_cr, locs_tl))
            a' = es.
Proof.
  intros.
  subst.
  destruct a.
  simpl.
  eexists; eauto.
Defined.

Lemma in_dflat_map :
  forall (A B : Type) (l : list A) (f : forall x, In x l -> list B) (y : B) (ys : list B),
    dflat_map l f = ys
    -> In y ys
    -> (exists x Hin, In x l /\ In y (f x Hin)).
Proof.
  intros A B l f y ys Heq Hin; subst.
  induction l as [| x l' IH].
  + inv Hin.
  + simpl in Hin.
    apply in_app_or in Hin; destruct Hin as [Hl | Hr].
    * exists x; eexists; split; eauto.
      apply in_eq.
    * apply IH in Hr.
      destruct Hr as [x' [Hin [Hin' Hin'']]].
      exists x'; eexists; split; eauto.
      -- apply in_cons; auto.
      -- apply Hin''.
Defined.

(* CLEAN THIS UP! *)
Lemma sp_closure_preserves_prediction :
  forall g sp Ha sp' es,
    spc g sp Ha = es
    -> In (inr sp') es
    -> sp'.(prediction) = sp.(prediction).
Proof.
  intros g sp.
  remember (stackScore (stack sp) (S (maxRhsLength g)) (NtSet.cardinal (avail sp))) as score.
  generalize dependent sp.
  induction score as [score IHscore] using lt_wf_ind.
  intros sp.
  remember (stackHeight (stack sp)) as height.
  generalize dependent sp.
  induction height as [height IHheight] using lt_wf_ind.
  intros sp Hheight Hscore Ha sp' es Hf Hi.
  destruct Ha as [Ha].
  destruct sp as [av pred stk] eqn:Hsp.
  destruct stk as (loc, locs) eqn:Hstk.
  destruct loc as [x pre suf] eqn:Hloc.
  destruct suf as [| [a | y] suf_tl] eqn:Hsuf.
  - (* return case *)
    destruct locs as [| caller locs_tl] eqn:Hlocs.
    + (* return to final configuration *)
      simpl in Hf; subst.
      apply in_singleton_eq in Hi; inv Hi; auto.
    + (* return to caller frame *)
      destruct caller as [x_cr pre_cr suf_cr] eqn:Hcr.
      destruct suf_cr as [| [a | x'] suf_tl_cr] eqn:Hsufcr.
      * simpl in Hf; subst.
        apply in_singleton_eq in Hi; tc.
      * simpl in Hf; subst.
        apply in_singleton_eq in Hi; tc.
      * (*eapply spc_unfold_return in Hf; eauto.
        destruct Hf as [a' Hf]. *)
        pose proof stackScore_le_after_return as Hss.
        specialize Hss with
            (callee := Loc x pre [])
            (caller := Loc x_cr pre_cr (NT x' :: suf_tl_cr))
            (caller' := Loc x_cr (pre_cr ++ [NT x']) suf_tl_cr)
            (x := x')
            (x' := x')
            (suf' := suf_tl_cr)
            (av := av)
            (locs := locs_tl)
            (b := S (maxRhsLength g)).
        eapply le_lt_or_eq in Hss; auto.
        destruct Hss as [Hlt | Heq].
        -- eapply IHscore with
               (sp := Sp (NtSet.add x' av)
                         pred
                         (Loc x_cr (pre_cr ++ [NT x']) suf_tl_cr,
                          locs_tl)); subst; eauto.
        -- eapply IHheight with
               (sp := Sp (NtSet.add x' av)
                         pred
                         (Loc x_cr (pre_cr ++ [NT x']) suf_tl_cr,
                          locs_tl)); subst; eauto.
           simpl; auto.
  - (* next symbol is a terminal *)
    simpl in Hf; subst.
    apply in_singleton_eq in Hi; inv Hi; auto.
  - (* next symbol is a nonterminal *)
    simpl in Hf.
    destruct (mem_dec y av).
    + subst; apply in_singleton_eq in Hi; inv Hi.
    + eapply in_dflat_map in Hf; eauto.
      destruct Hf as [sp_mid [Hin [Hin' Hf]]].
      eapply in_map_iff in Hin'.
      destruct Hin' as [rhs [Heq Hin']].
      assert (Hlt : stackScore (stack sp_mid) (S (maxRhsLength g)) (NtSet.cardinal (avail sp_mid)) < score).
      { subst.
        eapply stackScore_lt_after_push; simpl; eauto. }
      subst.
      eapply IHscore in Hlt; simpl in *; eauto.
      simpl in *; auto.
      simpl in *; auto.
Defined.
  
Lemma closure_preserves_prediction :
  forall g sp' sps sps',
    closure g sps = inr sps'
    -> In sp' sps'
    -> exists sp, In sp sps /\ sp'.(prediction) = sp.(prediction).
Proof.
  intros g sp' sps sps' Hc Hi'.
  unfold closure in Hc.
  eapply in_sumOfListSum_result_in_input in Hc; eauto.
  apply in_flat_map in Hc.
  destruct Hc as [sp [Hi Hspc]].
  eexists; split; eauto.
  eapply sp_closure_preserves_prediction; eauto.
Defined.

Lemma llPredict'_success_result_in_original_subparsers :
  forall g ts gamma sps,
    llPredict' g ts sps = PredSucc gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts_tl IH]; intros sps Hl; simpl in Hl.
  - eapply handleFinalSubparsers_success_from_subparsers; eauto.
  - destruct sps as [| sp_hd sps_tl] eqn:Hs; tc.
    destruct (allPredictionsEqual sp_hd sps_tl) eqn:Ha.
    + inv Hl.
      eexists; split; eauto.
      apply in_eq.
    + rewrite <- Hs in *; clear Hs. 
      destruct (move t _) as [msg | sps'] eqn:Hm; tc.
      destruct (closure g sps') as [msg | sps''] eqn:Hc; tc. 
      apply IH in Hl; clear IH.
      destruct Hl as [sp'' [Hin'' Heq]]; subst.
      eapply closure_preserves_prediction in Hc; eauto.
      destruct Hc as [sp' [Hin' Heq]]; rewrite Heq; clear Heq.
      eapply move_preserves_prediction in Hm; eauto.
      destruct Hm as [sp [Hin Heq]]; eauto.
Defined.

Lemma llPredict'_ambig_result_in_original_subparsers :
  forall g ts gamma sps,
    llPredict' g ts sps = PredAmbig gamma
    -> exists sp, In sp sps /\ (prediction sp) = gamma.
Proof.
  intros g ts gamma.
  induction ts as [| t ts_tl IH]; intros sps Hl; simpl in Hl.
  - eapply handleFinalSubparsers_ambig_from_subparsers; eauto.
  - destruct sps as [| sp_hd sps_tl] eqn:Hs; tc.
    destruct (allPredictionsEqual sp_hd sps_tl) eqn:Ha; tc.
    rewrite <- Hs in *; clear Hs. 
    destruct (move t _) as [msg | sps'] eqn:Hm; tc.
    destruct (closure g sps') as [msg | sps''] eqn:Hc; tc. 
    apply IH in Hl; clear IH.
    destruct Hl as [sp'' [Hin'' Heq]]; subst.
    eapply closure_preserves_prediction in Hc; eauto.
    destruct Hc as [sp' [Hin' Heq]]; rewrite Heq; clear Heq.
    eapply move_preserves_prediction in Hm; eauto.
    destruct Hm as [sp [Hin Heq]]; eauto.
Defined.

Lemma startState_sp_prediction_in_rhssForNt :
  forall g x stk sp' sps',
    startState g x stk = inr sps'
    -> In sp' sps'
    -> In sp'.(prediction) (rhssForNt g x).
Proof.
  intros g x stk sp' sps' Hf Hi.
  unfold startState in Hf.
  destruct stk as (loc, locs).
  eapply closure_preserves_prediction in Hf; eauto.
  destruct Hf as [sp [Hin Heq]]; subst.
  apply in_map_iff in Hin.
  destruct Hin as [gamma [Hin Heq']]; subst.
  rewrite Heq; auto.
Defined.  

Lemma PredSucc_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredSucc gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma Hp.
  unfold llPredict in Hp.
  dmeq Hss; tc.
  apply llPredict'_success_result_in_original_subparsers in Hp.
  destruct Hp as [sp [Hin Heq]]; subst.
  eapply startState_sp_prediction_in_rhssForNt; eauto.
Defined.

Lemma PredAmbig_result_in_rhssForNt :
  forall g x stk ts gamma,
    llPredict g x stk ts = PredAmbig gamma
    -> In gamma (rhssForNt g x).
Proof.
  intros g x stk ts gamma Hf.
  unfold llPredict in Hf.
  dmeq Hss; tc.
  apply llPredict'_ambig_result_in_original_subparsers in Hf.
  destruct Hf as [sp [Hin Heq]]; subst.
  eapply startState_sp_prediction_in_rhssForNt; eauto.
Defined.

Lemma llPredict_succ_arg_result_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredSucc ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply PredSucc_result_in_rhssForNt in hp.
  apply in_rhssForNt_production_in_grammar; auto.
Qed.

Lemma llPredict_ambig_arg_result_in_grammar :
  forall g x stk ts ys,
    llPredict g x stk ts = PredAmbig ys
    -> In (x, ys) g.
Proof.
  intros g x stk ts ys hp.
  apply in_rhssForNt_production_in_grammar.
  eapply PredAmbig_result_in_rhssForNt; eauto.
Qed.