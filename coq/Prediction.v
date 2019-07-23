Require Import Arith List Omega PeanoNat Program.Wf String.
Require Import Defs.
Require Import Lex.
Import ListNotations.

Definition grammar_loc     := (nonterminal * list symbol * list symbol)%type.

Definition subparser_stack := (grammar_loc * list grammar_loc)%type.

Record subparser           := mkSp { prediction : list symbol
                                   ; stack      : subparser_stack
                                   }.

Fixpoint rhssForNt (ps : list production) (x : nonterminal) : list (list symbol) :=
  match ps with
  | []                 => []
  | (x', gamma) :: ps' => 
    if nt_eq_dec x' x then 
      gamma :: rhssForNt ps' x
    else 
      rhssForNt ps' x
  end.

Inductive subparser_move_result :=
| SpMoveSucc   : subparser -> subparser_move_result
| SpMoveDieOff : subparser_move_result
| SpMoveError  : subparser_move_result.

Definition moveSp (tok : token) (sp : subparser) : subparser_move_result :=
  match sp with
  | mkSp pred stk =>
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
          SpMoveSucc (mkSp pred ((x, pre ++ [T a], suf), locs))
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

Record subparser_plus := mkSpPlus { av : NtSet.t
                                  ; sp : subparser
                                  }.


Definition headFrameSuffixLength (loc : grammar_loc) : nat :=
  match loc with
  | (_, _, suf) => List.length suf
  end.

Definition headFrameScore (loc : grammar_loc) (b : nat) (e : nat) : nat :=
  headFrameSuffixLength loc * (b ^ e).

Definition tailFrameSuffixSize (loc : grammar_loc) : nat :=
  match loc with
  | (_, _, suf) =>
    match suf with
    | [] => 0
    | _ :: suf' => List.length suf'
    end
  end.

Definition tailFrameScore (loc : grammar_loc) (b : nat) (e : nat) : nat :=
  tailFrameSuffixSize loc * (b ^ e).

Fixpoint tailFramesScore (locs : list grammar_loc) (b : nat) (e : nat) : nat :=
  match locs with
  | [] => 0
  | loc :: locs' => tailFrameScore loc b e + tailFramesScore locs' b (1 + e)
  end.

Definition stackScore (stk : subparser_stack) (b : nat) (e : nat) : nat :=
  let (hl, tls) := stk
  in  headFrameScore hl b e + tailFramesScore tls b (1 + e).

Definition stackHeight (stk : subparser_stack) : nat :=
  let (_, locs) := stk in List.length locs.

Definition rhsLengths (g : grammar) : list nat :=
  map (fun rhs => List.length rhs) (rhss g).

Definition maxRhsLength (g : grammar) : nat :=
  listMax (rhsLengths g).

Definition meas (g : grammar) (spp : subparser_plus) : nat * nat :=
  match spp with
  | mkSpPlus av (mkSp _ stk) =>
    let m := maxRhsLength g in
    let e := NtSet.cardinal av in
    (stackScore stk (1 + m) e, stackHeight stk)
  end.

Definition nat_lex_pair := pair_lex nat nat lt lt.

Lemma tailFrameScore_cons :
  forall x pre sym suf b e,
    tailFrameScore (x, pre, sym :: suf) b e = List.length suf * b ^ e.
Proof.
  auto.
Qed.

Lemma nonzero_exponents_lt_stackScore_le :
  forall v b e1 e2 e3 e4 frs,
    0 < e1 < e2
    -> 0 < e3 < e4
    -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
       v * (b ^ e2) + tailFramesScore frs b e4.
Proof.
Admitted.

Lemma mem_true_cardinality_gt_0 :
  forall x s,
    NtSet.mem x s = true -> 0 < NtSet.cardinal s.
Admitted.

Inductive sp_closure_step_result :=
| ScsDone  : subparser -> sp_closure_step_result
| ScsCont  : list subparser_plus -> sp_closure_step_result
| ScsError : sp_closure_step_result.

Definition spClosureStep (g : grammar) (spp : subparser_plus) : sp_closure_step_result :=
  match spp with
  | mkSpPlus av sp =>
    match sp with
    | mkSp pred stk => 
      match stk with
      | (loc, locs) =>
        match loc with
        | (x, _, []) =>
          match locs with
          | []              => ScsDone sp
          | caller :: locs' =>
            match caller with
            | (x_caller, pre_caller, suf_caller) =>
              match suf_caller with
              | []                   => ScsError
              | T _ :: _             => ScsError
              | NT x' :: suf_caller' =>
                if nt_eq_dec x' x then
                  let stk' := ((x_caller, pre_caller ++ [NT x], suf_caller'), locs') in
                  let spp' := mkSpPlus (NtSet.add x av) (mkSp pred stk')
                  in  ScsCont [spp']
                else
                  ScsError
              end
            end
          end
        | (_, _, T _ :: _)     => ScsDone sp
        | (_, _, NT y :: suf') =>
          if NtSet.mem y av then
            let rhss := rhssForNt g y in
            let stks := map (fun rhs => ((y, [], rhs), loc :: locs)) rhss in
            let spps := map (fun stk => mkSpPlus (NtSet.remove y av) (mkSp pred stk)) stks in
            ScsCont spps
          else
            ScsError
        end
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
         | [] => fun _ => []
         | h :: t => fun Heq => (f h _) ++ fm t _
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
Program Fixpoint spClosure (g : grammar)
                           (spp : subparser_plus)
                           {measure (meas g spp) (nat_lex_pair)} :
                           list closure_step_result :=
  match spClosureStep g spp with
  | ScsDone sp => [CsSucc sp]
  | ScsError   => [CsError]
  | ScsCont spps => flat_map (fun spp => spClosure g spp) spps
  end.
Next Obligation.
Abort.

(* This does work -- note the alternative flat_map implementation *)
Program Fixpoint spClosure (g : grammar)
                           (spp : subparser_plus)
                           {measure (meas g spp) (nat_lex_pair)} :
                           list closure_step_result :=
  match spClosureStep g spp with
  | ScsDone sp => [CsSucc sp]
  | ScsError   => [CsError]
  | ScsCont spps => flat_map' spps (fun spp Hin => spClosure g spp)
  end.
Next Obligation.
Admitted.

Program Fixpoint spClosure (g : grammar)
                           (spp : subparser_plus)
                           {measure (meas g spp) (nat_lex_pair) } :
  list subparser_closure_result :=
  match spp with
  | mkSpPlus av sp =>
    match sp with
    | mkSp pred stk => 
      match stk with
      | (loc, locs) =>
        match loc with
        | (x, _, []) =>
          match locs with
          | []              => [SpClosureSucc sp]
          | caller :: locs' =>
            match caller with
            | (x_caller, pre_caller, suf_caller) =>
              match suf_caller with
              | []                   => [SpClosureError]
              | T _ :: _             => [SpClosureError]
              | NT x' :: suf_caller' =>
                if nt_eq_dec x' x then
                  let stk' := ((x_caller, pre_caller ++ [NT x], suf_caller'), locs') in
                  let spp' := mkSpPlus (NtSet.add x av) (mkSp pred stk')
                  in  spClosure g spp'
                else
                  [SpClosureError]
              end
            end
          end
        | (_, _, T _ :: _)     => [SpClosureSucc sp]
        | (_, _, NT y :: suf') =>
          if NtSet.mem y av then
            let rhss := rhssForNt g y in
            let stks := map (fun rhs => ((y, [], rhs), loc :: locs)) rhss in
            let spps := map (fun stk => mkSpPlus (NtSet.remove y av) (mkSp pred stk)) stks in
            let res := flat_map (fun sp => spClosure g sp) spps
            in  res
          else
            [SpClosureError]
        end
      end
    end
  end.
Next Obligation.
  unfold headFrameScore; simpl.
  rewrite tailFrameScore_cons.
  destruct (NtSet.mem x av0) eqn:Hm.
  - rewrite add_cardinal_1; auto.
    pose proof nonzero_exponents_lt_stackScore_le as Hnz.
    specialize (Hnz (List.length suf_caller')
                    (S (maxRhsLength g))
                    (NtSet.cardinal av0)
                    (S (NtSet.cardinal av0))
                    (S (NtSet.cardinal av0))
                    (S (S (NtSet.cardinal av0)))
                    locs').
    apply le_lt_or_eq in Hnz.
    + destruct Hnz as [Hlt | Heq].
      * apply pair_fst_lt; auto.
      * rewrite Heq; apply pair_snd_lt; auto.
    + split; auto.
      eapply mem_true_cardinality_gt_0; eauto.
    + split; omega.
  - rewrite add_cardinal_2; auto.
    simpl.
    apply pair_snd_lt; auto.
Defined.
Next Obligation.
  simpl.
  unfold headFrameScore; simpl.
        

    

Fixpoint spClosureStep (spp : subparser_plus) : closure_step_result :=
  match spp with
  | mkSpPlus (mkSp pred stk) av =>
    match 
    






Definition subparserStep (g : grammar) (sp : subparser) : list subparser :=
  match sp with
  | mkSp av pred ts (loc, locs) =>
    match loc with
    | (x, pre, suf) =>
      match suf with
      | [] =>
        match locs with
        | [] =>
          match ts with
          (* subparser has concluded and consumed the entire input *)
          | []     => [sp] 
          (* die off; subparser has concluded but some tokens remain *)
          | _ :: _ => []
          end
        | (x_caller, pre_caller, suf_caller) :: locs' =>
          match suf_caller with
          | []                   => [] (* impossible *)
          | T _ :: _             => [] (* impossible *)
          | NT x' :: suf_caller' =>
            if nt_eq_dec x' x then
              (* simulate a return to the caller frame *)
              let caller' := (x_caller, pre_caller ++ [NT x], suf_caller')
              in  [mkSp (NtSet.add x av) pred ts (caller', locs')]
            else
              [] (* impossible *)
          end
        end
      | T a :: suf' =>
        match ts with
        (* die off; input exhausted *)
        | []             => [] 
        | (a', l) :: ts' =>
          if t_eq_dec a' a then 
            let loc' := (x, pre ++ [T a], suf')
            in  [mkSp NtSet.empty pred ts' (loc', locs)]
          else
            (* die off; token mismatch *)
            []
        end
      | NT x :: gamma' => 
        if NtSet.mem x av then
          let rhss := rhssForNt x g
          in  map (fun rhs => mkSp (NtSet.remove x av) pred ts ((x, [], rhs), loc :: locs)) rhss
        else
          [] (* die off; left recursion detected *)
      end
    end
  end.

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