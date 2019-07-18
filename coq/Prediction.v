Require Import List PeanoNat String.
Require Import Defs.
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

Inductive subparser_closure_result :=
| SpClosureSucc  : subparser -> subparser_closure_result
| SpClosureError : subparser_closure_result.

Definition headLocSize (loc : grammar_loc) : nat :=
  match loc with
  | (_, _, suf) => List.length suf
  end.

Definition headLocScore (loc : grammar_loc) (b : nat) (e : nat) : nat :=
  headLocSize loc * (b ^ e).

Definition tailLocSize (loc : grammar_loc) : nat :=
  match loc with
  | (_, _, suf) =>
    match suf with
    | [] => 0
    | _ :: suf' => List.length suf'
    end
  end.

Definition tailLocScore (loc : grammar_loc) (b : nat) (e : nat) : nat :=
  tailLocSize loc * (b ^ e).

Fixpoint tailLocsScore (locs : list grammar_loc) (b : nat) (e : nat) : nat :=
  match locs with
  | [] => 0
  | loc :: locs' => tailLocScore loc b e + tailLocsScore locs' b (1 + e)
  end.

Definition stackScore (stk : subparser_stack) (b : nat) (e : nat) : nat :=
  let (hl, tls) := stk
  in  headLocScore hl b e + tailLocsScore tls b (1 + e).

Fixpoint spClosure (g : grammar) (spp : subparser_plus) : list subparser_closure_result :=
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
            let spps := map (fun stk => mkSpPlus (NtSet.remove y av) (mkSp pred stk)) stks
            in  List.concat (map (spClosure g) spps)
          else
            [SpClosureError]
        end
      end
    end
  end.

        

      
Inductive closure_step_result :=
| ClosureStepSucc  : list subparser_plus -> closure_step_result
| ClosureStepError : closure_step_result.

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