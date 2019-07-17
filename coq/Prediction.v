Require Import List String.
Require Import Defs.
Import ListNotations.

Definition grammar_loc     := (nonterminal * list symbol * list symbol)%type.

Definition subparser_stack := (grammar_loc * list grammar_loc)%type.

Record subparser           := mkSp { avail      : NtSet.t
                                   ; prediction : list symbol
                                   ; ts         : list token
                                   ; stack      : subparser_stack
                                   }.

Fixpoint rhssForNt (x : nonterminal) (ps : list production) : list (list symbol) :=
  match ps with
  | []                 => []
  | (x', gamma) :: ps' => 
    if nt_eq_dec x' x then 
      gamma :: rhssForNt x ps' 
    else 
      rhssForNt x ps'
  end.

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