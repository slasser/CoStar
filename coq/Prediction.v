Require Import Defs.

Definition grammar_loc := (nonterminal * list symbol * list symbol)%type.

Definition subparser_stack := (grammar_loc * list grammar_loc)%type.

Record subparser_state := mkSp { avail      : NtSet.t
                               ; prediction : list symbol
                               ; stack      : subparser_stack
                               }.

Definition predictionStep (g : grammar) (st : subparser_state) : list subparser_state :=
  match st with
  | mkSp av (loc, locs) ts =>
    match loc with
    | (x, pre, suf) =>
      match suf with
      | [] =>
        match locs with
        | [] =>
          match ts with
          | [] => [st] (* subparser has concluded and consumed the entire input *)
          | _ :: _ => []
          end
        | (x_caller, pre_caller, suf_caller) :: locs' =>
          match suf_caller with
          | [] => [] (* impossible *)
          | T _ :: _ => [] (* impossible *)
          | NT x' :: suf_caller' =>
            if nt_eq_dec x' x then
              let caller' := (x_caller, pre_caller ++ [NT x], suf_caller')
              in  [mkSp (NtSet.add x av) (caller', locs') ts]
            else
              [] (* impossible *)
          end
        end
      | T a :: suf' =>
        match ts with
        | [] => [] (* input exhausted *)
        | (a', l) :: ts' =>
          if t_eq_dec a' a then 
            let loc' := (x, pre ++ [T a], suf')
            in  StepK (mkState ts' (fr', frs) (allNts g))
          else
            StepReject "token mismatch"
        end
      | NT x :: gamma' => 
        if NtSet.mem x av then
          match ParseTable.find (x, peek ts) tbl with
          | Some gamma_callee =>
            let callee := mkFrame gamma_callee []
            in  StepK (mkState ts (callee, fr :: frs) (NtSet.remove x av))
          | None => StepReject "no parse table entry"
          end
        else
          StepError "left recursion detected"
      end
    end
  end.

Definition ll1PredictStep (g : grammar) (sps : list subparser_state) : list subparser_state) 