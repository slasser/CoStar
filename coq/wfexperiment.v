Require Import MSets Omega PeanoNat. 
Import ListNotations.

Definition nonterminal := nat.
Module MDT_NT.
  Definition t := nonterminal.
  Definition eq_dec := Nat.eq_dec.
End MDT_NT.
Module NT_as_DT := Make_UDT(MDT_NT).
Module NtSet := MSetWeakList.Make NT_as_DT.
Module NtSetFacts := WFactsOn NT_as_DT NtSet.
Module NtSetEqProps := EqProperties NtSet.
Module ND := WDecideOn NT_as_DT NtSet.

Definition lengthorder (xs ys : list nonterminal) :=
  length xs < length ys.

Lemma lengthorder_wf : well_founded lengthorder.
Proof.
  red.
  intros xs.
  induction xs.
  - constructor; intros ys Hlo.
    red in Hlo.
    simpl in *; omega.
  - constructor.
    intros ys Hlo.
    red in Hlo; simpl in *.
    pose proof IHxs as IH.
    inversion IHxs; subst; clear IHxs.
    assert (Hle: length ys <= length xs) by omega.
    apply le_lt_or_eq in Hle.
    destruct Hle.
    + apply H; auto.
    + constructor; intros. 
      apply H.
      red. red in H1. omega.
Qed.

Definition stack := list (list nonterminal).
Definition avail := NtSet.t.
Definition state := (stack * avail)%type.

Fixpoint stackScore (stk : stack) (mrs : nat) (e : nat) :=
  match stk with
  | [] => 0
  | gamma :: stk' => length gamma * ((mrs + 1) ^ e) + stackScore stk' mrs (e + 1)
  end.

Fixpoint stackPotential (mrs : nat) (e : nat) : nat :=
  match e with
  | O => mrs * ((mrs+1) ^ e)
  | S e' => mrs * ((mrs+1) ^ e) + stackPotential mrs e'
  end.

Definition stateScore (st : state) (b : nat) : nat :=
  let (stk, av) := st in
  let c := NtSet.cardinal av in
  match c with
  | O => stackScore stk b c
  | S c' => stackScore stk b c + stackPotential b c'
  end.

Ltac inv H := inversion H; subst; clear H.

(* Grammar:
 
   X --> [Y]
   Y --> []
*)

Definition x : nonterminal := 0.
Definition y : nonterminal := 1.
Definition x_set := NtSet.add x NtSet.empty.
Definition y_set := NtSet.add y NtSet.empty.
Definition xy_set := NtSet.add x (NtSet.add y NtSet.empty).

Definition st1 : state := ([[x]]         , xy_set).
Definition st2 : state := ([[y]; [x]]    , y_set).
Definition st3 : state := ([[]; [y]; [x]], NtSet.empty).
Definition st4 : state := ([[]; [x]]     , y_set).
Definition st5 : state := ([[]]          , xy_set).

Compute stackScore [[x]] 1 2.
Compute stackPotential 1 1.
Compute stateScore st1 1.
Compute stateScore st2 1.
Compute stateScore st3 1.
Compute stateScore st4 1.
Compute stateScore st5 1.

let step (tbl : parse_table) ((fr, stk') : stack) (ts : token list) : step_result =
  let _ = print_string ((showState (fr, stk') ts) ^ "\n\n") in
  let {lhs_opt = lo; rhs_pre = rpre; rhs_suf = rsuf; sem_val = sv} = fr in
   match rsuf with
   | [] ->
      (match (lo, stk') with
       | (None, [])            -> StepAccept (sv, ts)
       | (Some x, caller :: stk'') ->
          let {lhs_opt = lo'; rhs_pre = rpre'; rhs_suf = rsuf'; sem_val = sv'} = caller in
          (match rsuf' with
           | []              -> StepError "impossible"
           | T _ :: _        -> StepError "impossible"
           | NT x' :: rsuf'' ->
              if x = x' then
                let caller' = mkFrame lo' (rpre' @ [NT x]) rsuf'' (sv' @ [Node (x, sv)])
                in  StepK ((caller', stk''), ts)
              else
                StepError "impossible")
       | (None, _ :: _) -> StepError "impossible"
       | (Some _, [])   -> StepError "impossible")
   | T a :: rsuf' ->
      (match ts with
       | []             -> StepReject "input exhausted"
       | (a', l) :: ts' ->
          if a = a' then
            let fr' = mkFrame lo (rpre @ [T a]) rsuf' (sv @ [Leaf a])
            in  StepK ((fr', stk'), ts')
          else
            StepReject "token mismatch")
   | NT x :: rsuf' ->
      match pt_find_opt (x, peek ts) tbl with
      | Some gamma -> let callee = mkFrame (Some x) [] gamma []
                      in  StepK ((callee, fr :: stk'), ts)
      | None       -> StepReject "no parse table entry"

