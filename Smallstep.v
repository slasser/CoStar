Require Import FMaps Omega PeanoNat String. 
Require Import Defs.
Import ListNotations.

(* LL(1)-related definitions *)
Inductive lookahead := LA : terminal -> lookahead 
                     | EOF : lookahead.

Definition pt_key := (nonterminal * lookahead)%type.

Definition pt_key_eq_dec :
  forall k k2 : pt_key,
    {k = k2} + {k <> k2}.
Proof. repeat decide equality. Defined.

Module MDT_PtKey.
  Definition t := pt_key.
  Definition eq_dec := pt_key_eq_dec.
End MDT_PtKey.

Module PtKey_as_DT := Make_UDT(MDT_PtKey).

Module ParseTable := FMapWeakList.Make PtKey_as_DT.

Definition parse_table := ParseTable.t (list symbol).

Definition peek (input : list token) : lookahead :=
  match input with
  | nil => EOF
  | (a, lit) :: _ => LA a
  end.

Record frame := mkFrame { syms    : list symbol
                        ; sem_val : forest
                        }.

Definition stack := (frame * list frame)%type.

Record state := mkState { tokens : list token
                        ; stk    : stack
                        ; avail  : NtSet.t
                        }.

Inductive step_result := StepAccept : forest -> list token -> step_result
                       | StepReject : string -> step_result
                       | StepK      : state  -> step_result
                       | StepError  : string -> step_result.

Inductive parse_result := Accept : forest -> list token -> parse_result
                        | Reject : string -> parse_result
                        | Error  : string -> parse_result.

Definition ntKeys (tbl : parse_table) : list nonterminal :=
  List.map (fun pr => match pr with 
                      | ((x, _), _) => x
                      end)
           (ParseTable.elements tbl).

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition allNts (tbl : parse_table) : NtSet.t := 
  fromNtList (ntKeys tbl).

Definition entryLengths (tbl : parse_table) : list nat :=
  List.map (fun pr => match pr with
                      | (_, gamma) => List.length gamma
                      end)
           (ParseTable.elements tbl).

Definition listMax (xs : list nat) : nat := 
  fold_right max 0 xs.

Definition maxEntryLength (tbl : parse_table) : nat :=
  listMax (entryLengths tbl).

Definition step (tbl : parse_table) (st : state) : step_result :=
  match st with
  | mkState ts (fr, frs) av =>
    match fr with
    | mkFrame gamma sv =>
      match gamma with
      | [] => 
        match frs with
        | [] => StepAccept sv ts
        | mkFrame gamma_caller sv_caller :: frs' =>
          match gamma_caller with
          | [] => StepError "impossible"
          | T _ :: _ => StepError "impossible"
          | NT x :: gamma_caller' => 
            let caller' := mkFrame gamma_caller' (sv_caller ++ [Node x sv])
            in  StepK (mkState ts (caller', frs') (NtSet.add x av))
          end
        end
      | T a :: gamma' =>
        match ts with
        | [] => StepReject "input exhausted"
        | (a', l) :: ts' =>
          if t_eq_dec a' a then 
            let fr' := mkFrame gamma' (sv ++ [Leaf l])
            in  StepK (mkState ts' (fr', frs) (allNts tbl))
          else
            StepReject "token mismatch"
        end
      | NT x :: gamma' =>
        match ParseTable.find (x, peek ts) tbl with
        | Some gamma_callee =>
          let callee := mkFrame gamma_callee []
          in  StepK (mkState ts (callee, fr :: frs) (NtSet.remove x av))
        | None => StepReject "no parse table entry"
        end
      end
    end
  end.

Definition listOfStack (stk : stack) : list frame :=
  let (fr, frs) := stk in fr :: frs.

Definition gammasOf (frs : list frame) : list (list symbol) :=
  map syms frs.

Fixpoint gammasScore (gammas : list (list symbol)) (b : nat) (e : nat) :=
  match gammas with
  | [] => 0
  | gamma :: gammas' => List.length gamma * ((b + 1) ^ e) + gammasScore gammas' b (e + 1)
  end.

Definition stackScore (stk : stack) b e : nat :=
  gammasScore (gammasOf (listOfStack stk)) b e.

Fixpoint stackPotential (b : nat) (e : nat) : nat :=
  match e with
  | O => b * ((b + 1) ^ e)
  | S e' => b * ((b + 1) ^ e) + stackPotential b e'
  end.

Definition stateScore (st : state) (b : nat) : nat :=
  match st with
  | mkState ts stk avail =>
    let c := NtSet.cardinal avail in
    match c with
    | O => stackScore stk b c
    | S c' => stackScore stk b c + stackPotential b c'
    end
  end.

Ltac inv H := inversion H; subst; clear H.

Lemma add_ain't_empty :
  forall x s,
    ~ NtSet.Empty (NtSet.add x s).
Proof. 
  unfold not; intros x s He.
  specialize (He x); ND.fsetdec.
Qed.


Lemma foo :
  forall st st' ts caller caller' callee frs x gamma' av b,
    st' = mkState ts (caller', frs) (NtSet.add x av)
    -> st = mkState ts (callee, caller :: frs) av
    -> callee.(syms) = []
    -> caller.(syms) = NT x :: gamma'
    -> caller'.(syms) = gamma'
    -> stateScore st' b < stateScore st b.
Proof.
  intros st st' ts caller caller' callee frs x gamma' av b Hst' Hst Hcallee Hcaller Hcaller'.
  subst.
  destruct (NtSet.cardinal (NtSet.add x av)) eqn:Hc.
  - rewrite <- cardinal_Empty in Hc. exfalso; eapply add_ain't_empty; eauto.
  - (* we know that (add x av) is non-empty *)
    simpl.
    rewrite Hc.
    destruct (NtSet.mem x av) eqn:Hm.
    + rewrite add_cardinal_1 in Hc; auto.
      rewrite Hc.
      apply plus_lt_compat_r.
Abort.

Lemma gammasScore_top_frame_nil :
  forall gamma gammas b e,
    List.length gamma = 0
    -> gammasScore (gamma :: gammas) b e = gammasScore gammas b (e + 1).
Proof.
  intros gamma gammas b e He.
  simpl.
  rewrite He; simpl; auto.
Qed.

Lemma gammasScore_top_frame_cons :
  forall gamma sym gamma' gammas b e,
    gamma = sym :: gamma'
    -> gammasScore (gamma :: gammas) b e =
       ((b + 1) ^ e) + List.length gamma' * ((b + 1) ^ e) + gammasScore gammas b (e + 1).
Proof.
  intros gamma sym gamma' gammas b e He.
  subst; simpl; auto.
Qed.
  
Lemma foo :
  forall caller caller' callee gammas s b e,
    callee = nil
    -> caller = s :: caller'
    -> gammasScore (callee :: caller :: gammas) b e = 
       gammasScore (caller' :: gammas) b e + (b ^ (e + 1)).
Proof.
  intros caller caller' callee gammas s b e Hn Hc.
  rewrite gammasScore_top_frame_nil.
  - erewrite gammasScore_top_frame_cons; eauto.
    simpl. 
    

Lemma stateScore_lt :
  forall tbl st st',
    step tbl st = StepK st'
    -> stateScore st' (maxEntryLength tbl) <= stateScore st (maxEntryLength tbl).
Proof.
  intros tbl st st' Hs.
  unfold step in Hs.
  destruct st as [ts [[gamma sv] frs] avail] eqn:Hst.
  destruct gamma eqn:Hg.
  - (* returning to the caller frame *)
    destruct frs as [| [gamma_caller sv_caller] frs']; try congruence.
    destruct gamma_caller as [| [y | x] gamma_caller']; try congruence.
    inv Hs.
    simpl.
    destruct (NtSet.cardinal (NtSet.add x avail)) eqn:Hc.
    + exfalso.
      apply cardinal_Empty in Hc.
      eapply add_ain't_empty; eauto.
    + destruct (NtSet.cardinal avail) as [| c'].
      * simpl in *. omega.
      apply MP.cardinal_Empty in Hc. 
      ND.fsetdec.
    omega.
    unfold stateScore.
    simpl.
    
         
let rec run (tbl : parse_table) (stk : stack) (ts : token list) : parse_result =
  match step tbl stk ts with
  | StepAccept (f, ts') -> Accept (f, ts')
  | StepReject s        -> Reject s
  | StepError s         -> Error s
  | StepK (stk', ts')   -> run tbl stk' ts'

let parse (tbl : parse_table) (s : symbol) (ts : token list) =
  let fr_init = { lhs_opt = None
                ; rhs_pre = []
                ; rhs_suf = [s]
                ; sem_val = []
                }
  in  run tbl (fr_init, []) ts

let g = [ ('S', [T "a"])
        ; ('S', [T "b"])
        ]

let tbl = ParseTable.add ('S', LA "int") [T "int"; T "str"]
            (ParseTable.add ('S', LA "char") [T "char"; T "str"] ParseTable.empty)

let ts = [("int", "42"); ("str", "hello")]
            
let _ = parse tbl (NT 'S') ts