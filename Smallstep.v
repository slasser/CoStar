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

Definition headFrameSize (fr : frame) : nat :=
  List.length fr.(syms).

Definition headFrameScore (fr : frame) (b : nat) (e : nat) : nat :=
  headFrameSize fr * (b ^ e).

Definition tailFrameSize (fr : frame) : nat :=
  match fr.(syms) with
  | [] => 0
  | _ :: syms' => List.length syms'
  end.

Definition tailFrameScore (fr : frame) (b : nat) (e : nat) : nat :=
  tailFrameSize fr * (b ^ e).

Fixpoint tailFramesScore (frs : list frame) (b : nat) (e : nat) : nat :=
  match frs with
  | [] => 0
  | fr :: frs' => tailFrameScore fr b e + tailFramesScore frs' b (1 + e)
  end.

Definition stackScore (stk : stack) (b : nat) (e : nat) : nat :=
  let (hf, tfs) := stk
  in  headFrameScore hf b e + tailFramesScore tfs b (1 + e).

Ltac inv H := inversion H; subst; clear H.

  Section TripleLT.
    
    Variables (A B C : Type) (ltA : relation A) (ltB : relation B) (ltC : relation C).
    
    Inductive triple_lex : A * B * C -> A * B * C -> Prop :=
    | fst_lt : forall x x' y y' z z', ltA x x' -> triple_lex (x, y, z) (x', y', z')
    | snd_lt : forall x y y' z z', ltB y y' -> triple_lex (x, y, z) (x, y', z')
    | thd_lt : forall x y z z', ltC z z' -> triple_lex (x, y, z) (x, y, z').
    
    Hint Constructors triple_lex.
    
    Theorem triple_lex_trans :
      transitive _ ltA -> transitive _ ltB -> transitive _ ltC -> transitive _ triple_lex.
    Proof.
      intros tA tB tC [[x1 y1] z1] [[x2 y2] z2] [[x3 y3] z3] H12 H23.
      inv H12; inv H23; eauto.
    Defined.
    
    Theorem triple_lex_wf :
      well_founded ltA -> well_founded ltB -> well_founded ltC -> well_founded triple_lex.
    Proof.
      intros wfA wfB wfC [[x y] z].
      revert y z.
      induction (wfA x) as [x _ IHx].
      intros y.
      induction (wfB y) as [y _ IHy].
      intros z.
      induction (wfC z) as [z _ IHz].
      constructor.
      intros [[x' y'] z'] H.
      inv H; eauto.
    Defined.
    
  End TripleLT.

Definition stackHeight (stk : stack) : nat :=
  let (_, frs) := stk in List.length frs.

Definition meas (st : state) (tbl : parse_table) : nat * nat * nat :=
  let m := maxEntryLength tbl        in
  let e := NtSet.cardinal st.(avail) in
  (List.length st.(tokens), stackScore st.(stk) (1+m) e, stackHeight st.(stk)).

Lemma meas_unfold : 
  forall st tbl, meas st tbl = (List.length st.(tokens), 
                                stackScore st.(stk) (1 + maxEntryLength tbl) (NtSet.cardinal st.(avail)),
                                stackHeight st.(stk)).
Proof. 
  auto.
Qed.

Definition nat_triple_lex : relation (nat * nat * nat) :=
  triple_lex nat nat nat lt lt lt.

Lemma headFrameScore_nil :
  forall fr b e,
    fr.(syms) = [] -> headFrameScore fr b e = 0.
Proof.
  intros fr b e Hfr.
  unfold headFrameScore. unfold headFrameSize.
rewrite Hfr; auto.
Qed.

Lemma tailFrameScore_cons :
  forall fr sym gamma b e,
    fr.(syms) = sym :: gamma -> tailFrameScore fr b e = List.length gamma * (b ^ e).
Proof.
  intros fr sym gamma b e Hfr.
  unfold tailFrameScore. unfold tailFrameSize.
  rewrite Hfr; auto.
Qed.

Lemma stackScore_head_frame_nil :
  forall fr frs b e, 
    fr.(syms) = [] 
    -> stackScore (fr, frs) b e = tailFramesScore frs b (1 + e).
Proof.
  intros fr frs b e Hfr.  
  unfold stackScore. unfold headFrameScore. unfold headFrameSize.
  rewrite Hfr; simpl; auto.
Qed.

Lemma stackScore_pre_return :
  forall fr fr' sym gamma frs b e, 
    fr.(syms) = nil
    -> fr'.(syms) = sym :: gamma
    -> stackScore (fr, fr' :: frs) b e = 
       (List.length gamma * b ^ (1 + e)) + tailFramesScore frs b (2 + e).
Proof.
  intros fr fr' sym gamma frs b e Hfr Hfr'.
  rewrite stackScore_head_frame_nil; auto.
  simpl.
  erewrite tailFrameScore_cons; eauto.
Qed.

Lemma nonzero_exponents_lt_powers_le :
  forall b e1 e2, 0 < e1 < e2 -> b ^ e1 <= b ^ e2.
Proof.
  intros b e1 e2 [Hlt Hlt']. 
  destruct b as [| b']. 
  - destruct e1; destruct e2; auto.
    omega.
  - destruct b' as [| b''].
    + repeat rewrite Nat.pow_1_l; auto.
    + pose proof Nat.pow_lt_mono_r. 
      specialize (H (S (S b'')) e1 e2). 
      assert (fact : forall n m, n < m -> n <= m) by (intros; omega).
      apply fact.
      apply Nat.pow_lt_mono_r; auto.
      omega.
Qed.

Lemma stackScore_le_after_return :
  forall callee caller caller' sym gamma frs b e,
    callee.(syms) = []
    -> caller.(syms) = sym :: gamma
    -> caller'.(syms) = gamma
    -> 0 < e
    -> stackScore (caller', frs) b e <= stackScore (callee, caller :: frs) b e.
Proof.
  intros callee caller caller' sym gamma frs b e Hnil Hcons Htl Hnz.
  erewrite stackScore_pre_return; eauto.
  unfold stackScore. unfold headFrameScore. unfold headFrameSize. subst.
  assert (fact : forall a b c d, a <= c -> b <= d -> a + b <= c + d) by (intros; omega).
  apply fact.
  - apply Nat.mul_le_mono_l.
    apply nonzero_exponents_lt_powers_le; auto.
  - admit.
Admitted.

Lemma nonzero_exponents_lt_tailFrameScore_le :
  forall fr b e1 e2,
    0 < e1 < e2
    -> tailFrameScore fr b e1 <= tailFrameScore fr b e2.
Proof.
  intros fr b e1 e2 Hlt.
  unfold tailFrameScore. 
  apply Nat.mul_le_mono_l.
  apply nonzero_exponents_lt_powers_le; auto.
Qed.

Lemma nonzero_exponents_lt_tailFramesScore_le :
  forall frs b e1 e2,
    0 < e1 < e2
    -> tailFramesScore frs b e1 <= tailFramesScore frs b e2.
Proof.
  intros frs.
  induction frs as [| fr frs IH]; intros b e1 e2 Hlt; simpl; auto.
  apply plus_le_compat.
  - apply nonzero_exponents_lt_tailFrameScore_le; auto.
  - apply IH; omega.
Qed.

Lemma nonzero_exponents_lt_stackScore_le :
  forall v b e1 e2 e3 e4 frs,
    0 < e1 < e2
    -> 0 < e3 < e4
    -> v * (b ^ e1) + tailFramesScore frs b e3 <= 
       v * (b ^ e2) + tailFramesScore frs b e4.
Proof.
  intros v b e1 e2 e3 e4 frs [H0e1 He1e2] [H0e3 He3e4].
  apply plus_le_compat.
  - apply Nat.mul_le_mono_l. 
    apply nonzero_exponents_lt_powers_le; auto.
  - apply nonzero_exponents_lt_tailFramesScore_le; auto.
Qed.

Lemma mem_true_cardinality_neq_0 :
  forall x s,
    NtSet.mem x s = true -> NtSet.cardinal s <> 0.
Proof.
  intros x s Hm; unfold not; intros Heq.
  rewrite NtSet.mem_spec in Hm.
  apply cardinal_inv_1 in Heq.
  unfold NtSet.Empty in Heq. 
  eapply Heq; eauto.
Qed.

Lemma mem_true_cardinality_gt_0 :
  forall x s,
    NtSet.mem x s = true -> 0 < NtSet.cardinal s.
Proof.
  intros x s Hm.
  apply mem_true_cardinality_neq_0 in Hm; omega.
Qed.

  Lemma post_return_state_lt_pre_return_state :
  forall st st' ts callee caller caller' frs x gamma av tbl,
    st = mkState ts (callee, caller :: frs) av
    -> st' = mkState ts (caller', frs) (NtSet.add x av)
    -> callee.(syms) = []
    -> caller.(syms) = NT x :: gamma
    -> caller'.(syms) = gamma
    -> nat_triple_lex (meas st' tbl) (meas st tbl).
Proof.
  intros st st' ts callee caller caller' frs x gamma av tbl Hst Hst' Hnil Hcons Htl; subst.
  unfold meas; simpl.
  rewrite headFrameScore_nil with (fr := callee); simpl; auto.
  erewrite tailFrameScore_cons; eauto.
  unfold headFrameScore. unfold headFrameSize.
  destruct (NtSet.mem x av) eqn:Hm.
  - (* x is already in av, so the cardinality stays the same *)
    rewrite add_cardinal_1; auto.
    pose proof nonzero_exponents_lt_stackScore_le as Hle. 
    specialize (Hle (List.length caller'.(syms))
                  (S (maxEntryLength tbl)) 
                  (NtSet.cardinal av)
                  (S (NtSet.cardinal av))
                  (S (NtSet.cardinal av))
                  (S (S (NtSet.cardinal av)))
                  frs).
    apply le_lt_or_eq in Hle.
    + destruct Hle as [Hlt | Heq]; subst.
      * apply snd_lt; auto.
      * rewrite Heq.
        apply thd_lt; auto.
    + split; auto.
      eapply mem_true_cardinality_gt_0; eauto.
    + split; auto.
      omega.
  - (* x isn't in av, so the cardinality increase by 1 *)
    rewrite add_cardinal_2; auto.
    apply thd_lt; auto.
Qed.

Lemma step_meas_lt :
  forall tbl st st',
    step tbl st = StepK st'
    -> nat_triple_lex (meas st' tbl) (meas st tbl).
Proof.
  intros tbl st st' Hs.
  unfold step in Hs.
  destruct st as [ts [fr frs] av].
  destruct fr as [gamma sv].
  destruct gamma as [| [y | x] gamma'].
  - (* return from the current frame *)
    destruct frs as [| caller frs']; try congruence.
    destruct caller as [gamma_caller sv_caller]. 
    destruct gamma_caller as [| [y | x] gamma_caller']; try congruence.
    inv Hs.
    eapply post_return_state_lt_pre_return_state; simpl; eauto.
    simpl; auto.
  - admit.
  - admit.
Admitted.

Lemma add_ain't_empty :
  forall x s,
    ~ NtSet.Empty (NtSet.add x s).
Proof. 
  unfold not; intros x s He.
  specialize (He x); ND.fsetdec.
Qed.
             
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