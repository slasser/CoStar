Require Import FMaps List MSets Omega PeanoNat String.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
        Import ListNotations.

(* CORE PROJECT DEFINITIONS *)

(* Representations of grammar symbols *)
Definition terminal    := string.
Definition nonterminal := nat.
Inductive symbol       := T  : terminal -> symbol 
                        | NT : nonterminal -> symbol.

Lemma t_eq_dec :
  forall a a' : terminal,
    {a = a'} + {a <> a'}.
Proof. repeat decide equality. Defined.

Lemma nt_eq_dec :
  forall x x' : nonterminal,
    {x = x'} + {x <> x'}.
Proof. decide equality. Defined.

Lemma gamma_eq_dec :
  forall gamma gamma' : list symbol,
    {gamma = gamma'} + {gamma <> gamma'}.
Proof. repeat decide equality. Defined.

Definition beqGamma (xs ys : list symbol) : bool :=
  if gamma_eq_dec xs ys then true else false.

(* Finite sets of nonterminals *)
Module MDT_NT.
  Definition t      := nonterminal.
  Definition eq_dec := Nat.eq_dec.
End MDT_NT.
Module NT_as_DT     := Make_UDT(MDT_NT).
Module NtSet        := MSetWeakList.Make NT_as_DT.
Module Export NF    := WFactsOn NT_as_DT NtSet.
Module Export NP    := MSetProperties.Properties NtSet.
Module Export NE    := EqProperties NtSet.
Module Export ND    := WDecideOn NT_as_DT NtSet.

(* Grammar-related definitions *)               
Definition production := (nonterminal * list symbol)%type.

Definition grammar    := list production.

Definition lhs (p : production) : nonterminal :=
  let (x, _) := p in x.

Definition lhss (g : grammar) : list nonterminal :=
  map lhs g.

Lemma production_lhs_in_lhss :
  forall g x ys,
    In (x, ys) g
    -> In x (lhss g).
Proof.
  intros g x ys hi; induction g as [| (x', ys') ps IH]; sis.
  - inv hi.
  - destruct hi as [hh | ht].
    + inv hh; apply in_eq.
    + apply in_cons; auto.
Qed.

Definition rhs (p : production) : list symbol :=
  let (_, gamma) := p in gamma.

Definition rhss (g : grammar) : list (list symbol) :=
  map rhs g.

Fixpoint rhssForNt (ps : list production) (x : nonterminal) : list (list symbol) :=
  match ps with
  | []                 => []
  | (x', gamma) :: ps' => 
    if nt_eq_dec x' x then 
      gamma :: rhssForNt ps' x
    else 
      rhssForNt ps' x
  end.

Lemma rhssForNt_in_iff :
  forall g x ys,
    In ys (rhssForNt g x)
    <-> In (x, ys) g.
Proof.
  intros g x ys; split; intros hi.
  - induction g as [| (x', ys') g]; sis; tc.
    destruct (nt_eq_dec x' x); subst; auto.
    inv hi; auto.
  - induction g as [| (x', ys') g]; sis; tc.
    destruct hi as [heq | hi].
    + inv heq.
      destruct (nt_eq_dec x x); tc.
      apply in_eq.
    + destruct (nt_eq_dec x' x); subst; auto.
      apply in_cons; auto.
Qed.
Hint Resolve rhssForNt_in_iff.

Lemma rhssForNt_rhss :
  forall g x rhs,
    In rhs (rhssForNt g x) -> In rhs (rhss g).
Proof.
  intros g x rhs Hin; induction g as [| (x', rhs') ps IH]; simpl in *.
  - inv Hin.
  - destruct (nt_eq_dec x' x); subst; auto.
    destruct Hin as [Heq | Hin]; subst; auto.
Qed.

Definition rhsLengths (g : grammar) : list nat :=
  map (fun rhs => List.length rhs) (rhss g).

Lemma rhss_rhsLengths_in :
  forall g rhs,
    In rhs (rhss g)
    -> In (List.length rhs) (rhsLengths g).
Proof.
  intros g rhs Hin; induction g as [| (x, rhs') ps IH];
  simpl in *; inv Hin; auto.
Qed.

Definition maxRhsLength (g : grammar) : nat :=
  listMax (rhsLengths g).

Lemma grammar_rhs_length_le_max :
  forall g x rhs,
    In rhs (rhssForNt g x)
    -> List.length rhs <= maxRhsLength g.
Proof.
  intros; unfold maxRhsLength.
  apply listMax_in_le.
  apply rhss_rhsLengths_in.
  eapply rhssForNt_rhss; eauto.
Qed.

Lemma grammar_rhs_length_lt_max_plus_1 :
  forall g x rhs,
    In rhs (rhssForNt g x)
    -> List.length rhs < 1 + maxRhsLength g.
Proof.
  intros g x rhs Hin.
  apply grammar_rhs_length_le_max in Hin; omega.
Qed.

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Lemma fromNtList_in_iff :
  forall (x : nonterminal)
         (l : list nonterminal), 
    In x l <-> NtSet.In x (fromNtList l).
Proof.
  intros x l; split; intro hi; induction l as [| x' l IH]; sis; try ND.fsetdec.
  - destruct hi as [hh | ht]; subst; auto.
    + ND.fsetdec.
    + apply IH in ht; ND.fsetdec.
  - destruct (NF.eq_dec x' x); subst; auto.
    right; apply IH; ND.fsetdec.
Qed.

Definition allNts (g : grammar) : NtSet.t := 
  fromNtList (lhss g).

Lemma allNts_lhss_iff :
  forall (g : grammar) (x : nonterminal),
    In x (lhss g)
    <-> NtSet.In x (allNts g).
Proof.
  intros g x; split; intros hi; apply fromNtList_in_iff; auto.
Qed.

Lemma lhs_mem_allNts_true :
  forall g x ys,
    In (x, ys) g
    -> NtSet.mem x (allNts g) = true.
Proof.
  intros g x ys hi.
  apply NtSet.mem_spec.
  apply allNts_lhss_iff. 
  eapply production_lhs_in_lhss; eauto.
Qed.

(* Definitions related to input that the parser consumes. *)
Definition literal := string.

Definition token   := (terminal * literal)% type.

(* Parser return values *)
Inductive tree    := Leaf : literal -> tree
                   | Node : nonterminal -> list tree -> tree.

Definition forest := list tree.

(* Grammar locations *)
Record location := Loc { lopt : option nonterminal
                       ; rpre : list symbol
                       ; rsuf : list symbol
                       }.

(* Grammatical derivation relation *)
Inductive sym_derivation (g : grammar) : symbol -> list token -> tree -> Prop :=
| T_der  : 
    forall (a : terminal) (l : literal),
      sym_derivation g (T a) [(a, l)] (Leaf l)
| NT_der : 
    forall (x  : nonterminal) (ys : list symbol) (w : list token) (sts : forest),
      In (x, ys) g
      -> gamma_derivation g ys w sts
      -> sym_derivation g (NT x) w (Node x sts)
with gamma_derivation (g : grammar) : list symbol -> list token-> forest-> Prop :=
     | Nil_der  : 
         gamma_derivation g [] [] []
     | Cons_der : 
         forall (s : symbol) (ss : list symbol) (wpre wsuf : list token) 
                (tr : tree) (trs : list tree),
           sym_derivation g s wpre tr
           -> gamma_derivation g ss wsuf trs
           -> gamma_derivation g (s :: ss) (wpre ++ wsuf) (tr :: trs).

Hint Constructors sym_derivation gamma_derivation.

Scheme sym_derivation_mutual_ind   := Induction for sym_derivation Sort Prop
  with gamma_derivation_mutual_ind := Induction for gamma_derivation Sort Prop.

Lemma gamma_derivation_app' :
  forall g ys1 w1 v1,
    gamma_derivation g ys1 w1 v1
    -> forall ys2 w2 v2,
      gamma_derivation g ys2 w2 v2
      -> gamma_derivation g (ys1 ++ ys2) (w1 ++ w2) (v1 ++ v2).
Proof.
  intros g ys1 w1 v1 hg.
  induction hg; intros ys2 w2 v2 hg2; simpl in *; auto.
  rewrite <- app_assoc; constructor; auto.
Qed.

Lemma gamma_derivation_app :
  forall g ys ys' w w' v v',
    gamma_derivation g ys w v
    -> gamma_derivation g ys' w' v'
    -> gamma_derivation g (ys ++ ys') (w ++ w') (v ++ v').
Proof.
  intros; eapply gamma_derivation_app'; eauto.
Qed.

Lemma forest_app_singleton_node : 
  forall g x ys ys' w w' v v',
    In (x, ys') g
    -> gamma_derivation g ys w v
    -> gamma_derivation g ys' w' v'
    -> gamma_derivation g (ys ++ [NT x]) (w ++ w') (v ++ [Node x v']).
Proof.
  intros g x ys ys' w w' v v' hi hg hg'.
  apply gamma_derivation_app; auto.
  rew_nil_r w'; eauto.
Qed.

Lemma terminal_head_gamma_derivation :
  forall g a l ys w v,
    gamma_derivation g ys w v
    -> gamma_derivation g (T a :: ys) ((a, l) :: w) (Leaf l :: v).
Proof.
  intros g a l ys w v hg.
  assert (happ : (a, l) :: w = [(a, l)] ++ w) by apply cons_app_singleton.
  rewrite happ; auto.
Qed.

Lemma gamma_derivation_split :
  forall g ys ys' w'' v'',
    gamma_derivation g (ys ++ ys') w'' v''
    -> exists w w' v v',
      w'' = w ++ w'
      /\ v'' = v ++ v'
      /\ gamma_derivation g ys  w  v
      /\ gamma_derivation g ys' w' v'.
Proof.
  intros g ys; induction ys as [| y ys IH]; intros ys' w'' v'' hg; sis.
  - exists []; exists w''; exists []; exists v''; repeat split; auto.
  - inversion hg as [| s ss wpre wsuf t f hs hg']; subst; clear hg. 
    apply IH in hg'; destruct hg' as [w [w' [v [v' [? [? [hg' hg'']]]]]]]; subst.
    exists (wpre ++ w); exists w'; exists (t :: v); exists v'. 
    repeat split; auto; apps.
Qed.

Lemma gamma_derivation_terminal_end :
  forall g ys a w v,
    gamma_derivation g (ys ++ [T a]) w v
    -> exists w_front l v_front,
      w = w_front ++ [(a, l)]
      /\ v = v_front ++ [Leaf l]
      /\ gamma_derivation g ys w_front v_front.
Proof.
  intros g ys a w v hg.
  eapply gamma_derivation_split in hg.
  destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
  inv hg'.
  (* lemma *)
  inv H1. inv H4.
  repeat eexists; eauto.
Qed.

Lemma gamma_derivation_nonterminal_end :
  forall g ys x w v,
    gamma_derivation g (ys ++ [NT x]) w v
    -> exists wpre wsuf vpre v',
      w = wpre ++ wsuf
      /\ v = vpre ++ [Node x v']
      /\ gamma_derivation g ys wpre vpre
      /\ sym_derivation g (NT x) wsuf (Node x v').
Proof.
  intros g ys x w v hg.
  eapply gamma_derivation_split in hg.
  destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
  inv hg'.
  (* lemma *)
  inv H4. rewrite app_nil_r in *.
  inv H1.
  repeat eexists; eauto.
Qed.  

Definition unique_gamma_derivation g ss w v :=
  gamma_derivation g ss w v
  /\ forall v', gamma_derivation g ss w v' -> v = v'.

Inductive sym_recognize (g : grammar) : symbol -> list token -> Prop :=
| T_rec  : 
    forall (a : terminal) (l : literal),
      sym_recognize g (T a) [(a, l)]
| NT_rec : 
    forall (x  : nonterminal) (ys : list symbol) (w : list token),
      In (x, ys) g
      -> gamma_recognize g ys w
      -> sym_recognize g (NT x) w
with gamma_recognize (g : grammar) : list symbol -> list token -> Prop :=
     | Nil_rec  : 
         gamma_recognize g [] []
     | Cons_rec : 
         forall (s : symbol) (ss : list symbol) (wpre wsuf : list token),
           sym_recognize g s wpre
           -> gamma_recognize g ss wsuf
           -> gamma_recognize g (s :: ss) (wpre ++ wsuf).

Hint Constructors sym_recognize gamma_recognize.

Scheme sym_recognize_mutual_ind   := Induction for sym_recognize Sort Prop
  with gamma_recognize_mutual_ind := Induction for gamma_recognize Sort Prop.

Lemma gamma_recognize_terminal_head :
  forall g a suf w,
    gamma_recognize g (T a :: suf) w
    -> exists l w',
      w = (a, l) :: w'
      /\ gamma_recognize g suf w'.
Proof.
  intros g a suf w hg.
  inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
  inv hs; simpl; eauto.
Qed.

Lemma gamma_recognize_nonterminal_head :
  forall g x suf w,
    gamma_recognize g (NT x :: suf) w
    -> exists rhs wpre wsuf,
      w = wpre ++ wsuf
      /\ In (x, rhs) g
      /\ gamma_recognize g rhs wpre
      /\ gamma_recognize g suf wsuf.
Proof.
  intros g x suf w hg.
  inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
  inv hs; simpl; eauto 8.
Qed.

Lemma gamma_recognize_app' :
  forall g ys1 w1,
    gamma_recognize g ys1 w1
    -> forall ys2 w2,
      gamma_recognize g ys2 w2
      -> gamma_recognize g (ys1 ++ ys2) (w1 ++ w2).
Proof.
  intros g ys1 w1 hg.
  induction hg; intros ys2 w2 hg2; simpl in *; auto.
  rewrite <- app_assoc; constructor; auto.
Qed.

Lemma gamma_recognize_app :
  forall g ys1 ys2 w1 w2,
    gamma_recognize g ys1 w1
    -> gamma_recognize g ys2 w2
    -> gamma_recognize g (ys1 ++ ys2) (w1 ++ w2).
Proof.
  intros; apply gamma_recognize_app'; auto.
Qed.

Lemma gamma_recognize_split :
  forall g ys ys' w'',
    gamma_recognize g (ys ++ ys') w''
    -> exists w w',
      w'' = w ++ w'
      /\ gamma_recognize g ys w
      /\ gamma_recognize g ys' w'.
Proof.
  intros g ys; induction ys as [| y ys IH]; intros ys' w'' hg; sis.
  - exists []; exists w''; repeat split; auto.
  - inversion hg as [| s ss wpre wsuf hs hg']; subst; clear hg. 
    apply IH in hg'; destruct hg' as [w [w' [? [hg' hg'']]]]; subst.
    exists (wpre ++ w); exists w'; repeat split; auto; apps.
Qed.

(* Inductive definition of a nullable grammar symbol *)
Inductive nullable_sym (g : grammar) : symbol -> Prop :=
| NullableSym : forall x ys,
    In (x, ys) g
    -> nullable_gamma g ys
    -> nullable_sym g (NT x)
with nullable_gamma (g : grammar) : list symbol -> Prop :=
     | NullableNil  : nullable_gamma g []
     | NullableCons : forall hd tl,
         nullable_sym g hd
         -> nullable_gamma g tl
         -> nullable_gamma g (hd :: tl).

Hint Constructors nullable_sym nullable_gamma.

Lemma nullable_split :
  forall g xs ys,
    nullable_gamma g (xs ++ ys)
    -> nullable_gamma g xs /\ nullable_gamma g ys.
Proof.
  intros g xs; induction xs as [| x xs IH]; intros ys hn; sis; auto.
  inv hn; firstorder.
Qed.

Lemma nullable_split_l :
  forall g xs ys,
    nullable_gamma g (xs ++ ys)
    -> nullable_gamma g ys.
Proof.
  intros g xs ys hn; apply nullable_split in hn; firstorder.
Qed.

Lemma nullable_app :
  forall g xs ys,
    nullable_gamma g xs
    -> nullable_gamma g ys
    -> nullable_gamma g (xs ++ ys).
Proof.
  intros g xs ys hng hng'.
  induction xs as [| x xs]; sis; inv hng; auto.
Qed.

Inductive nullable_path (g : grammar) :
  symbol -> symbol -> Prop :=
| DirectPath : forall x z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT z :: suf
    -> nullable_gamma g pre
    -> nullable_path g (NT x) (NT z)
| IndirectPath : forall x y z gamma pre suf,
    In (x, gamma) g
    -> gamma = pre ++ NT y :: suf
    -> nullable_gamma g pre
    -> nullable_path g (NT y) (NT z)
    -> nullable_path g (NT x) (NT z).

Hint Constructors nullable_path.

Lemma nullable_path_trans :
  forall g x y z,
    nullable_path g x y
    -> nullable_path g y z
    -> nullable_path g x z.
Proof.
  intros g x y z hxy hyz.
  induction hxy; sis; subst.
  - destruct z as [a | z]; eauto.
    inv hyz.
  - destruct z as [a | z]; eauto.
    inv hyz.
Qed.  

Definition left_recursive g sym :=
  nullable_path g sym sym.

Definition no_left_recursion g :=
  forall (x : nonterminal), 
    ~ left_recursive g (NT x).


(* May not be necessary *)
Inductive gamma_recognize' (g : grammar) : list symbol -> list token -> Prop :=
| Nil_gr :
    gamma_recognize' g [] []
| T_gr   : 
    forall ys wsuf a l,
      gamma_recognize' g ys wsuf
      -> gamma_recognize' g (T a :: ys) ((a, l) :: wsuf)
| NT_gr  : 
    forall x ys ys' wpre wsuf,
      In (x, ys) g
      -> gamma_recognize' g ys  wpre
      -> gamma_recognize' g ys' wsuf
      -> gamma_recognize' g (NT x :: ys') (wpre ++ wsuf).

