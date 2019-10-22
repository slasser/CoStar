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

Lemma t_eq_dec : forall a a' : terminal,
    {a = a'} + {a <> a'}.
Proof. repeat decide equality. Defined.

Lemma nt_eq_dec : forall x x' : nonterminal,
    {x = x'} + {x <> x'}.
Proof. decide equality. Defined.

Lemma gamma_eq_dec : forall gamma gamma' : list symbol,
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

Definition rhs (p : production) : list symbol :=
  let (_, gamma) := p in gamma.

Definition rhss (g : grammar) : list (list symbol) :=
  map rhs g.

Definition rhsLengths (g : grammar) : list nat :=
  map (fun rhs => List.length rhs) (rhss g).

Definition maxRhsLength (g : grammar) : nat :=
  listMax (rhsLengths g).

Fixpoint rhssForNt (ps : list production) (x : nonterminal) : list (list symbol) :=
  match ps with
  | []                 => []
  | (x', gamma) :: ps' => 
    if nt_eq_dec x' x then 
      gamma :: rhssForNt ps' x
    else 
      rhssForNt ps' x
  end.

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition allNts (g : grammar) : NtSet.t := 
  fromNtList (lhss g).

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

Inductive nullable_gamma' (g : grammar) : list symbol -> Prop :=
| NullableNil'  : 
    nullable_gamma' g []
| NullableCons' : 
    forall x ys tl,
      In (x, ys) g
      -> nullable_gamma' g ys
      -> nullable_gamma' g tl
      -> nullable_gamma' g (NT x :: tl).

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

Definition left_recursive g sym :=
  nullable_path g sym sym.

Definition no_left_recursion g :=
  forall (x : nonterminal), 
    ~ left_recursive g (NT x).

(* LEMMAS *)

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

Lemma gamma_derivation_app :
  forall g ys1 w1 v1,
    gamma_derivation g ys1 w1 v1
    -> forall ys2 w2 v2,
      gamma_derivation g ys2 w2 v2
      -> gamma_derivation g (ys1 ++ ys2) (w1 ++ w2) (v1 ++ v2).
Proof.
  intros g ys1 w1 v1 hg.
  induction hg; intros ys2 w2 v2 hg2; simpl in *; auto.
  rewrite <- app_assoc.
  constructor; auto.
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

Lemma in_list_iff_in_fromNtList :
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

Lemma in_lhss_iff_in_allNts :
  forall (g : grammar) (x : nonterminal),
    In x (lhss g)
    <-> NtSet.In x (allNts g).
Proof.
  intros g x; split; intros hi; apply in_list_iff_in_fromNtList; auto.
Qed.

Lemma in_rhssForNt_production_in_grammar :
  forall g x ys,
    In ys (rhssForNt g x)
    -> In (x, ys) g.
Proof.
  intros g x ys hin.
  induction g as [| (x', ys') g]; sis; tc.
  destruct (nt_eq_dec x' x); subst; auto.
  inv hin; auto.
Qed.

Lemma rhs_in_grammar_length_in_rhsLengths :
  forall g rhs,
    In rhs (rhss g) -> In (List.length rhs) (rhsLengths g).
Proof.
  intros g rhs Hin; induction g as [| (x, rhs') ps IH];
  simpl in *; inv Hin; auto.
Qed.

Lemma in_rhssForNt_in_rhss :
  forall g x rhs,
    In rhs (rhssForNt g x) -> In rhs (rhss g).
Proof.
  intros g x rhs Hin; induction g as [| (x', rhs') ps IH]; simpl in *.
  - inv Hin.
  - destruct (nt_eq_dec x' x); subst; auto.
    destruct Hin as [Heq | Hin]; subst; auto.
Qed.
  
Lemma grammar_rhs_length_le_max :
  forall g x rhs,
    In rhs (rhssForNt g x) -> List.length rhs <= maxRhsLength g.
Proof.
  intros; unfold maxRhsLength.
  apply listMax_in_le.
  apply rhs_in_grammar_length_in_rhsLengths.
  eapply in_rhssForNt_in_rhss; eauto.
Qed.

Lemma grammar_rhs_length_lt_max_plus_1 :
  forall g x rhs,
    In rhs (rhssForNt g x) -> List.length rhs < 1 + maxRhsLength g.
Proof.
  intros g x rhs Hin.
  apply grammar_rhs_length_le_max in Hin; omega.
Qed.
