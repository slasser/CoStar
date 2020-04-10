Require Import FMaps List MSets Omega PeanoNat String.
Require Import GallStar.Tactics.
Require Import GallStar.Utils.
Import ListNotations.

(* Types of grammar symbols; the user provides these at grammar definition time *)
Module Type SYMBOL_TYPES.

  Parameters terminal nonterminal : Type.
  
  Hypothesis t_eq_dec : forall a a' : terminal,
      {a = a'} + {a <> a'}.
  
  Hypothesis nt_eq_dec : forall x x' : nonterminal,
      {x = x'} + {x <> x'}.

  Parameter showT  : terminal    -> string.
  Parameter showNT : nonterminal -> string.
  
End SYMBOL_TYPES.

(* Core definitions, parameterized by grammar symbol types *)
Module DefsFn (Export Ty : SYMBOL_TYPES).

  Definition t_eq_dec  := Ty.t_eq_dec.
  Definition nt_eq_dec := Ty.nt_eq_dec.

  Definition beqNt (x x' : nonterminal) : bool :=
    match nt_eq_dec x' x with
    | left _  => true
    | right _ => false
    end.

  Definition beqT (a a' : terminal) : bool :=
    match t_eq_dec a' a with
    | left _  => true
    | right _ => false
    end.

  Inductive symbol := T  : terminal -> symbol 
                    | NT : nonterminal -> symbol.

  Lemma symbol_eq_dec : forall s s' : symbol,
      {s = s'} + {s <> s'}.
  Proof. 
    decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Defined.

  Lemma gamma_eq_dec :
    forall gamma gamma' : list symbol,
      {gamma = gamma'} + {gamma <> gamma'}.
  Proof. 
    decide equality. apply symbol_eq_dec. 
  Defined.

  Definition beqGamma (xs ys : list symbol) : bool :=
    if gamma_eq_dec xs ys then true else false.

  Lemma beqGamma_eq_iff :
    forall xs ys, beqGamma xs ys = true <-> xs = ys.
  Proof.
    unfold beqGamma; split; intros; dms; tc. 
  Qed.

  (* Finite sets of nonterminals *)
  Module MDT_NT.
    Definition t      := nonterminal.
    Definition eq_dec := Ty.nt_eq_dec.
  End MDT_NT.
  Module NT_as_DT     := Make_UDT(MDT_NT).
  Module NtSet        := MSetWeakList.Make NT_as_DT.
  Module Export NF    := WFactsOn NT_as_DT NtSet.
  Module Export NP    := MSetProperties.Properties NtSet.
  Module Export NE    := EqProperties NtSet.
  Module Export ND    := WDecideOn NT_as_DT NtSet.

  (* Hide an alternative definition of "sum" from NtSet *)
  Definition sum := Datatypes.sum.

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
      if Ty.nt_eq_dec x' x then 
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
      destruct (Ty.nt_eq_dec x' x); subst; auto.
      inv hi; auto.
    - induction g as [| (x', ys') g]; sis; tc.
      destruct hi as [heq | hi].
      + inv heq.
        destruct (Ty.nt_eq_dec x x); tc.
        apply in_eq.
      + destruct (Ty.nt_eq_dec x' x); subst; auto.
        apply in_cons; auto.
  Qed.
  Hint Resolve rhssForNt_in_iff : core.

  Lemma rhssForNt_rhss :
    forall g x rhs,
      In rhs (rhssForNt g x) -> In rhs (rhss g).
  Proof.
    intros g x rhs Hin; induction g as [| (x', rhs') ps IH]; simpl in *.
    - inv Hin.
    - destruct (Ty.nt_eq_dec x' x); subst; auto.
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
      In (x, rhs) g
      -> List.length rhs <= maxRhsLength g.
  Proof.
    intros; unfold maxRhsLength.
    apply listMax_in_le.
    apply rhss_rhsLengths_in.
    eapply rhssForNt_rhss.
    eapply rhssForNt_in_iff; eauto.
  Qed.

  Lemma grammar_rhs_length_lt_max_plus_1 :
    forall g x rhs,
      In (x, rhs) g
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
  Inductive tree    := Leaf : terminal -> literal -> tree
                     | Node : nonterminal -> list tree -> tree.

  Definition forest := list tree.

  (* Parser stacks *)
  Inductive prefix_frame :=
  | PF : list symbol -> forest -> prefix_frame.

  Definition prefix_stack := (prefix_frame * list prefix_frame)%type.

  Inductive suffix_frame :=
  | SF : option nonterminal -> list symbol -> suffix_frame.

  Lemma suffix_frame_eq_dec :
    forall fr fr' : suffix_frame, {fr = fr'} + {fr <> fr'}.
  Proof.
    repeat decide equality; try apply t_eq_dec; try apply nt_eq_dec.
  Qed.

  (* Finite sets and maps for suffix frames *)
  Module MDT_SF.
    Definition t       := suffix_frame.
    Definition eq_dec  := suffix_frame_eq_dec.
  End MDT_SF.
  Module SF_as_DT      := Make_UDT(MDT_SF).
  Module FrameSet      := MSetWeakList.Make SF_as_DT.
  Module FrameSetFacts := WFactsOn SF_as_DT FrameSet.
  Module FrameMap      := FMapWeakList.Make SF_as_DT.
  Module FrameMapFacts := WFacts_fun SF_as_DT FrameMap.
  Module FS            := FrameSet.
  Module FM            := FrameMap.
  Module FMF           := FrameMapFacts.
  
  Definition suffix_stack := (suffix_frame * list suffix_frame)%type. 

  Fixpoint unprocTailSyms (frs : list suffix_frame) : list symbol :=
    match frs with 
    | []                         => []
    | SF _ [] :: _               => [] (* impossible for a well-formed stack *)
    | SF _ (T _ :: _) :: _       => [] (* impossible for a well-formed stack *)
    | SF _ (NT x :: suf) :: frs' => suf ++ unprocTailSyms frs'
    end.

  Definition unprocStackSyms (stk : suffix_stack) : list symbol :=
    match stk with
    | (SF _ suf, frs) => suf ++ unprocTailSyms frs
    end.

  (*
Definition bottomFramePrefix (p_stk : prefix_stack) : list symbol :=
  match bottomElt p_stk with
  | PF pre _ => pre
  end.

Definition bottomFrameSuffix (s_stk : suffix_stack) : list symbol :=
  match bottomElt s_stk with
  | SF suf => suf
  end.
   *)
  Definition bottomFrameSyms p_stk s_stk := 
    match bottomElt p_stk, bottomElt s_stk with
    | PF pre _, SF _ suf => rev pre ++ suf
    end.

  (* Grammatical derivation relation *)
  Inductive sym_derivation (g : grammar) : symbol -> list token -> tree -> Prop :=
  | T_der  : 
      forall (a : terminal) (l : literal),
        sym_derivation g (T a) [(a, l)] (Leaf a l)
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

  Hint Constructors sym_derivation gamma_derivation : core.

  Scheme sym_derivation_mutual_ind   := Induction for sym_derivation Sort Prop
    with gamma_derivation_mutual_ind := Induction for gamma_derivation Sort Prop.

  Ltac inv_sd hs  hi hg:=
    inversion hs as [ ? ? | ? ? ? ? hi hg]; subst; clear hs.

  Ltac inv_gd hg  hs hg' :=
    inversion hg as [| ? ? ? ? ? ? hs hg']; subst; clear hg.

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
      -> gamma_derivation g (T a :: ys) ((a, l) :: w) (Leaf a l :: v).
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
        /\ v = v_front ++ [Leaf a l]
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

  Lemma trees_eq__gammas_eq_words_eq' :
    forall g ys w v,
      gamma_derivation g ys w v
      -> forall ys' w',
        gamma_derivation g ys' w' v
        -> ys' = ys /\ w' = w.
  Proof.
    intros g ys w v hg.
    induction hg using gamma_derivation_mutual_ind with
        (P := fun s w t (hs : sym_derivation g s w t) =>
                forall s' w',
                  sym_derivation g s' w' t
                  -> s' = s /\ w' = w).
    - intros s' w' hs; inv hs; auto.
    - intros s' w' hs; inv hs; firstorder.
    - intros ys' w' hg; inv hg; auto.
    - intros ys' w' hg'; inv hg'.
      apply IHhg in H3; destruct H3; subst.
      apply IHhg0 in H4; destruct H4; subst; auto.
  Qed.

  Lemma trees_eq__gammas_eq_words_eq :
    forall g ys ys' w w' v,
      gamma_derivation g ys w v
      -> gamma_derivation g ys' w' v
      -> ys' = ys /\ w' = w.
  Proof.
    intros; eapply trees_eq__gammas_eq_words_eq'; eauto.
  Qed.

  Lemma gamma_derivation_singleton_t :
    forall g a w v,
      gamma_derivation g [T a] w v
      -> exists l,
        w = [(a, l)]
        /\ v = [Leaf a l].
  Proof.
    intros g a w v hg.
    inv_gd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
  Qed.

  Lemma gamma_derivation_singleton_nt :
    forall g x w v,
      gamma_derivation g [NT x] w v
      -> exists ys v',
        In (x, ys) g
        /\ v = [Node x v']
        /\ gamma_derivation g ys w v'.
  Proof.
    intros g x w v hg.
    inv_gd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
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

  Hint Constructors sym_recognize gamma_recognize : core.

  Ltac inv_sr hs  hi hg :=
    inversion hs as [ ? ? | ? ? ? hi hg ]; subst; clear hs.

  Ltac inv_gr hg  wpre wsuf hs hg' :=
    inversion hg as [| ? ? wpre wsuf hs hg']; subst; clear hg.

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

  Lemma gamma_recognize_fold_head_nt :
    forall g x rhs ys ts,
      In (x, rhs) g
      -> gamma_recognize g (rhs ++ ys) ts
      -> gamma_recognize g (NT x :: ys) ts.
  Proof.
    intros g x rhs ys ts hi hr.
    apply gamma_recognize_split in hr.
    destruct hr as [w [w' [? [hr hr']]]]; subst; eauto.
  Qed.

  Lemma gamma_derivation__gamma_recognize :
    forall g ys w v,
      gamma_derivation g ys w v
      -> gamma_recognize g ys w.
  Proof.
    intros g ys w v hg.
    induction hg using gamma_derivation_mutual_ind with
        (P := fun s w t (hs : sym_derivation g s w t) => 
                sym_recognize g s w); eauto.
  Qed.

  Lemma gamma_recognize__exists_gamma_derivation :
    forall g ys w,
      gamma_recognize g ys w
      -> exists v,
        gamma_derivation g ys w v.
  Proof.
    intros g ys w hg.
    induction hg using gamma_recognize_mutual_ind with
        (P := fun s w (hs : sym_recognize g s w) => 
                exists t, sym_derivation g s w t); firstorder; eauto.
    repeat econstructor; eauto.
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

  Hint Constructors nullable_sym nullable_gamma : core.

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

  Hint Constructors nullable_path : core.

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

End DefsFn.

Module Type DefsT (SymTy : SYMBOL_TYPES).
  Include DefsFn SymTy.
End DefsT.

Module Type T.
  Declare Module SymTy : SYMBOL_TYPES.
  Declare Module Defs  : DefsT SymTy.
  Export SymTy.
  Export Defs.
End T.
