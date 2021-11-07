Require Import FSets FSets.FMapAVL List Omega String.
Require Import CoLoR.Util.FGraph.TransClos.
Require Import CoStar.Orders.
Require Import CoStar.Tactics.
Require Import CoStar.Utils.
Import ListNotations.

(* Types of grammar symbols; the user provides these at grammar definition time *)
Module Type SYMBOL_TYPES.

  Parameters terminal nonterminal : Type.

  Parameter compareT : terminal -> terminal -> comparison.

  Parameter compareT_eq :
    forall x y : terminal,
      compareT x y = Eq <-> x = y. 

  Parameter compareT_trans :
    forall (c : comparison) (x y z : terminal),
      compareT x y = c -> compareT y z = c -> compareT x z = c.

  Parameter compareNT : nonterminal -> nonterminal -> comparison.

  Parameter compareNT_eq :
    forall x y : nonterminal,
      compareNT x y = Eq <-> x = y. 

  Parameter compareNT_trans :
    forall (c : comparison) (x y z : nonterminal),
      compareNT x y = c -> compareNT y z = c -> compareNT x z = c.
  
  Parameter showT  : terminal    -> string.
  Parameter showNT : nonterminal -> string.

  Parameter t_semty  : terminal    -> Type.
  Parameter nt_semty : nonterminal -> Type.
  
End SYMBOL_TYPES.

(* Core definitions, parameterized by grammar symbol types *)
Module DefsFn (Export Ty : SYMBOL_TYPES).

  (* Terminal symbols as a usual ordered type *)
  
  Module T_as_UCT <: UsualComparableType.
    Definition t             := terminal.
    Definition compare       := compareT.
    Definition compare_eq    := compareT_eq.
    Definition compare_trans := compareT_trans.
  End T_as_UCT.

  Module T_as_UOT <: UsualOrderedType := UOT_from_UCT T_as_UCT.
  
  (* Nonterminal symbols as a usual ordered type *)

  Module NT_as_UCT <: UsualComparableType.
    Definition t             := nonterminal.
    Definition compare       := compareNT.
    Definition compare_eq    := compareNT_eq.
    Definition compare_trans := compareNT_trans.
  End NT_as_UCT.
    
  Module NT_as_UOT <: UsualOrderedType := UOT_from_UCT NT_as_UCT.

  (* Equality tests for terminals and nonterminals *)
  
  Definition t_eq_dec  := T_as_UOT.eq_dec.
  Definition nt_eq_dec := NT_as_UOT.eq_dec.

  Definition beqT (a a' : terminal) : bool :=
    match t_eq_dec a' a with
    | left _  => true
    | right _ => false
    end.
  
  Definition beqNt (x x' : nonterminal) : bool :=
    match nt_eq_dec x' x with
    | left _  => true
    | right _ => false
    end.

  Lemma t_semty_inj :
    forall (a : terminal) (v v' : t_semty a),
      @existT _ _ a v = @existT _ _ a v'
      -> v = v'.
  Proof.
    intros a v v' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply t_eq_dec.
  Qed.

  Ltac t_inj :=
    match goal with
    | H : @existT _ _ ?a ?v = @existT _ _ ?a ?v' |- _ =>
      apply t_semty_inj in H; subst
    end.

  (* Finite sets of nonterminals *)

  Module NtSet      := FSetList.Make NT_as_UOT.
  Module Export NF  := FSetFacts.Facts NtSet.
  Module Export NP  := FSetProperties.Properties NtSet.
  Module Export NE  := FSetEqProperties.EqProperties NtSet.
  Module Export ND  := FSetDecide.Decide NtSet.
  (* hide an alternative definition of "sum" from NtSet *)
  Definition sum := Datatypes.sum.

  Definition fromNtList (ls : list nonterminal) : NtSet.t :=
    fold_right NtSet.add NtSet.empty ls.

  Lemma fromNtList_in_iff :
    forall (x : nonterminal)
           (l : list nonterminal), 
      In x l <-> NtSet.In x (fromNtList l).
  Proof.
    intros x l; split; intro hi; induction l as [| x' l Ih]; sis; try ND.fsetdec.
    - destruct hi as [hh | ht]; subst; auto.
      + ND.fsetdec.
      + apply Ih in ht; ND.fsetdec.
    - destruct (NF.eq_dec x' x); subst; auto.
      right; apply Ih; ND.fsetdec.
  Qed.

  (* Grammar symbols *)
  
  Inductive symbol := T  : terminal -> symbol 
                    | NT : nonterminal -> symbol.

  (* The semantic type for symbol s *)  
  Definition symbol_semty (s : symbol) : Type :=
    match s with
    | T a  => t_semty  a
    | NT x => nt_semty x
    end.

  (* Symbols as a usual ordered type *)
  Module Symbol_as_UOT <: UsualOrderedType.
    
    Definition t := symbol.

    Definition eq       := @eq symbol.
    Definition eq_refl  := @eq_refl symbol.
    Definition eq_sym   := @eq_sym symbol.
    Definition eq_trans := @eq_trans symbol.

    Definition lt (x y : symbol) : Prop :=
      match x, y with
      | T a, T b   => T_as_UOT.lt a b
      | T _, NT _  => True
      | NT _, T _  => False
      | NT a, NT b => NT_as_UOT.lt a b
      end.

    Lemma lt_trans :
      forall x y z, lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros x y z hlt hlt'; destruct x as [a | a];
        destruct y as [b | b]; destruct z as [c | c]; try contradiction; auto.
      - eapply T_as_UOT.lt_trans; eauto.
      - eapply NT_as_UOT.lt_trans; eauto.
    Qed.
    
    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros x y hl heq; destruct x as [a | a];
        destruct y as [b | b]; inv heq; auto.
      - eapply T_as_UOT.lt_not_eq; eauto.
      - eapply NT_as_UOT.lt_not_eq; eauto.
    Qed.

    Definition compare (x y : symbol) : Compare lt eq x y.
      refine (match x as x' return x = x' -> _ with
              | T a =>
                fun he => 
                  match y as y' return y = y' -> _ with
                  | T a' =>
                    fun he' => 
                      match T_as_UOT.compare a a' with
                      | LT _ => LT _
                      | GT _ => GT _
                      | EQ _ => EQ _
                      end
                  | NT _ => fun _ => LT _
                  end (eq_refl y)
              | NT b =>
                fun he =>
                  match y as y' return y = y' -> _ with
                  | T _   => fun _ => GT _
                  | NT b' =>
                    fun he' =>
                      match NT_as_UOT.compare b b' with
                      | LT _ => LT _
                      | GT _ => GT _
                      | EQ _ => EQ _
                      end
                  end (eq_refl y)
              end (eq_refl x));
        red; unfold T_as_UOT.eq in *; unfold NT_as_UOT.eq in *; subst; auto.
    Defined.

    Definition eq_dec (x y : symbol) : {x = y} + {x <> y}.
      refine (match x as x' return x = x' -> _ with
              | T a =>
                fun he => 
                  match y as y' return y = y' -> _ with
                  | T a' =>
                    fun he' => 
                      match T_as_UOT.eq_dec a a' with
                      | left _  => left _
                      | right _ => right _
                      end
                  | NT _ => fun _ => right _
                  end (eq_refl y)
              | NT b =>
                fun he =>
                  match y as y' return y = y' -> _ with
                  | T _   => fun _ => right _
                  | NT b' =>
                    fun he' =>
                      match NT_as_UOT.eq_dec b b' with
                      | left _  => left _
                      | right _ => right _
                      end
                  end (eq_refl y)
              end (eq_refl x)); tc.
    Defined.

  End Symbol_as_UOT.

  Lemma symbol_semty_inj :
    forall (x : symbol) (v v' : symbol_semty x),
      @existT _ _ x v = @existT _ _ x v'
      -> v' = v.
  Proof.
    intros x v v' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply Symbol_as_UOT.eq_dec.
  Qed.

  Ltac s_inj :=
    match goal with
    | H : @existT symbol _ _ _ = @existT symbol _ _ _ |- _ =>
      apply symbol_semty_inj in H; subst
    end.

  (* Sequences of symbols (i.e., production right-hand sides) *)
  
  Module Gamma_as_UOT <: UsualOrderedType := List_as_UOT Symbol_as_UOT.

  Definition beqGamma (xs ys : list symbol) : bool :=
    if Gamma_as_UOT.eq_dec xs ys then true else false.

  Lemma beqGamma_eq_iff :
    forall xs ys, beqGamma xs ys = true <-> xs = ys.
  Proof.
    unfold beqGamma; split; intros; dms; tc. 
  Qed.

  (* The semantic type for a list of symbols *)
  Definition symbols_semty (gamma : list symbol) : Type :=
    tuple (List.map symbol_semty gamma).

  Definition cast_ss
             (xs  : list symbol)
             (ys  : list symbol)
             (heq : xs = ys)
             (vs  : symbols_semty xs): symbols_semty ys.
    subst; exact vs.
  Defined.

  Lemma cast_ss_refl :
    forall xs vs (heq : xs = xs),
      cast_ss xs xs heq vs = vs.
  Proof.
    intros xs vs heq.
    unfold cast_ss.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply Gamma_as_UOT.eq_dec.
  Qed.

  Lemma cast_ss_prop_eq :
    forall (xs ys : list symbol)
           (heq   : xs = ys)
           (vs    : symbols_semty xs)
           (vs'   : symbols_semty ys)
           (heq'  : vs' = cast_ss xs ys heq vs)
           (P     : forall (xs : list symbol) (vs : symbols_semty xs), Prop),
      P xs vs -> P ys vs'.
  Proof.
    intros xs ys ? vs vs' ? P hp; subst.
    rewrite cast_ss_refl; auto.
  Qed.

  Lemma cast_ss_ins_trans :
    forall xs ys zs (heq : xs = zs) (heq' : ys = zs) (heq'' : xs = ys) vs,
      cast_ss xs zs heq vs = cast_ss ys zs heq' (cast_ss xs ys heq'' vs).
  Proof.
    intros xs ys zs ? ? ? vs; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  Lemma cast_ss_roundtrip :
    forall xs ys (heq : xs = ys) (heq' : ys = xs) vs,
      cast_ss ys xs heq' (cast_ss xs ys heq vs) = vs.
  Proof.
    intros xs ys heq heq' vs; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  Lemma cast_ss_cons :
    forall x ys zs (heq : (x :: ys) = (x :: zs)) v (vs : symbols_semty ys),
      (exists (heq' : ys = zs),
          cast_ss (x :: ys) (x :: zs) heq (v, vs) =
          (v, cast_ss ys zs heq' vs)).
  Proof.
    intros x ys zs heq v vs.
    pose proof heq as heq'; inv heq'.
    exists eq_refl.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  Lemma cast_elim_common :
    forall xs ys zs (heq : xs = zs) (heq' : ys = zs) (heq'' : xs = ys) vs vs',
      vs' = cast_ss _ _ heq'' vs
      -> cast_ss _ _ heq vs = cast_ss _ _ heq' vs'.
  Proof.
    intros xs ys zs heq heq' heq'' vs vs' heq'''; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.
  
  Lemma symbols_semty_inj :
    forall (ys : list symbol) (vs vs' : symbols_semty ys),
      @existT _ _ ys vs' = @existT _ _ ys vs
      -> vs' = vs.
  Proof.
    intros ys vs vs' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply Gamma_as_UOT.eq_dec.
  Qed.

  Ltac ss_inj :=
    match goal with
    | H : @existT (list symbol) _ ?ys ?vs = @existT (list symbol) _ ?ys ?vs' |- _ =>
      apply symbols_semty_inj in H; subst
    end.
  
  Definition concatTuple_nil_case :
    forall (xs ys : list symbol)
           (vs    : symbols_semty xs)
           (vs'   : symbols_semty ys)
           (heq   : xs = []),
      symbols_semty (xs ++ ys).
    intros xs ys vs vs' heq; subst; auto.
  Defined.

  Definition concatTuple_rec_case :
    forall (x         : symbol)
           (xs' xs ys : list symbol)
           (vs        : symbols_semty xs)
           (vs'       : symbols_semty ys)
           (f         : forall xs ys, symbols_semty xs -> symbols_semty ys -> symbols_semty (xs ++ ys))
           (heq       : xs = x :: xs'),
      symbols_semty (xs ++ ys).
    intros x xs' xs ys vs vs' f heq; subst.
    destruct vs as (v, vs).
    unfold symbols_semty; constructor.
    - exact v.
    - apply f; auto.
  Defined.
  
  Fixpoint concatTuple
             (xs ys : list symbol)
             (vs    : symbols_semty xs)
             (vs'   : symbols_semty ys) : symbols_semty (xs ++ ys) :=
    match xs as xs' return xs = xs' -> _ with
    | []  =>
      fun heq =>
        concatTuple_nil_case xs ys vs vs' heq
    | x :: xs' =>
      fun heq =>
        concatTuple_rec_case x xs' xs ys vs vs' concatTuple heq
    end eq_refl.

  Ltac unct :=
    try unfold concatTuple_nil_case in *;
    try unfold concatTuple_rec_case in *;
    try unfold eq_rect_r            in *; sis.

  Lemma cast_ss_snoc :
    forall ys zs x (heq : ys ++ [x] = zs ++ [x]) (vs : symbols_semty ys) (v : symbol_semty x),
      (exists heq' : ys = zs,
          cast_ss (ys ++ [x]) (zs ++ [x]) heq (concatTuple ys [x] vs (v, tt)) =
          concatTuple zs [x] (cast_ss ys zs heq' vs) (v, tt)).
  Proof.
    intros ys zs x heq vs v.
    pose proof heq as heq'.
    apply app_inj_tail in heq'.
    destruct heq'; subst.
    exists eq_refl.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (* Why does rewriting the goal not work at the end of this proof? *)
  Lemma concatTuple_nil_r :
    forall xs vs (heq : xs = xs ++ []),
      concatTuple xs [] vs tt = cast_ss _ _ heq vs.
  Proof.
    intros xs; induction xs as [| x xs IH]; intros vs heq; sis.
    - destruct vs.
      rewrite cast_ss_refl; auto.
    - destruct vs as (v, vs).
      unfold concatTuple_rec_case.
      unfold eq_rect_r; sis.
      pose proof (cast_ss_cons x xs (xs ++ []) heq v vs) as hc.
      destruct hc as [heq' heq''].
      rewrite <- IH in heq''; auto.
  Qed.

  Lemma concatTuple_assoc :
    forall xs ys zs (heq : (xs ++ ys) ++ zs = xs ++ ys ++ zs) vs vs' vs'',
      concatTuple xs (ys ++ zs) vs (concatTuple ys zs vs' vs'') =
      cast_ss ((xs ++ ys) ++ zs) (xs ++ ys ++ zs) heq (concatTuple (xs ++ ys) zs (concatTuple xs ys vs vs') vs'').
  Proof.
    intros xs; induction xs as [| x xs IH]; intros ys zs heq vs vs' vs''; sis.
    - destruct vs.
      unfold concatTuple_nil_case.
      unfold eq_rect_r; sis.
      rewrite cast_ss_refl; auto.
    - destruct vs as (v, vs).
      unfold concatTuple_rec_case.
      unfold eq_rect_r; sis.
      pose proof (cast_ss_cons x ((xs ++ ys) ++ zs) (xs ++ ys ++ zs) heq v
                               (concatTuple (xs ++ ys) zs (concatTuple xs ys vs vs') vs'')) as hc.
      destruct hc as [heq' heq''].
      rewrite <- IH in heq''; auto.
  Qed.

  Lemma concatTuple_assoc' :
    forall xs ys zs (heq : xs ++ ys ++ zs = (xs ++ ys) ++ zs) vs vs' vs'',
      concatTuple (xs ++ ys) zs (concatTuple xs ys vs vs') vs'' =
      cast_ss (xs ++ ys ++ zs) ((xs ++ ys) ++ zs) heq (concatTuple xs (ys ++ zs) vs (concatTuple ys zs vs' vs'')).
  Proof.
    intros xs ys zs heq vs vs' vs''.
    assert (heq' : (xs ++ ys) ++ zs = xs ++ ys ++ zs) by apps.
    rewrite concatTuple_assoc with (heq := heq').
    rewrite cast_ss_roundtrip; auto.
  Qed.

  Lemma concatTuple_eq :
    forall xs xs' ys ys' (heq : xs = xs') (heq' : ys = ys') (heq'' : xs ++ ys = xs' ++ ys') vx vx' vy vy',
      vx' = cast_ss xs xs' heq vx
      -> vy' = cast_ss ys ys' heq' vy
      -> concatTuple xs' ys' vx' vy' = cast_ss _ _ heq'' (concatTuple xs ys vx vy).
  Proof.
    intros xs xs' ys ys' heq heq' heq'' vx vx' vy vy' h h'; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  Lemma concatTuple_cons_app_singleton :
    forall x xs v vs (heq : [x] ++ xs = x :: xs),
      (v, vs) = cast_ss _ _ heq (concatTuple [x] xs (v, tt) vs).
  Proof.
    intros x xs v vs heq; sis.
    repeat unct.
    rewrite cast_ss_refl; auto.
  Qed.

  Lemma concatTuple_shift_head_l :
    forall s xs ys (heq : (xs ++ [s]) ++ ys = xs ++ s :: ys) v vs vs',
      concatTuple xs (s :: ys) vs (v, vs') =
      cast_ss _ _ heq (concatTuple (xs ++ [s]) ys (concatTuple xs [s] vs (v, tt)) vs').
  Proof.
    intros s xs ys heq v vs vs'.
    erewrite concatTuple_assoc'; sis.
    repeat unct.
    rewrite cast_ss_roundtrip; auto.
    Unshelve.
    all : apps.
  Qed.

  (*
  Lemma concatTuple_app_singleton_cons_eq :
    forall xs xs' s ys ys'
           (heq : xs = xs')
           (heq' : ys = ys')
           (heq'' : (xs' ++ [s]) ++ ys' = xs ++ s :: ys)
           vx vx' v v' vy vy',
      vx' = cast_ss xs xs' heq vx
      -> vy' = cast_ss ys ys' heq' vy
      -> v' = cast_
      -> concatTuple xs (s :: ys) vx (v, vy) = cast_ss _ _ heq'' (concatTuple (xs' ++ [s]) ys' (concatTuple xs' [s] vx' (v' ,tt)) vy').

  Proof.
    intros xs xs' s ys ys' heq heq'

   *)
  
  Definition revTuple_nil_case :
    forall (xs : list symbol)
           (vs : symbols_semty xs)
           (heq : xs = []),
      symbols_semty (rev xs).
    intros; subst; auto.
  Defined.

  Definition revTuple_cons_case :
    forall (xs  : list symbol)
           (x   : symbol)
           (xs' : list symbol)
           (heq : xs = x :: xs')
           (vs  : symbols_semty xs)
           (f   : forall xs, symbols_semty xs -> symbols_semty (rev xs)),
      symbols_semty (rev xs).
    intros xs x xs' heq vs f; subst; sis.
    destruct vs as (v, vs).
    exact (concatTuple (rev xs') [x] (f xs' vs) (v, tt)).
  Defined.

  Fixpoint revTuple (xs : list symbol) (vs : symbols_semty xs) : symbols_semty (rev xs) :=
    match xs as xs' return xs = xs' -> _ with
    | [] => fun heq => revTuple_nil_case xs vs heq 
    | x :: xs' => fun heq => revTuple_cons_case xs x xs' heq vs revTuple
    end eq_refl.

  Ltac unrt :=
    try unfold revTuple_nil_case  in *;
    try unfold revTuple_cons_case in *;
    try unfold eq_rect_r          in *; sis.

  Lemma revTuple_concatTuple_distr :
    forall xs ys (heq : rev ys ++ rev xs = rev (xs ++ ys)) (vs : symbols_semty xs) (vs' : symbols_semty ys),
      revTuple _ (concatTuple _ _ vs vs') =
      cast_ss _ _ heq (concatTuple _ _ (revTuple _ vs') (revTuple _ vs)).
  Proof.
    intros xs; induction xs as [| x xs IH]; intros ys heq vs vs'; sis.
    - destruct vs.
      unfold revTuple_nil_case.
      unfold concatTuple_nil_case.
      unfold eq_rect_r; sis.
      assert (h : rev ys = rev ys ++ []) by auto.
      rewrite concatTuple_nil_r with (heq := h).
      rewrite cast_ss_roundtrip; auto.
    - destruct vs as (v, vs).
      unfold revTuple_cons_case.
      unfold concatTuple_rec_case.
      unfold eq_rect_r; sis.
      assert (h : (rev ys ++ rev xs) ++ [x] = rev ys ++ rev xs ++ [x]).
      { rewrite <- app_assoc; auto. }
      rewrite concatTuple_assoc with (heq := h).
      assert (h' : (rev ys ++ rev xs) ++ [x] = rev (xs ++ ys) ++ [x]) by apps.
      rewrite <- cast_ss_ins_trans with (heq := h').
      pose proof cast_ss_snoc as hs.
      specialize (hs (rev ys ++ rev xs) (rev (xs ++ ys)) x h'
                     (concatTuple _ _ (revTuple _ vs') (revTuple _ vs)) v).
      destruct hs as [heq' heq''].
      rewrite  heq''.
      rewrite <- IH; auto.
  Qed.

  Lemma revTuple_unit :
    forall x xs (heq : x :: rev xs = rev (xs ++ [x])) v vs,
      revTuple (xs ++ [x]) (concatTuple xs [x] vs (v, tt)) =
      cast_ss (x :: rev xs) (rev (xs ++ [x])) heq (v, revTuple _ vs).
  Proof.
    intros x xs heq v vs.
    apply revTuple_concatTuple_distr.
  Qed.
  
  Lemma revTuple_involutive :
    forall xs (heq : xs = rev (rev xs)) (vs : symbols_semty xs),
      revTuple _ (revTuple _ vs) = cast_ss xs (rev (rev xs)) heq vs.
  Proof. intros xs.
    induction xs as [| x xs IH]; intros heq vs; sis.
    - destruct vs.
      unfold cast_ss.
      unfold eq_rect_r.
      rewrite <- Eqdep_dec.eq_rect_eq_dec.
      + unfold revTuple_nil_case.
        unfold eq_rect_r.
        rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
        apply Gamma_as_UOT.eq_dec.
      + apply Gamma_as_UOT.eq_dec.
    - destruct vs.
      unfold revTuple_cons_case.
      unfold eq_rect_r; sis.
      assert (heq' : x :: rev (rev xs) = rev (rev xs ++ [x])).
      { rewrite rev_unit; auto. }
      rewrite revTuple_unit with (xs := rev xs) (heq := heq').
      assert (heq'' : x :: xs = x :: rev (rev xs)).
      { rewrite rev_involutive; auto. }
      rewrite cast_ss_ins_trans with
          (heq := heq) (heq' := heq') (heq'' := heq'').
      pose proof cast_ss_cons as hc.
      specialize (hc x xs (rev (rev xs)) heq'' s t).
      destruct hc as [heq4 heq5].
      rewrite IH with (heq := heq4).
      rewrite <- heq5; auto.
  Qed.

  Lemma rr_anr_expand :
    forall A (xs : list A),
      xs = rev (rev xs) ++ [].
  Proof.
    intros.
    rew_anr.
    rewrite rev_involutive; auto.
  Qed.

  Lemma rr_expand :
    forall A (xs : list A),
      xs = rev (rev xs).
  Proof.
    intros A xs.
    rewrite rev_involutive; auto.
  Qed.

  Lemma anr_expand :
    forall A (xs : list A),
      xs = xs ++ [].
  Proof.
    intros; apps.
  Qed.
  
  Lemma rrt_anr :
    forall xs vs (heq : xs = rev (rev xs) ++ []),
      concatTuple _ [] (revTuple _ (revTuple _ vs)) tt =
      cast_ss xs (rev (rev xs) ++ []) heq vs.
  Proof.
    intros xs vs heq.
    rewrite concatTuple_nil_r with (heq := anr_expand _ (rev (rev xs))).
    rewrite revTuple_involutive with (heq := rr_expand _ xs).
    erewrite <- cast_ss_ins_trans; eauto.
  Qed.
  
  (* Grammar productions *)
  
  Definition production := (nonterminal * list symbol)%type.

  Module Production_as_UOT <: UsualOrderedType := Pair_as_UOT NT_as_UOT Gamma_as_UOT.

  (* Finite maps with productions as keys *)
  Module PM  := FMapAVL.Make Production_as_UOT.
  Module PMF := FMapFacts.Facts PM.

  Lemma pm_mapsto_in :
    forall (p : production)
           (A : Type)
           (a : A)
           (m : PM.t A),
      PM.MapsTo p a m -> PM.In p m.
  Proof.
    intros x A a m hm.
    apply PMF.in_find_iff.
    intros hf.
    apply PMF.find_mapsto_iff in hm; tc.
  Qed.

  Lemma grammar_eq_key_elt_equivalence :
    forall (A : Type),
      Equivalence (PM.eq_key_elt (elt:=A)).
  Proof.
    constructor; try firstorder.
    - intros x y z heq heq'.
      repeat red in heq; repeat red in heq'; repeat red.
      destruct heq as [h1 h2]; destruct heq' as [h3 h4].
      rewrite h1; rewrite h3; rewrite h2; rewrite h4; auto.
  Qed.

  Lemma pm_InA__In :
    forall A x ys e prs,
      InA (PM.eq_key_elt (elt:=A)) ((x, ys), e) prs
      -> In ((x, ys), e) prs.
  Proof.
    intros A x ys e prs hi; induction prs as [| ((x', ys'), e') prs Ih]; sis.
    - inv hi.
    - inversion hi as [pr' prs' heq | pr' prs' hi']; subst; clear hi.
      + repeat red in heq; sis.
        destruct heq as [heq ?]; subst.
        inv heq; auto.
      + right; auto.
  Qed.

  Ltac mapsto_fun heq :=
    match goal with
    | H : PM.MapsTo ?k ?v ?m, H' : PM.MapsTo ?k ?v' ?m |- _ =>
      assert (heq : v = v') by (eapply PMF.MapsTo_fun in H; eauto)
    end.

  Definition lhs' (p : production) : nonterminal :=
    let (x, _) := p in x.

  Definition lhss' (ps : list production) : list nonterminal :=
    map lhs' ps.

  Lemma production_lhs_in_lhss' :
    forall ps x ys,
      In (x, ys) ps
      -> In x (lhss' ps).
  Proof.
    intros ps x ys hi.
    apply in_map_iff.
    exists (x, ys); split; sis; auto.
  Qed.

  Lemma in_lhss'_exists_rhs :
    forall x ps,
      In x (lhss' ps)
      -> exists ys,
        In (x, ys) ps.
  Proof.
    intros x ps hi.
    apply in_map_iff in hi.
    destruct hi as [(x', ys) [? hi]]; sis; subst; eauto.
  Qed.

  Definition rhs' (p : production) : list symbol :=
    let (_, gamma) := p in gamma.

  Definition rhss' (ps : list production) : list (list symbol) :=
    map rhs' ps.

   Fixpoint rhssFor' (ps : list production) (x : nonterminal) : list (list symbol) :=
    match ps with
    | []                 => []
    | (x', gamma) :: ps' => 
      if nt_eq_dec x' x then 
        gamma :: rhssFor' ps' x
      else 
        rhssFor' ps' x
    end.
  
  Lemma rhssFor'_in_iff :
    forall ps x ys,
      In ys (rhssFor' ps x)
      <-> In (x, ys) ps.
  Proof.
    intros g x ys; split; intros hi.
    - induction g as [| (x', ys') g]; sis; tc.
      dm; subst; auto.
      inv hi; auto.
    - induction g as [| (x', ys') g]; sis; tc.
      destruct hi as [heq | hi].
      + inv heq.
        dm; tc.
        apply in_eq.
      + dm; subst; auto. 
        apply in_cons; auto.
  Qed.

  Hint Resolve rhssFor'_in_iff : core.

  Lemma rhssFor'_rhss :
    forall ps x rhs,
      In rhs (rhssFor' ps x) -> In rhs (rhss' ps).
  Proof.
    intros g x rhs Hin; induction g as [| (x', rhs') ps IH]; simpl in *.
    - inv Hin.
    - dm; subst; auto.
      destruct Hin as [Heq | Hin]; subst; auto.
  Qed.

  (* The type of a semantic predicate for a production *)
  Definition predicate_semty (p : production) : Type :=
    let (_, ys) := p in symbols_semty ys -> bool.

  Definition cast_predicate
             (x y  : production)
             (heq  : x = y)
             (p    : predicate_semty x) : predicate_semty y.
    subst; exact p.
  Defined.

    Lemma cast_predicate_refl :
    forall xs (heq : xs = xs) p,
      cast_predicate xs xs heq p = p.
  Proof.
    intros xs heq p.
    unfold cast_predicate.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply Production_as_UOT.eq_dec.
  Qed.

  Lemma cast_predicate_prop_eq :
    forall (x y   : production)
           (heq   : x = y)
           (p     : predicate_semty x)
           (p'    : predicate_semty y)
           (heq'  : p' = cast_predicate x y heq p)
           (P     : forall (x : production) (p : predicate_semty x), Prop),
      P x p -> P y p'.
  Proof.
    intros; subst.
    rewrite cast_predicate_refl; auto.
  Qed.

  Lemma cast_predicate_ins_trans :
    forall x y z (heq : x = z) (heq' : y = z) (heq'' : x = y) p,
      cast_predicate x z heq p = cast_predicate y z heq' (cast_predicate x y heq'' p).
  Proof.
    intros; subst.
    repeat rewrite cast_predicate_refl; auto.
  Qed.

  Lemma cast_predicate_roundtrip :
    forall x y (heq : x = y) (heq' : y = x) p,
      cast_predicate y x heq' (cast_predicate x y heq p) = p.
  Proof.
    intros; subst.
    repeat rewrite cast_predicate_refl; auto.
  Qed.

  Lemma cast_predicate_eq_true :
    forall x ys ys' (heq : ys = ys') (heq' : (x, ys) = (x, ys')) (vs : symbols_semty ys) (vs' : symbols_semty ys') (p : predicate_semty (x, ys)),
      vs' = cast_ss ys ys' heq vs
      -> p vs = true
      -> (cast_predicate (x, ys) (x, ys') heq' p) vs' = true.
  Proof.
    intros x ys ys' heq heq' vs vs' p heq'' hp; subst.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.
  
  (* The type of a semantic action for a production *)
  Definition action_semty (p : production) : Type :=
    let (x, ys) := p in symbols_semty ys -> nt_semty x.

  Definition cast_action
             (x y  : production)
             (heq  : x = y)
             (f    : action_semty x) : action_semty y.
    subst; exact f.
  Defined.

  Lemma cast_action_refl :
    forall x (heq : x = x) f,
      cast_action x x heq f = f.
  Proof.
    intros xs heq p.
    unfold cast_action.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply Production_as_UOT.eq_dec.
  Qed.

  Lemma cast_action_eq :
    forall x ys ys' (heq : ys = ys') (heq' : (x, ys) = (x, ys')) (vs : symbols_semty ys) (vs' : symbols_semty ys') (f : action_semty (x, ys)),
      vs' = cast_ss ys ys' heq vs
      -> f vs = (cast_action _ _ heq' f) vs'.
  Proof.
    intros x ys ys' heq heq' vs vs' f heq''; subst.
    rewrite cast_action_refl.
    rewrite cast_ss_refl; auto.
  Qed.
  
  (* Grammars *)

  (* Each grammar production includes a semantic predicate 
     and a semantic action. The production's symbols
     determine the types of these functions. *)
  Definition production_semty (p : production) : Type :=
    predicate_semty p * action_semty p.

  Definition cast_production_semty
             (p p' : production)
             (heq  : p = p')
             (fs   : production_semty p) : production_semty p'.
    subst; auto.
  Defined.

  Definition grammar_entry : Type :=
    {p : production & production_semty p}.

  
  Lemma inv_grammar_entry_eq :
    forall x ys (p p' : predicate_semty (x, ys)) (f f' : action_semty (x, ys)),
      @existT _ production_semty (x, ys) (p, f) = @existT _ production_semty (x, ys) (p', f')
      -> p = p' /\ f = f'.
  Proof.
    intros x ys p p' f f' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    - inv heq; auto.
    - apply Production_as_UOT.eq_dec.
  Qed.
    
  Definition grammar : Type :=
    PM.t grammar_entry.

  Lemma mapsto_cast  :
    forall (g        : grammar)
           (x x' y z : production)
           (heq      : x = x')
           (heq'     : y = z)
           (p        : predicate_semty y)
           (f        : action_semty y),
      PM.MapsTo x (@existT _ _ y (p, f)) g
      -> PM.MapsTo x' (@existT _ _ z (cast_predicate y z heq' p, cast_action y z heq' f)) g.
  Proof.
    intros g x x' y z heq heq' p f hm; subst.
    rewrite cast_predicate_refl.
    rewrite cast_action_refl; auto.
  Qed.
    
  (* might not be necessary *)
  Definition lhs_in_grammar (x : nonterminal) (g : grammar) : Prop :=
    exists (ys : list symbol), PM.In (x, ys) g.

  Definition productions (g : grammar) : list production :=
    map fst (PM.elements g).

  Lemma in_productions_iff :
    forall g x ys,
      PM.In (x, ys) g <-> In (x, ys) (productions g).
  Proof.
    intros g x ys; split; intros hi.
    - apply in_map_iff.
      apply PMF.elements_in_iff in hi.
      destruct hi as [e hi].
      apply pm_InA__In in hi.
      exists ((x, ys), e); auto.
    - apply in_map_iff in hi.
      destruct hi as [((x',ys'), e) [heq hi]]; sis.
      inv heq.
      apply PMF.elements_in_iff.
      exists e.
      apply In_InA; auto.
      apply grammar_eq_key_elt_equivalence.
  Qed.

  Definition lhss (g : grammar) : list nonterminal :=
    map fst (productions g).

  Lemma production_lhs_in_lhss :
    forall g x ys,
      PM.In (x, ys) g -> In x (lhss g).
  Proof.
    intros g x ys hi.
    apply in_map_iff.
    exists (x, ys).
    split; auto.
    apply in_productions_iff; auto.
  Qed.

  Definition rhss (g : grammar) : list (list symbol) :=
    map snd (productions g).

  Definition allNts (g : grammar) : NtSet.t :=
    fromNtList (lhss g).

  Lemma allNts_lhss_iff :
    forall (g : grammar) (x : nonterminal),
      In x (lhss g)
      <-> NtSet.In x (allNts g).
  Proof.
    intros g x; split; intros hi; apply fromNtList_in_iff; auto.
  Qed.
  
  Definition grammar_wf (g : grammar) : Prop :=
    forall p p' fs, PM.MapsTo p (@existT _ _ p' fs) g -> p = p'.

(*
  Lemma foo :
    forall (gr : grammar) k k' v,
      grammar_wf gr
      -> PM.MapsTo k v gr
      -> k' = k cast_lookup_result
      -> exists (v' : production_semty k'),
          PM.MapsTo k' (@existT _
  Proof.
    intros gr k k' v hm ?; subst; auto.
  Qed.
   *)
  
  (* A well-formed grammar is essentially a dependent map, 
     where the type of each entry (semantic predicate / 
     semantic action pair) depends on the key (production) 
     associated with it. Coq's standard library for finite
     maps does not provide a dependent interface, so we create
     one as follows:

     A well-formed grammar is a finite map in which keys are
     productions, entries are (production, semantic function)
     pairs, and for each key/entry pair, the productions in the
     key and entry are equal. *)
  Definition wf_grammar : Type :=
    {g : grammar | grammar_wf g}.

  (*
  Definition cast_predicate_from_lookup :
    forall (gr   : grammar)
           (x y  : production)
           (p    : predicate_semty y)
           (f    : action_semty y)
           (hw   : grammar_wf gr)
           (hm   : PM.MapsTo x (@existT _ _ y (p, f)) gr),
      predicate_semty x.
    intros g x y p f hw hm. 
    apply hw in hm; subst; auto.
  Defined.
   *)
  
  Lemma predicate_appl_eq_cast :
    forall (x : nonterminal)
           (ys ys' : list symbol)
           (vs : symbols_semty ys)
           (p  : predicate_semty (x, ys))
           (heq : (x, ys) = (x, ys'))
           (heq' : ys = ys'),
      p vs = (cast_predicate (x, ys) (x, ys') heq p) (cast_ss ys ys' heq' vs).
  Proof.
    intros x ys ys' vs p heq heq'.
    subst.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.

  Definition cast_lookup_result :
    forall (gr   : grammar)
           (p p' : production)
           (fs   : production_semty p')
           (hw   : grammar_wf gr)
           (hf   : PM.find p gr = Some (@existT _ _ p' fs)),
      production_semty p.
    intros g p p' fs hw hf.
    apply PMF.find_mapsto_iff in hf.
    apply hw in hf; subst; auto.
  Defined.

  Lemma cast_lookup_result_refl :
    forall gr p fs fs' hw hf,
      cast_lookup_result gr p p fs hw hf = fs'
      -> fs = fs'.
  Proof.
    intros gr p fs fs' hw hf hc.
    unfold cast_lookup_result in hc.
    unfold eq_rect_r in hc.
    unfold eq_sym in hc.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in hc; auto.
    apply PMF.eq_dec.
  Qed.
  
  Lemma in_find_contra :
    forall (p : production)
           (g : grammar),
      PM.In p g
      -> PM.find p g <> None.
  Proof.
    intros p g hi hf.
    eapply PMF.in_find_iff; eauto.
  Defined.

  (* Look up the semantic predicate and action associated
     with a given production *)
  Definition findPredicateAndAction
             (p  : production)
             (g  : grammar)
             (hw : grammar_wf g) : option (production_semty p) :=
    match PM.find p g as o return PM.find p g = o -> _ with
    | Some (@existT _ _ _ fs) =>
      fun hf =>
        Some (cast_lookup_result _ _ _ fs hw hf)
    | None =>
      fun _ =>
        None
    end eq_refl.

  Lemma fpaa_cases' :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ys  : list symbol)
           (o   : option grammar_entry)
           (heq : PM.find (x, ys) gr = o)
           (o'  : option (production_semty (x, ys))),
      match o as r return PM.find (x, ys) gr = r -> _ with
      | Some (@existT _ _ _ fs) =>
        fun hf =>
          Some (cast_lookup_result _ _ _ fs hw hf)
      | None =>
        fun _ =>
          None
      end heq = o'
      -> match o' with
         | Some (p, f) =>
           PM.find (x, ys) gr = Some (@existT _ _ (x, ys) (p, f))
         | None =>
           PM.find (x, ys) gr = None
         end.
  Proof.
    intros gr hw x ys o hf o' heq.
    pose proof hf as hf'.
    destruct o as [((x', ys'), (p, f)) |]; subst; auto.
    - apply PMF.find_mapsto_iff in hf'.
      apply hw in hf'; inv hf'.
      destruct (cast_lookup_result _ _ _ _ _ _) as (o, f') eqn:hc.
      apply cast_lookup_result_refl in hc; inv hc; auto.
  Qed.

  Lemma fpaa_cases :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ys  : list symbol)
           (o   : option (production_semty (x, ys))),
      findPredicateAndAction (x, ys) gr hw = o
      -> match o with
         | Some (p, f) =>
           PM.find (x, ys) gr = Some (@existT _ _ (x, ys) (p, f))
         | None =>
           PM.find (x, ys) gr = None
         end.
  Proof.
    intros; eapply fpaa_cases'; eauto.
  Qed.
  
  Lemma fpaa_mapsto :
    forall g hw x ys p f,
      findPredicateAndAction (x, ys) g hw = Some (p, f)
      -> PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g.
  Proof.
    intros g hw x ys p f hf.
    apply fpaa_cases in hf.
    apply PMF.find_mapsto_iff; auto.
  Qed.

  Ltac appl_fpaa :=
    match goal with
    | H : findPredicateAndAction _ _ _ = Some _ |- _ =>
      apply fpaa_mapsto in H
    end.

  (* An rhs_map maps each grammar nonterminal to its
     right-hand sides. It provides an efficient way to look
     up all right-hand sides for a given nonterminal -- a 
     frequent parser operation. *)
  
  (* Finite maps with nonterminal keys *)
  Module NM  := FMapAVL.Make NT_as_UOT.
  Module NMF := FMapFacts.Facts NM.

  Lemma nm_mapsto_in :
    forall (x : nonterminal)
           (A : Type)
           (a : A)
           (m : NM.t A),
      NM.MapsTo x a m -> NM.In x m.
  Proof.
    intros x A a m hm.
    apply NMF.in_find_iff.
    intros hf.
    apply NMF.find_mapsto_iff in hm; tc.
  Qed.

  Lemma nm_InA_In :
    forall B x (y : B) prs,
      InA (NM.eq_key_elt (elt:=B)) (x, y) prs
      -> In (x, y) prs.
  Proof.
    intros B x y prs hi; induction prs as [| (x', y') prs IH]; inv hi; sis; auto.
    match goal with
    | H : NM.eq_key_elt _ _ |- _ => inv H
    end.
    sis; subst; auto.
  Qed.

  Lemma nm_eq_key_elt_equivalence :
    forall (A : Type),
      Equivalence (NM.eq_key_elt (elt:=A)).
  Proof.
    constructor; try firstorder.
    - intros x y z heq heq'.
      repeat red in heq; repeat red in heq'; repeat red.
      destruct heq as [h1 h2]; destruct heq' as [h3 h4].
      rewrite h1; rewrite h3; rewrite h2; rewrite h4; auto.
  Qed.
  
  Lemma nm_mapsto_elements_iff :
    forall B x (y : B) m,
      NM.MapsTo x y m <-> In (x, y) (NM.elements m).
  Proof.
    intros B x y m; split; [intros hm | intros hi].
    - apply nm_InA_In.
      apply NMF.elements_mapsto_iff in hm; auto.
    - apply NMF.elements_mapsto_iff.
      apply In_InA; auto.
      apply nm_eq_key_elt_equivalence.
  Qed.

  Lemma find_Some__In :
    forall (x : nonterminal)
           (A : Type)
           (a : A)
           (m : NM.t A),
      NM.find x m = Some a -> NM.In x m.
  Proof.
    intros x A a m hi.
    apply NMF.in_find_iff; tc.
  Qed.

  Definition rhs_map := NM.t (list (list symbol)).

  Definition allRhss (rm : rhs_map) : list (list symbol) :=
    List.concat (List.map snd (NM.elements rm)).

  Definition addProduction
             (p : production)
             (e : grammar_entry)
             (rm : rhs_map) : rhs_map :=
    match p with
    | (x, ys) =>
      match NM.find x rm with
      | Some yss => NM.add x (ys :: yss) rm
      | None     => NM.add x [ys] rm
      end
    end.

  Definition mkRhsMap (g : grammar) : rhs_map :=
    PM.fold addProduction g (NM.empty (list (list symbol))).

  (* Soundness of keys in the result of mkRhsMap w.r.t. the input grammar *)

  Definition rmks' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x,
      NM.In x rm -> exists ys e, In ((x, ys), e) prs.
  
  Lemma rmks'_empty :
      rmks' (NM.empty (list (list symbol))) [].
  Proof.
    intros x hi.
    apply NMF.empty_in_iff in hi; destruct hi.
  Qed.
  
  Lemma addProduction_preserves_rmks' :
    forall rm pr prs,
      rmks' rm prs
      -> rmks' (addProduction (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x, ys), e) prs hi x' hi'; red in hi; sis.
    destruct (NM.find x rm) as [yss |] eqn:hf.
    - destruct (nt_eq_dec x' x) as [heq | hneq]; subst.
      + apply find_Some__In in hf.
        apply hi in hf.
        destruct hf as [ys' [e' hi'']].
        exists ys', e'.
        apply in_or_app; left; auto.
      + apply NMF.add_neq_in_iff in hi'; auto.
        apply hi in hi'.
        destruct hi' as [ys' [e' hi']].
        exists ys', e'.
        apply in_or_app; left; auto.
    - destruct (nt_eq_dec x' x) as [heq | hneq]; subst.
      + exists ys, e.
        apply in_or_app; right.
        apply in_eq.
      + apply NMF.add_neq_in_iff in hi'; auto.
        apply hi in hi'.
        destruct hi' as [ys' [e' hi']].
        exists ys', e'.
        apply in_or_app; left; auto.
  Qed.
  
  Lemma rmks'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rmks' 
        (fold_left (fun a p => addProduction (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rmks'_empty.
    - apply addProduction_preserves_rmks'.
  Qed.

  Definition rhs_map_keys_sound (rm : rhs_map) (g : grammar) : Prop :=
    forall x,
      NM.In x rm -> exists ys, PM.In (x, ys) g.
  
  Lemma mkRhsMap_keys_sound :
    forall g,
      rhs_map_keys_sound (mkRhsMap g) g.
  Proof.
    intros g x hi.
    unfold mkRhsMap in hi.
    rewrite PM.fold_1 in hi.
    apply rmks'__fold_left in hi.
    destruct hi as [ys [e hi]].
    exists ys.
    apply PMF.elements_in_iff.
    exists e.
    apply In_InA; auto.
    apply grammar_eq_key_elt_equivalence.
  Qed.
 
  (* Soundness of the result of mkRhsMap w.r.t. the input grammar *)

  Definition rms' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x ys yss,
      NM.MapsTo x yss rm -> In ys yss -> exists e, In ((x, ys), e) prs.

  Lemma rms'_empty :
      rms' (NM.empty (list (list symbol))) [].
  Proof.
    intros x ys yss hm hi.
    exfalso.
    eapply NMF.empty_mapsto_iff; eauto.
  Qed.

  Lemma addProduction_preserves_rms' :
    forall rm pr prs,
      rms' rm prs
      -> rms' (addProduction (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x', ys'), e) prs hr x ys yss hm hi; sis. 
    destruct (NM.find _ _) as [yss' |] eqn:hf.
    - destruct (nt_eq_dec x' x) as [? | hneq]; subst.
      + apply NMF.add_mapsto_iff in hm.
        destruct hm as [[_ heq] | [? ?]]; tc; subst.
        destruct hi as [hh | ht]; subst.
        * exists e.
          apply in_or_app; right.
          apply in_eq.
        * apply NMF.find_mapsto_iff in hf.
          eapply hr in ht; eauto.
          destruct ht as [e' hi].
          exists e'.
          apply in_or_app; left; auto.
      + apply NM.add_3 in hm; auto.
        eapply hr in hi; eauto.
        destruct hi as [e' hi].
        exists e'.
        apply in_or_app; left; auto.
    - destruct (nt_eq_dec x' x) as [? | hneq]; subst.
      + apply NMF.add_mapsto_iff in hm.
        destruct hm as [[_ heq] | [? ?]]; tc; subst.
        apply in_singleton_eq in hi; subst.
        exists e.
        apply in_or_app; right.
        apply in_eq.
      + apply NM.add_3 in hm; auto.
        eapply hr in hi; eauto.
        destruct hi as [e' hi].
        exists e'.
        apply in_or_app; left; auto.
  Qed.

    Lemma rms'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rms' 
        (fold_left (fun a p => addProduction (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rms'_empty.
    - apply addProduction_preserves_rms'.
  Qed.
  
  Definition rhs_map_sound (rm : rhs_map) (g : grammar) :=
    forall x ys yss,
      NM.MapsTo x yss rm -> In ys yss -> PM.In (x, ys) g.

  Lemma mkRhsMap_sound :
    forall g,
      rhs_map_sound (mkRhsMap g) g.
  Proof.
    intros g x ys yss hm hi.
    unfold mkRhsMap in hm.
    rewrite PM.fold_1 in hm.
    eapply rms'__fold_left in hi; eauto.
    destruct hi as [e hi].
    apply PMF.elements_in_iff.
    exists e.
    apply In_InA; auto.
    apply grammar_eq_key_elt_equivalence.
  Qed.

  (* Completeness of the result of mkRhsMap w.r.t. the input grammar *)

  Definition rmc' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x ys e,
      In ((x, ys), e) prs
      -> exists yss, NM.MapsTo x yss rm /\ In ys yss.

  Lemma rmc'_empty :
      rmc' (NM.empty (list (list symbol))) [].
  Proof.
    intros x ys e hi.
    inv hi. 
  Qed.

  Lemma addProduction_preserves_rmc' :
    forall rm pr prs,
      rmc' rm prs
      -> rmc' (addProduction (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x', ys'), e') prs hr x ys e hi; sis.
    apply in_app_or in hi; destruct hi as [hl | hr'].
    - destruct (NM.find _ _) as [yss' |] eqn:hf.
      + destruct (nt_eq_dec x' x) as [? | hneq]; subst;
          apply hr in hl; destruct hl as [yss [hm hi]].
        * exists (ys' :: yss'); split; auto.
          -- apply NMF.add_mapsto_iff; auto.
          -- apply NMF.find_mapsto_iff in hm.
             rewrite hm in hf; inv hf; apply in_cons; auto.
        * exists yss; split; auto.
          apply NMF.add_mapsto_iff; auto.
      + destruct (nt_eq_dec x' x) as [? | hneq]; subst;
          apply hr in hl; destruct hl as [yss [hm hi]].
        * exists [ys']; split; auto.
          -- apply NMF.add_mapsto_iff; auto.
          -- apply NMF.find_mapsto_iff in hm.
             rewrite hm in hf; inv hf; apply in_cons; auto.
        * exists yss; split; auto.
          apply NM.add_2; auto.
    - apply in_singleton_eq in hr'; inv hr'.
      destruct (NM.find _ _) as [yss' |] eqn:hf; eexists; split;
        try (apply NMF.add_mapsto_iff; auto); try apply in_eq.
  Qed.
  
  Lemma rmc'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rmc' 
        (fold_left (fun a p => addProduction (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rmc'_empty.
    - apply addProduction_preserves_rmc'.
  Qed.

  Definition rhs_map_complete (rm : rhs_map) (g : grammar) :=
    forall x ys,
      PM.In (x, ys) g -> exists yss, NM.MapsTo x yss rm /\ In ys yss.

  Lemma mkRhsMap_complete :
    forall g,
      rhs_map_complete (mkRhsMap g) g.
  Proof.
    intros g x ys hi.
    apply PMF.elements_in_iff in hi.
    destruct hi as [e hi].
    apply pm_InA__In in hi.
    eapply rmc'__fold_left in hi.
    destruct hi as [yss [hm hi]].
    exists yss; split; auto.
    unfold mkRhsMap.
    rewrite PM.fold_1; auto.
  Qed.

  (* Correctness spec for mkRhsMap *)
  Definition rhs_map_correct (rm : rhs_map) (g : grammar) :=
    rhs_map_keys_sound rm g
    /\ rhs_map_sound rm g
    /\ rhs_map_complete rm g.

  Lemma in_grammar_find_some :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> exists yss,
          NM.find x rm = Some yss
          /\ In ys yss.
  Proof.
    intros g rm x ys [hs [hs' hc]] hi.
    apply hc in hi; destruct hi as [yss [hm hi]].
    apply NMF.find_mapsto_iff in hm; eauto.
  Qed.
  
  Lemma mkRhsMap_correct :
    forall (g : grammar),
      rhs_map_correct (mkRhsMap g) g.
  Proof.
    intros g; repeat split.
    - apply mkRhsMap_keys_sound.
    - apply mkRhsMap_sound.
    - apply mkRhsMap_complete.
  Qed.

  Definition keys (rm : rhs_map) : list nonterminal :=
    fold_right (fun pr l => fst pr :: l) [] (NM.elements rm).

  Lemma production_lhs_in_keys :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> In x (keys rm).
  Proof.
    intros g rm x ys hc hi.
    apply in_map_iff.
    destruct hc as [_ [_ hc]].
    apply hc in hi.
    destruct hi as [yss [hm hi]].
    exists (x, yss); split; auto.
    apply nm_mapsto_elements_iff; auto.
  Qed.
    
  Definition keySet (rm : rhs_map) : NtSet.t :=
    fromNtList (keys rm).

  Lemma production_lhs_in_keySet :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> NtSet.In x (keySet rm).
  Proof.
    intros.
    eapply fromNtList_in_iff.
    eapply production_lhs_in_keys; eauto.
  Qed.
  
  Definition rhssFor (x : nonterminal) (rm : rhs_map) : list (list symbol) :=
    match NM.find x rm with
    | Some yss => yss
    | None     => []
    end.
  
  Lemma rhssFor_in_iff :
    forall g rm x ys,
      rhs_map_correct rm g
      -> In ys (rhssFor x rm) <-> PM.In (x, ys) g.
  Proof.
    unfold rhssFor; intros g rm x ys [hs [hs' hc]]; split; intros hi.
    - destruct (NM.find _ _) eqn:hf; try inv hi.
      apply NMF.find_mapsto_iff in hf; eauto.
    - apply hc in hi; destruct hi as [yss [hm hi]].
      destruct (NM.find _ _) as [yss' |] eqn:hf;
        apply NMF.find_mapsto_iff in hm;
        rewrite hm in hf; inv hf; auto.
  Qed.

  Lemma rhssFor_keys :
    forall x ys rm,
      In ys (rhssFor x rm) -> In x (keys rm).
  Proof.
    intros x ys rm hi; unfold rhssFor in hi.
    destruct (NM.find _ _) as [yss |] eqn:hf; try solve [inv hi].
    apply NMF.find_mapsto_iff in hf.
    apply NMF.elements_mapsto_iff in hf.
    apply InA_alt in hf.
    destruct hf as [(x', yss') [heq hi']]; inv heq; sis; subst.
    apply in_map_iff. 
    exists (x', yss'); split; auto.
  Qed.
  
  Lemma rhssFor_keySet :
    forall x ys rm,
      In ys (rhssFor x rm) -> NtSet.In x (keySet rm).
  Proof.
    intros.
    apply fromNtList_in_iff.
    eapply rhssFor_keys; eauto.
  Qed.

  Lemma rhssFor_elements :
    forall x ys rm,
      In ys (rhssFor x rm)
      -> (exists yss, In (x, yss) (NM.elements rm) /\ In ys yss).
  Proof.
    intros x ys rm hi.
    unfold rhssFor in hi.
    destruct (NM.find _ _) as [yss |] eqn:hf.
    - exists yss; split; auto.
      apply NMF.find_mapsto_iff in hf.
      apply nm_mapsto_elements_iff; auto.
    - inv hi.
  Qed.

  Lemma rhssFor_allRhss' :
    forall A B (x : A) (y : B) ys prs,
      In (x, ys) prs
      -> In y ys
      -> In y (List.concat (List.map snd prs)).
  Proof.
    intros A B x y ys prs hi hi'.
    induction prs as [| (x', y') prs IH]; sis.
    - inv hi.
    - destruct hi as [hh | ht].
      + inv hh;
        apply in_or_app; auto.
      + apply in_or_app; auto.
  Qed.
  
  Lemma rhssFor_allRhss :
    forall x ys rm,
      In ys (rhssFor x rm)
      -> In ys (allRhss rm).
  Proof.
    intros x ys rm hi.
    apply rhssFor_elements in hi.
    destruct hi as [yss [hi hi']].
    eapply rhssFor_allRhss'; eauto.
  Qed.

(*
  Lemma in_grammar__keySet :
    forall g pm x ys,
      production_map_correct pm g
      -> In (x, ys) g
      -> NtSet.In x (keySet pm).
  Proof.
    intros g pm x ys hp hi.
    eapply rhssFor_keySet.
    eapply rhssFor_in_iff; eauto.
  Qed.
  
  Definition rhsLengths (g : grammar) : list nat :=
    map (fun rhs => List.length rhs) (rhss g).
 *)
  
  (* The next two definitions help us use a well-founded measure that is 
     already defined in terms of a grammar, rather than a production map *)

  (*
  Definition decompress (e : nonterminal * list (list symbol)) : list production :=
    match e with
    | (x, yss) => map (pair x) yss
    end.

  Lemma decompress_nt_eq :
    forall x x' ys yss,
      In (x, ys) (decompress (x', yss))
      -> x' = x.
  Proof.
    intros x x' ys yss hi; sis.
    apply in_map_iff in hi; destruct hi as [? [heq hi]].
    inv heq; auto.
  Qed.

  Definition grammarOf (pm : production_map) : grammar :=
    flat_map decompress (NM.elements pm).

  Lemma rhssFor_grammarOf :
    forall x ys pm,
      In ys (rhssFor x pm) -> In (x, ys) (grammarOf pm).
  Proof.
    unfold rhssFor, grammarOf; intros x ys pm hi.
    destruct (NM.find _ _) as [yss |] eqn:hf; try solve [inv hi].
    apply in_flat_map.
    exists (x, yss); split.
    - apply NMF.find_mapsto_iff in hf.
      apply NMF.elements_mapsto_iff in hf.
      apply InA_alt in hf.
      destruct hf as [(x', yss') [heq hi']].
      repeat red in heq; sis; destruct heq; subst; auto.
    - apply in_map_iff; eauto.
  Qed.

  Lemma in_elements__in_fold_right_add_key :
    forall (x   : nonterminal)
           (yss : list (list symbol))
           (prs : list (nonterminal * list (list symbol))),
      In (x, yss) prs
      -> In x (fold_right (fun pr l => fst pr :: l) [] prs).
    intros x yss prs hi; induction prs as [| (x', yss') prs Ih]; sis; auto.
    destruct hi as [hh | ht]; auto.
    inv hh; auto.
  Qed.
  
  Lemma grammarOf_keySet :
    forall x ys pm,
      In (x, ys) (grammarOf pm)
      -> NtSet.In x (keySet pm).
  Proof.
    intros x ys pm hi.
    apply in_flat_map in hi; destruct hi as [(x', yss) [hi hi']].
    apply decompress_nt_eq in hi'; subst.
    apply fromNtList_in_iff.
    eapply in_elements__in_fold_right_add_key; eauto.
  Qed.

  Lemma in_grammar__in_grammarOf :
    forall g pm x ys,
      production_map_correct pm g
      -> In (x, ys) g
      -> In (x, ys) (grammarOf pm).
  Proof.
    intros g pm x ys hc hi.
    apply rhssFor_grammarOf.
    eapply rhssFor_in_iff; eauto.
  Qed.
  
  Lemma rhss_rhsLengths_in :
    forall g rhs,
      In rhs (rhss g)
      -> In (List.length rhs) (rhsLengths g).
  Proof.
    intros g rhs hin; induction g as [| (x, rhs') ps Ih];
      simpl in *; inv hin; auto.
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
    intros g x rhs hin.
    apply grammar_rhs_length_le_max in hin; omega.
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
    apply NF.mem_iff.
    apply allNts_lhss_iff. 
    eapply production_lhs_in_lhss; eauto.
  Qed.
   *)
  
  (* Definitions related to input that the parser consumes. *)
  Definition token   := {a : terminal & t_semty a}. 

  Definition showToken (t : token) : string :=
    match t with
    | @existT _ _ a _ => "(" ++ showT a ++ ")"
    end.

  (* Concrete syntax trees *)
  Inductive tree    := Leaf : terminal -> tree
                     | Node : nonterminal -> list tree -> tree.

  Definition forest := list tree.

  (* The next two functions are used to validate 
     the output of extracted parsers *)
  Fixpoint countNodes (t : tree) : nat :=
    match t with
    | Leaf _     => 1
    | Node _ sts =>
      let fix countNodes' (f : forest) : nat :=
          match f with
          | []      => 0
          | t :: f' => countNodes t + countNodes' f'
          end
      in  countNodes' sts
    end.

  Fixpoint flatten (t : tree) : list terminal :=
    match t with
    | Leaf t     => [t]
    | Node _ sts => flat_map flatten sts
    end.

  (* Parser stacks *)

  (* The stack used in LL prediction and parsing *)

  Inductive parser_frame : Type :=
  | Fr (pre : list symbol)       (* rhs prefix *)
       (sem : symbols_semty pre) (* sem value for prefix *)
       (suf : list symbol).      (* rhs suffix *)

  Lemma frames_eq__semvals_eq :
    forall pre vs vs' suf suf',
      Fr pre vs suf = Fr pre vs' suf'
      -> vs = vs'.
  Proof.
    intros pre vs vs' suf suf' heq.
    inv heq.
    ss_inj; auto.
  Qed.
  
  Definition suffix (fr : parser_frame) : list symbol :=
    match fr with
    | Fr _ _ suf => suf
    end.

  Definition parser_stack : Type :=
    (parser_frame * list parser_frame)%type.

  Definition stackSuffixes (stk : parser_stack) : list symbol * list (list symbol) :=
    match stk with
    | (fr, frs) => (suffix fr, map suffix frs)
    end.

  Definition bottomFrameSyms (stk : parser_stack) : list symbol := 
    match bottomElt stk with
    | Fr pre _ suf => rev pre ++ suf
    end.

  Record subparser := Sp { prediction : list symbol
                           ; stack      : parser_stack }.

  Lemma sps_eq__head_frames_eq :
    forall pred pred' fr fr' frs frs',
      Sp pred (fr, frs) = Sp pred' (fr', frs')
      -> fr = fr'.
  Proof.
    intros pred pred' fr fr' frs frs' heq; inv heq; auto.
  Qed.

  Lemma inv_sp_eq_terminal_head :
    forall pred a pre v vs suf frs pred' pre' vs' suf' frs',
      Sp pred (Fr (T a :: pre) (v, vs) suf, frs) = Sp pred' (Fr pre' vs' suf', frs')
      -> pred = pred'
         /\ suf = suf'
         /\ frs = frs'
         /\ exists (heq : T a :: pre = pre'),
             (cast_ss _ _ heq (v, vs)) = vs'.
  Proof.
    intros pred a pre v vs suf frs pred' pre' vs' suf' frs' heq.
    pose proof heq as heq'.
    inv heq.
    apply sps_eq__head_frames_eq in heq'.
    apply frames_eq__semvals_eq in heq'; subst.
    repeat split; auto.
    exists eq_refl.
    rewrite cast_ss_refl; auto.
  Qed.

  (* The stack used in SLL prediction *)
  
  Inductive sll_frame :=
  | SllFr : option nonterminal -> list symbol -> sll_frame.

  Definition sllSuffix (fr : sll_frame) : list symbol :=
    match fr with
    | SllFr _ suf => suf
    end.

  Module SllFr_as_UOT <: UsualOrderedType.

    Module O  := Option_as_UOT NT_as_UOT.
    Module L  := List_as_UOT Symbol_as_UOT.
    Module P  := Pair_as_UOT O L.

    Definition t := sll_frame.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt x y :=
      match x, y with
      | SllFr o suf, SllFr o' suf' =>
        P.lt (o, suf) (o', suf')
      end.

    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros [o suf] [o' suf'] [o'' suf'']; eapply P.lt_trans; eauto.
    Qed.

    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros [o suf] [o' suf'] hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    Definition compare (x y : sll_frame) : Compare lt eq x y.
      refine (match x, y with
              | SllFr o suf, SllFr o' suf' =>
                match P.compare (o, suf) (o', suf') with
                | LT hl => LT _
                | GT he => GT _
                | EQ hl => EQ _
                end
              end); red; tc.
    Defined.
      
    Definition eq_dec (x y : sll_frame) : {x = y} + {x <> y}.
      refine (match x, y with
              | SllFr o suf, SllFr o' suf' =>
                match P.eq_dec (o, suf) (o', suf') with
                | left he  => left _
                | right hn => right _
                end
              end); tc.
    Defined.

  End SllFr_as_UOT.

  (* Finite sets of SLL frames *)
  Module FS  := FSetAVL.Make SllFr_as_UOT.
  Module FSF := FSetFacts.Facts FS.

  (* Finite maps with SLL frame keys *)
  Module FM  := FMapAVL.Make SllFr_as_UOT.
  Module FMF := FMapFacts.Facts FM.

  (* Module for finding the transitive closure
     of a finite graph with SLL frame nodes *)
  Module TC  := TransClos.Make FS FM.

  Definition sll_stack := (sll_frame * list sll_frame)%type.
  
  Definition sllStackSuffixes (stk : sll_stack) : list symbol * list (list symbol) :=
    match stk with
    | (fr, frs) => (sllSuffix fr, map sllSuffix frs)
    end.

  Record sll_subparser : Type :=
    SllSp { sll_pred : list symbol;
            sll_stk  : sll_stack }.

  (* Projecting an SLL subparser from an LL subparser *)


  (*Definition sllify' (fr : parser_frame) : suffix_frame :=
    match fr with
    | Fr _ _ suf => SF None suf
    end.

  Definition sllify (stk : parser_stack) : suffix_stack :=
    match stk with
    | (fr, frs) => (sllify' fr, map sllify' frs)
    end.

  Definition sllifySp (sp : subparser) : sll_subparser :=
    match sp with
    | Sp pred stk => SllSp pred (sllify stk)
    end. *)

  (*
  
  Fixpoint unprocSyms (frs : list parser_frame) : list symbol :=
    match frs with 
    | []                         => []
    | Fr _ _ _ suf :: frs'       => suf ++ unprocSyms frs'
    end.

  Definition unprocStackSyms (stk : parser_stack) : list symbol :=
    match stk with
    | (fr, frs) => unprocSyms (fr :: frs)
    end.
   *)

  (* Grammatical derivation relations -- the main parser correctnes spec *)

  (* Derivation relation for concrete syntax trees *)
  Inductive tree_derivation (g : grammar) : symbol -> list token -> tree -> Prop :=
  | Leaf_der  : 
      forall (a : terminal) (v : t_semty a),
        tree_derivation g (T a) [@existT _ _ a v] (Leaf a)
  | Node_der : 
      forall (x  : nonterminal) (ys : list symbol) (w : list token) (sts : forest),
        PM.In (x, ys) g
        -> forest_derivation g ys w sts
        -> tree_derivation g (NT x) w (Node x sts)
  with forest_derivation (g : grammar) : list symbol -> list token-> forest-> Prop :=
       | NilForest_der  : 
           forest_derivation g [] [] []
       | ConsForest_der : 
           forall (s : symbol) (ss : list symbol) (wpre wsuf : list token) 
                  (tr : tree) (trs : list tree),
             tree_derivation g s wpre tr
             -> forest_derivation g ss wsuf trs
             -> forest_derivation g (s :: ss) (wpre ++ wsuf) (tr :: trs).

  Hint Constructors tree_derivation forest_derivation : core.

  Scheme tree_derivation_mutual_ind   := Induction for tree_derivation Sort Prop
    with forest_derivation_mutual_ind := Induction for forest_derivation Sort Prop.

  Ltac inv_td hs  hi hg:=
    inversion hs as [ ? ? | ? ? ? ? hi hg]; subst; clear hs.

  Ltac inv_fd hg  hs hg' :=
    inversion hg as [| ? ? ? ? ? ? hs hg']; subst; clear hg.

  Lemma forest_derivation_app' :
    forall g ys1 w1 v1,
      forest_derivation g ys1 w1 v1
      -> forall ys2 w2 v2,
        forest_derivation g ys2 w2 v2
        -> forest_derivation g (ys1 ++ ys2) (w1 ++ w2) (v1 ++ v2).
  Proof.
    intros g ys1 w1 v1 hg.
    induction hg; intros ys2 w2 v2 hg2; simpl in *; auto.
    rewrite <- app_assoc; constructor; auto.
  Qed.

  Lemma forest_derivation_app :
    forall g ys ys' w w' v v',
      forest_derivation g ys w v
      -> forest_derivation g ys' w' v'
      -> forest_derivation g (ys ++ ys') (w ++ w') (v ++ v').
  Proof.
    intros; eapply forest_derivation_app'; eauto.
  Qed.

  Lemma forest_app_singleton_node : 
    forall g x ys ys' w w' v v',
      PM.In (x, ys') g
      -> forest_derivation g ys w v
      -> forest_derivation g ys' w' v'
      -> forest_derivation g (ys ++ [NT x]) (w ++ w') (v ++ [Node x v']).
  Proof.
    intros g x ys ys' w w' v v' hi hg hg'.
    apply forest_derivation_app; auto.
    rew_nil_r w'; eauto.
  Qed.

  Lemma terminal_head_forest_derivation :
    forall g a v ys w ts,
      forest_derivation g ys w ts
      -> forest_derivation g (T a :: ys) ((@existT _ _ a v) :: w) (Leaf a :: ts).
  Proof.
    intros g a v ys w ts hg.
    assert (happ : (@existT _ _  a v) :: w =
                   [@existT _ _ a v] ++ w)
      by apply cons_app_singleton.
    rewrite happ; auto.
  Qed.

  Lemma forest_derivation_split :
    forall g ys ys' w'' v'',
      forest_derivation g (ys ++ ys') w'' v''
      -> exists w w' v v',
        w'' = w ++ w'
        /\ v'' = v ++ v'
        /\ forest_derivation g ys  w  v
        /\ forest_derivation g ys' w' v'.
  Proof.
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' v'' hg; sis.
    - exists []; exists w''; exists []; exists v''; repeat split; auto.
    - inversion hg as [| s ss wpre wsuf t f hs hg']; subst; clear hg. 
      apply Ih in hg'; destruct hg' as [w [w' [v [v' [? [? [hg' hg'']]]]]]]; subst.
      exists (wpre ++ w); exists w'; exists (t :: v); exists v'. 
      repeat split; auto; apps.
  Qed.

  Lemma forest_derivation_terminal_end :
    forall g ys a w v,
      forest_derivation g (ys ++ [T a]) w v
      -> exists w_front l v_front,
        w = w_front ++ [@existT _ _ a l]
        /\ v = v_front ++ [Leaf a]
        /\ forest_derivation g ys w_front v_front.
  Proof.
    intros g ys a w v hg.
    eapply forest_derivation_split in hg.
    destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
    inv_fd hg' ht hg''.
    inv_td ht hi hf.
    inv_fd hg'' ht hg'''.
    repeat eexists; eauto.
  Qed.

  Lemma forest_derivation_nonterminal_end :
    forall g ys x w v,
      forest_derivation g (ys ++ [NT x]) w v
      -> exists wpre wsuf vpre v',
        w = wpre ++ wsuf
        /\ v = vpre ++ [Node x v']
        /\ forest_derivation g ys wpre vpre
        /\ tree_derivation g (NT x) wsuf (Node x v').
  Proof.
    intros g ys x w v hg.
    eapply forest_derivation_split in hg.
    destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
    inv_fd hg' ht hg''.
    inv_td ht hi hf.
    inv_fd hg'' ht hg'''.
    rewrite app_nil_r.
    repeat eexists; eauto.
  Qed.

  Lemma inv_leaf_treeder :
    forall g s w a,
      tree_derivation g s w (Leaf a)
      -> s = T a  /\ exists v, w = [@existT _ _ a v].
  Proof.
    intros g s w a hd; inv hd; eauto.
  Qed.

  Lemma inv_node_treeder :
    forall g s w x sts,
      tree_derivation g s w (Node x sts)
      -> s = NT x /\ exists ys, PM.In (x, ys) g /\ forest_derivation g ys w sts.
  Proof.
    intros g s w x sts hd; inv hd; eauto.
  Qed.

  Lemma inv_cons_forestder :
    forall g ss w t ts,
      forest_derivation g ss w (t :: ts)
      -> exists s ss' w1 w2,
        ss = s :: ss'
        /\ w = w1 ++ w2
        /\ tree_derivation g s w1 t
        /\ forest_derivation g ss' w2 ts.
  Proof.
    intros g ss w t ts hd; inv hd; eauto 8.
  Qed.
            
  Definition terminals (ts : list token) : list terminal :=
    map (@projT1 _ t_semty) ts.

  Lemma terminals_app :
    forall ts ts',
      terminals (ts ++ ts') = terminals ts ++ terminals ts'.
  Proof.
    intros ts ts'.
    unfold terminals.
    apply map_app.
  Qed.

  Lemma forests_eq__words_eq_rhss_eq' :
    forall g ys w ts,
      forest_derivation g ys w ts
      -> forall w' suf suf' ys',
        forest_derivation g ys' w' ts
        -> w ++ suf = w' ++ suf'
        -> w' = w /\ suf' = suf /\ ys' = ys.
  Proof.
    intros g ys w ts hf. 
    induction hf using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall w' suf suf' s',
                  tree_derivation g s' w' t
                  -> w ++ suf = w' ++ suf'
                  -> w' = w /\ suf' = suf /\ s' = s).
    - intros w' suf suf' s' hd heq; sis.
      apply inv_leaf_treeder in hd.
      destruct hd as [? [v' heq']]; subst.
      inv heq; repeat split; auto.
      apply heads_eq_tails_eq__lists_eq; auto.
    - intros w' suf suf' s' hd heq.
      apply inv_node_treeder in hd.
      destruct hd as [? [ys' [hi hd]]]; subst.
      eapply IHhf in hd; eauto.
      firstorder.
    - intros w' suf suf' ys' hd heq; inv hd; auto.
    - intros w' suf suf' ys' hd heq.
      apply inv_cons_forestder in hd.
      destruct hd as [s' [ss' [w1 [w2 [heq' [heq'' [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      eapply IHhf in hd; eauto.
      destruct hd as [? [heq' ?]]; subst.
      eapply IHhf0 in hd'; eauto.
      destruct hd' as [? [? ?]]; subst; auto.
  Qed.

  Lemma forests_eq__words_eq_rhss_eq :
    forall g ys ys' pre pre' suf suf' ts,
      forest_derivation g ys pre ts
      -> forest_derivation g ys' pre' ts
      -> pre ++ suf = pre' ++ suf'
      -> pre' = pre /\ suf' = suf /\ ys' = ys.
  Proof.
    intros. eapply forests_eq__words_eq_rhss_eq'; eauto.
  Qed.
  
(*  Lemma forests_eq__rhss_eq' :
    forall g ys w ts,
      forest_derivation g ys w ts
      -> forall w' ys',
        forest_derivation g ys' w' ts
        -> (terminals w' = terminals w) /\ ys' = ys.
  Proof.
    intros g ys w ts hf. 
    induction hf using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall w' s',
                  tree_derivation g s' w' t
                  -> terminals w' = terminals w /\ s' = s).
    - intros w' s' hs; inv hs; auto.
    - intros w' s' hs; inv hs; firstorder.
    - intros w' ys' hf; auto; inv hf; auto. 
    - intros w' ys' hf'.
      inv hf'.
      apply IHhf in H3.
      destruct H3 as [ht ?]; subst.
      apply IHhf0 in H4.
      destruct H4 as [ht' ?]; subst.
      split; auto.
      repeat rewrite terminals_app.
      rewrite ht.
      rewrite ht'; auto.
  Qed. *)

(*  Lemma forests_eq__rhss_eq :
    forall g ys ys' w ts,
      forest_derivation g ys w ts
      -> forest_derivation g ys' w ts
      -> ys' = ys.
  Proof.
    intros g ys ys' w ts hf hf'.
    eapply forests_eq__rhss_eq'
      with (ys := ys) (ys' := ys') in hf'; eauto.
    firstorder.
  Qed. *)

(*  Lemma trees_eq__forests_eq_words_eq' :
    forall g ys w v,
      forest_derivation g ys w v
      -> forall ys' w',
        forest_derivation g ys' w' v
        -> ys' = ys /\ w' = w.
  Proof.
    intros g ys w v hg.
    induction hg using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall s' w',
                  tree_derivation g s' w' t
                  -> s' = s /\ w' = w).
    - intros s' w' hs; inv hs; auto.
    - intros s' w' hs; inv hs; firstorder.
    - intros ys' w' hg; inv hg; auto.
    - intros ys' w' hg'; inv hg'.
      apply Ihhg in h3; destruct h3; subst.
      apply Ihhg0 in h4; destruct h4; subst; auto.
  Qed. 

  Lemma trees_eq__gammas_eq_words_eq :
    forall g ys ys' w w' v,
      gamma_derivation g ys w v
      -> gamma_derivation g ys' w' v
      -> ys' = ys /\ w' = w.
  Proof.
    intros; eapply trees_eq__gammas_eq_words_eq'; eauto.
  Qed.

 *)

  Lemma forest_derivation_singleton_t :
    forall g a w v,
      forest_derivation g [T a] w v
      -> exists l,
        w = [@existT _ _ a l]
        /\ v = [Leaf a].
  Proof.
    intros g a w v hg.
    inv_fd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
  Qed.

  Lemma forest_derivation_singleton_nt :
    forall g x w v,
      forest_derivation g [NT x] w v
      -> exists ys v',
        PM.In (x, ys) g
        /\ v = [Node x v']
        /\ forest_derivation g ys w v'.
  Proof.
    intros g x w v hg.
    inv_fd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
  Qed.

  Definition unique_forest_derivation g ss w v :=
    forest_derivation g ss w v
    /\ forall v', forest_derivation g ss w v' -> v = v'.

  (* Derivation relation for semantic values *)
  Inductive sem_value_derivation (g : grammar) :
    forall (s : symbol), list token -> symbol_semty s -> Prop :=
  | T_der  : 
      forall (a : terminal) (v : t_semty a),
        sem_value_derivation g (T a) [@existT _ _ a v] v
  | NT_der : 
      forall (x  : nonterminal)
             (ys : list symbol)
             (w  : list token)
             (vs : symbols_semty ys)
             (p  : predicate_semty (x, ys))
             (f  : action_semty (x, ys)),
        PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
        -> sem_values_derivation g ys w vs
        -> p vs = true
        -> sem_value_derivation g (NT x) w (f vs)
  with sem_values_derivation (g : grammar) :
         forall (ys : list symbol), list token -> (symbols_semty ys) -> Prop :=
       | Nil_der  : 
           sem_values_derivation g [] [] tt
       | Cons_der : 
           forall (s     : symbol)
                  (ss    : list symbol)
                  (w1 w2 : list token) 
                  (v     : symbol_semty s)
                  (vs    : symbols_semty ss),
             sem_value_derivation g s w1 v
             -> sem_values_derivation g ss w2 vs
             -> sem_values_derivation g (s :: ss) (w1 ++ w2) (v, vs).

  Hint Constructors sem_value_derivation sem_values_derivation : core.

  Scheme sem_value_derivation_mutual_ind  := Induction for sem_value_derivation Sort Prop
    with sem_values_derivation_mutual_ind := Induction for sem_values_derivation Sort Prop.

  Ltac inv_sv hv  hm hvs hp :=
    inversion hv as [ ? ?
                    | ? ? ? ? ? ? hm hvs hp]; subst; clear hv.

  Ltac inv_svs hvs  hv hvs' :=
    inversion hvs as [| ? ? ? ? ? ? hv hvs']; subst; clear hvs.

  Ltac inv_t_der :=
    match goal with
    | H : sem_value_derivation _ (T _) _ _ |- _ =>
      inv H
    end.

  Ltac inv_nt_der :=
    match goal with
    | H : sem_value_derivation _ (NT _) _ _ |- _ =>
      inv H
    end.

  Lemma foo :
    forall g (ys : list symbol) w vs,
      sem_values_derivation g ys w vs
      -> (forall ys' vs' (heq : ys = ys'),
             sem_values_derivation g ys' w vs'
             -> vs' = (cast_ss ys ys' heq vs))
      -> (forall vs',
             sem_values_derivation g ys w vs'
             -> vs' = vs).
  Proof.
    intros g ys w vs hd ha vs' hd'.
    apply ha with (heq := eq_refl) in hd'.
    unfold cast_ss in hd'.
    unfold eq_rect_r in hd'.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in hd'; auto.
    apply Gamma_as_UOT.eq_dec.
  Qed.
  
  Lemma inv_t_semder :
    forall g a w v,
      sem_value_derivation g (T a) w v
      -> w = [@existT _ _ a v].
  Proof.
    intros g a w v hs.
    inversion hs as [? ? h h' heq |]; subst; clear hs.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; subst; auto.
    apply Symbol_as_UOT.eq_dec.
  Qed.

  Lemma inv_nt_semder :
    forall g x w v,
      sem_value_derivation g (NT x) w v
      -> (exists ys p f vs,
             PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
             /\ sem_values_derivation g ys w vs
             /\ f vs = v).
  Proof.
    intros g x w v hd.
    inversion hd as [| ? ? ? ? ? ? hm hd' hp h h' heq]; subst; clear hd.
    - repeat eexists; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
      apply Symbol_as_UOT.eq_dec.
  Qed.

  Lemma svd_app' :
    forall gr ys1 w1 vs1,
      sem_values_derivation gr ys1 w1 vs1
      -> forall ys2 w2 vs2,
        sem_values_derivation gr ys2 w2 vs2
        -> sem_values_derivation gr (ys1 ++ ys2) (w1 ++ w2) (concatTuple _ _ vs1 vs2).
  Proof.
    intros gr ys1 w1 vs1 hd.
    induction hd; intros ys2 w2' vs2 hd2; simpl in *; auto.
    rewrite <- app_assoc; constructor; auto.
  Qed.

  Lemma svd_app :
    forall gr ys ys' w w' vs vs',
      sem_values_derivation gr ys w vs
      -> sem_values_derivation gr ys' w' vs'
      -> sem_values_derivation gr (ys ++ ys') (w ++ w') (concatTuple _ _ vs vs').
  Proof.
    intros; eapply svd_app'; eauto.
  Qed.

  Lemma svd_app_nil_r' :
    forall gr ss w vs,
      sem_values_derivation gr (ss ++ []) w (concatTuple ss [] vs tt)
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss; induction ss as [| s ss IH]; intros w vs hd; sis.
    - inv hd.
      assert (vs = tt).
      { destruct vs; auto. }
      subst; auto.
    - inversion hd as [| ? ? ? ? ? ? hv hvs h h' h'' ]; subst; clear hd.
      apply symbols_semty_inj in h''.
      unfold concatTuple_rec_case in h''.
      unfold eq_rect_r in h''.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in h''.
      + destruct vs.
        inv h''.
        constructor; auto.
      + apply Gamma_as_UOT.eq_dec.
  Qed.

  Lemma svd_app_nil_r :
    forall gr ss w vs,
      sem_values_derivation gr (ss ++ []) (w ++ []) (concatTuple ss [] vs tt)
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss w vs hd.
    assert (heq : w = w ++ []) by (rewrite app_nil_r; auto).
    rewrite <- heq in hd.
    apply svd_app_nil_r'; auto.
  Qed.

  Lemma svd_app_nil_r_word:
    forall gr ss w vs,
      sem_values_derivation gr ss (w ++ []) vs
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss w vs hd.
    rewrite app_nil_r in hd; auto.
  Qed.

    Lemma svd_split :
    forall g ys ys' w'' vs'',
      sem_values_derivation g (ys ++ ys') w'' vs''
      -> exists w w' vs vs',
        w'' = w ++ w'
        /\ vs'' = concatTuple _ _ vs vs'
        /\ sem_values_derivation g ys w vs
        /\ sem_values_derivation g ys' w' vs'.
  Proof.
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' vs'' hvs; sis.
    - exists []; exists w''; exists tt; exists vs''; repeat split; auto.
    - inv_svs hvs hv hvs'; ss_inj. 
      apply Ih in hvs'.
      destruct hvs' as [w [w' [vs' [vs'' [? [? [hvs' hvs'']]]]]]]; subst.
      exists (w1 ++ w); exists w'; exists (v, vs'); exists vs''. 
      repeat split; auto; apps.
  Qed.
  
  Lemma svd_singleton_nt :
    forall g x w vs,
      sem_values_derivation g [NT x] w vs
      -> exists v ys vs' p f,
        vs = (v, tt)
        /\ PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
        /\ sem_values_derivation g ys w vs'
        /\ p vs' = true
        /\ v = f vs'.
  Proof.
    intros g x w vs hd.
    inv_svs hd hs hd'; ss_inj.
    inv hs; s_inj.
    inv hd'; ss_inj.
    rew_anr; eauto 10.
  Qed.

  Lemma svd_singleton_t :
    forall g a w vs,
      sem_values_derivation g [T a] w vs
      -> (exists v,
             w = [@existT _ _ a v]
             /\ vs = (v, tt)).
  Proof.
    intros g a w vs hd.
    inv_svs hd hs hd'.
    inv hs; inv hd'; s_inj; repeat ss_inj.
    rew_anr; eauto.
  Qed.

  Lemma svd_eq :
    forall gr xs ys w vs vs'
           (heq  : xs = ys)
           (heq' : vs' = cast_ss xs ys heq vs),
      sem_values_derivation gr xs w vs
      -> sem_values_derivation gr ys w vs'.
  Proof.
    intros gr xs ys w vs vs' heq heq' hd.
    eapply cast_ss_prop_eq with (vs' := vs'); eauto.
  Qed.

  Lemma svd_inv_singleton :
    forall g s w vs,
      sem_values_derivation g [s] w vs
      -> (exists v,
             (v, tt) = vs
             /\ sem_value_derivation g s w v).
  Proof.
    intros g s w vs hd; subst.
    inv_svs hd hv hvs; ss_inj.
    inv hvs; ss_inj.
    rew_anr; eauto.
  Qed.
  
  Lemma svd_singleton :
    forall g s w v,
      sem_value_derivation g s w v
      <-> sem_values_derivation g [s] w (v, tt).
  Proof.
    intros g s w v; split; intros hd.
    - rew_nil_r w.
      constructor; auto.
    - apply svd_inv_singleton in hd.
      destruct hd as [v' [heq hd]].
      inv heq; auto.
  Qed.

  Lemma svd_split_eq :
    forall gr ys ys' ys'' w'' vs''
      (heq : ys'' = ys ++ ys'),
      sem_values_derivation gr ys'' w'' vs''
      -> (exists w w' vs vs',
             w'' = w ++ w'
             /\ cast_ss _ _ heq vs'' = concatTuple _ _ vs vs'
             /\ sem_values_derivation gr ys w vs
             /\ sem_values_derivation gr ys' w' vs').
  Proof.
    intros gr ys ys' ys'' w'' vs'' heq hd; subst.
    apply svd_split in hd; auto.
  Qed.

  Lemma svd_inv_nil_syms :
    forall gr ys w vs (heq : ys = []),
      sem_values_derivation gr ys w vs
      -> w = [] /\ cast_ss _ _ heq vs = tt.
  Proof.
    intros gr ys w vs heq hd; subst.
    inv hd; ss_inj.
    rewrite cast_ss_refl; auto.
  Qed.

  Lemma svd_inv_terminal_head :
    forall gr a ys ts vs,
      sem_values_derivation gr (T a :: ys) ts vs
      -> exists v ts', ts = @existT _ _ a v :: ts'.
  Proof.
    intros gr a ys ts vs hd; subst.
    inv hd; ss_inj.
    inv_t_der; s_inj.
    repeat eexists; split; eauto.
  Qed.

  Lemma svd_inv_nonterminal_head :
    forall gr x ys ys' ts vs v' vs' (heq : ys = NT x :: ys'),
      sem_values_derivation gr ys ts vs
      -> (v', vs') = cast_ss _ _ heq vs
      -> exists ts' ts'',
        ts = ts' ++ ts''
        /\ sem_value_derivation gr (NT x) ts' v'
        /\ sem_values_derivation gr ys' ts'' vs'.
  Proof.
    intros gr x ys ys' ts vs v' vs' heq hd heq'; subst.
    inv hd; ss_inj.
    rewrite cast_ss_refl in heq'; inv heq'; eauto.
  Qed.

  Lemma svd_terminal_head_contra :
    forall gr a ys vs,
      ~ sem_values_derivation gr (T a :: ys) [] vs.
  Proof.
    unfold not; intros gr a ys vs hd.
    inv hd.
    match goal with
    | H : ?pre ++ ?suf = [] |- _ => apply app_eq_nil in H; destruct H; subst
    end.
    inv_t_der.
  Qed.

  Lemma svd_terminal_head__svd_tl :
    forall g ys a v ys' ts vs (heq : ys = T a :: ys'),
      sem_values_derivation g ys (@existT _ _ a v :: ts) vs
      -> (exists vs',
             (v, vs') = cast_ss _ _ heq vs
             /\ sem_values_derivation g ys' ts vs').
  Proof.
    intros g ys a v ys' ts vs ? hd; subst.
    inv_svs hd hh ht; ss_inj.
    inv hh; s_inj.
    sis; inv_cons_tokens_eq; t_inj.
    rewrite cast_ss_refl; eauto.
  Qed.
  
  (*
  Lemma svd_inv_terminal_head :
    forall gr a ys ys' ts vs v vs' (heq : ys = T a :: ys'),
      sem_values_derivation gr ys ts vs
      -> (v, vs') = cast_ss _ _ heq vs
      -> exists ts', ts = @existT _ _ a v :: ts' /\ sem_values_derivation gr (T a :: ys') (@existT _ _ a v :: ts') (v, vs').
  Proof.
    intros gr a ys ys' ts vs v vs' heq hd heq'; subst.
    rewrite cast_ss_refl in heq'.
    inv hd; ss_inj.
    inv_t_der; s_inj.
    inv_pr_eq; sis.
    eexists; split; eauto.
    rewrite cons_app_singleton with (x := @existT _ _ _ _).
    constructor; auto.
  Qed.                                              
   *)
  
  Inductive tree_corresp_value (g : grammar) :
    forall (s : symbol), list token -> tree -> symbol_semty s -> Prop :=
  | Leaf_corresp :
      forall (a : terminal)
             (v : t_semty a),
        tree_corresp_value g (T a) [@existT _ _ a v] (Leaf a) v
  | Node_corresp :
      forall (x   : nonterminal)
             (ys  : list symbol)
             (w   : list token)
             (sts : forest)
             (vs  : symbols_semty ys)
             (p   : predicate_semty (x, ys))
             (f   : action_semty (x, ys)),
        PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p,f)) g
        -> forest_corresp_values g ys w sts vs
        -> tree_corresp_value g (NT x) w (Node x sts) (f vs)
  with forest_corresp_values (g : grammar) :
         forall (ys : list symbol), list token -> forest -> symbols_semty ys -> Prop :=
  | Nil_corresp :
      forest_corresp_values g [] [] [] tt
  | Cons_corresp :
      forall (s     : symbol)
             (ss    : list symbol)
             (w1 w2 : list token)
             (t     : tree)
             (ts    : forest)
             (v     : symbol_semty s)
             (vs    : symbols_semty ss),
        tree_corresp_value g s w1 t v
        -> forest_corresp_values g ss w2 ts vs
        -> forest_corresp_values g (s :: ss) (w1 ++ w2) (t :: ts) (v, vs).

  Hint Constructors tree_corresp_value forest_corresp_values : core.

  Scheme tcv_mutual_ind := Induction for tree_corresp_value Sort Prop
    with fcv_mutual_ind := Induction for forest_corresp_values Sort Prop.

  Lemma inv_terminal_corresp :
    forall g a w t v,
      tree_corresp_value g (T a) w t v
      -> (w = [@existT _ _ a v]
          /\ t = Leaf a).
  Proof.
    intros g a w t v hc.
    inv hc.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; auto.
    apply Symbol_as_UOT.eq_dec.
  Qed.

  Lemma inv_nonterminal_corresp :
    forall g x w t v,
      tree_corresp_value g (NT x) w t v
      -> (exists ys o f sts vs,
             PM.MapsTo (x, ys) (@existT _ _ (x, ys) (o, f)) g
             /\ t = Node x sts
             /\ v = f vs
             /\ forest_corresp_values g ys w sts vs).
  Proof.
    intros g x w t v hc.
    inv hc.
    repeat eexists; eauto.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; auto.
    apply Symbol_as_UOT.eq_dec.
  Qed.

  Lemma sem_derivation__exists_corresp_tree_derivation :
    forall g s w v,
      sem_value_derivation g s w v
      -> exists t, tree_corresp_value g s w t v.
  Proof.
    intros g s w v hs.
    induction hs using sem_value_derivation_mutual_ind with
        (P  := fun s w v hs =>
                 exists t, tree_corresp_value g s w t v)
        (P0 := fun ss w vs hs =>
                 exists ts, forest_corresp_values g ss w ts vs); eauto.
    - destruct IHhs as [sts hc].
      eexists; eauto.
    - destruct IHhs  as [st hc].
      destruct IHhs0 as [sts hc'].
      exists (st :: sts); auto.
  Qed.

(*  Lemma inv_nt_tcv :
    forall x t v,
      tree_corresp_value (NT x) t v
      -> (exists ys sts vs f,
             t = Node x sts
             /\ forest_corresp_values ys sts vs
             /\ v = f vs).
  Proof.
    intros x t v hc.
    inversion hc as [| ? ? ? ? ? ? h h' heq]; subst; clear hc.
    repeat eexists; eauto.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; eauto.
    apply Symbol_as_UOT.eq_dec.
  Qed.
  
 *)

  Lemma corresp__tree_derivation :
    forall g s w t v,
      tree_corresp_value g s w t v
      -> tree_derivation g s w t.
  Proof.
    intros g s w t v hc.
    induction hc using tcv_mutual_ind with
        (P0 := fun ss w ts vs hc =>
                 forest_derivation g ss w ts); eauto.
    econstructor; eauto.
    eapply pm_mapsto_in; eauto.
  Qed.
    
  Lemma corresp__forest_derivation :
    forall g ss w ts vs,
      forest_corresp_values g ss w ts vs
      -> forest_derivation g ss w ts.
  Proof.
    intros g ss w ts vs hc.
    induction hc using fcv_mutual_ind with
        (P  := fun s w t v hc =>
                 tree_derivation g s w t); eauto.
    econstructor; eauto.
    eapply pm_mapsto_in; eauto.
  Qed.

  Lemma fcv__forests_eq__words_eq_rhss_eq :
    forall g ss ss' pre pre' suf suf' ts vs vs',
      forest_corresp_values g ss pre ts vs
      -> forest_corresp_values g ss' pre' ts vs'
      -> pre ++ suf = pre' ++ suf'
      -> pre' = pre /\ suf' = suf /\ ss' = ss.
  Proof.
    intros g ss ss' pre pre' suf suf' ts vs vs' hc hc' heq.
    apply corresp__forest_derivation in hc.
    apply corresp__forest_derivation in hc'.
    eapply forests_eq__words_eq_rhss_eq; eauto.
  Qed.

  Lemma tree_corresp_values_function' :
    forall (g      : grammar)
           (s : symbol)
           (pre : list token)
           (t : tree)
           (v : symbol_semty s),
      tree_corresp_value g s pre t v
      -> (forall (pre' suf suf' : list token)
                 (v' : symbol_semty s),
             tree_corresp_value g s pre' t v'
             -> pre ++ suf = pre' ++ suf'
             -> pre = pre' /\ suf = suf' /\ v = v').
  Proof.
    intros g s pre t v hc.
    induction hc using tcv_mutual_ind with
        (P  := fun s pre t v hc =>
                 (forall pre' suf suf' v',
                     tree_corresp_value g s pre' t v'
                     -> pre ++ suf = pre' ++ suf'
                     -> pre = pre' /\ suf = suf' /\ v = v'))
        (P0 := fun ss pre ts vs hc =>
                 (forall pre' suf suf' vs',
                     forest_corresp_values g ss pre' ts vs'
                     -> pre ++ suf = pre' ++ suf'
                     -> pre = pre' /\ suf = suf' /\ vs = vs')).
    - intros wpre' wsuf wsuf' v' hc heq.
      apply inv_terminal_corresp in hc.
      destruct hc; subst.
      inv heq.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; subst; auto.
      apply t_eq_dec.
    - intros wpre' wsuf wsuf' v' hc heq.
      apply inv_nonterminal_corresp in hc.
      destruct hc as [ys' [p' [f' [sts' [vs' [hm [heq' [heq'' hc]]]]]]]]; subst.
      inv heq'.
      pose proof hc as hc'.
      eapply fcv__forests_eq__words_eq_rhss_eq
        with (ss := ys) in hc; subst; eauto.
      destruct hc as [? [? ?]]; subst.
      repeat split; auto.
      eapply IHhc in hc'; eauto.
      destruct hc' as [_ [_ ?]]; subst.
      apply PMF.MapsTo_fun
        with (e := @existT _ _ (x,ys) (p,f)) in hm; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in hm.
      + inv hm; auto.
      + apply Production_as_UOT.eq_dec.
    - intros pre suf suf' vs' hc heq; sis; subst.
      inv hc; repeat split; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
      apply Gamma_as_UOT.eq_dec.
    - intros wpre' wsuf wsuf' vs' hc' heq.
      inv hc'.
      repeat rewrite <- app_assoc in heq.
      eapply IHhc in H5; eauto.
      destruct H5 as [? [? ?]]; subst.
      eapply IHhc0 in H6; eauto.
      destruct H6 as [? [? ?]]; subst.
      repeat split; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; auto.
      apply Gamma_as_UOT.eq_dec.
  Qed.

  Lemma tree_corresp_value_function :
    forall (g : grammar)
           (s : symbol)
           (w : list token)
           (t : tree)
           (v v' : symbol_semty s),
      tree_corresp_value g s w t v
      -> tree_corresp_value g s w t v'
      -> v = v'.
  Proof.
    intros g s w t v v' hc hc'.
    eapply tree_corresp_values_function'
      with (suf := []) (suf' := []) (v := v) in hc'; eauto.
    firstorder.
  Qed.
  
  Lemma all_trees_eq__all_sem_values_eq :
    forall g s w v t,
      sem_value_derivation g s w v
      -> tree_corresp_value g s w t v
      -> (forall t', tree_derivation g s w t' -> t' = t)
      -> (forall v', sem_value_derivation g s w v' -> v = v').
  Proof.
    intros g s w v t hd hc hu v' hd'.
    apply sem_derivation__exists_corresp_tree_derivation in hd'.
    destruct hd' as [t' hc'].
    pose proof hc' as hc''.
    apply corresp__tree_derivation in hc''.
    apply hu in hc''; subst.
    eapply tree_corresp_value_function; eauto.
  Qed.
  
  Inductive sym_recognize (g : grammar) : symbol -> list token -> Prop :=
  | T_rec  : 
      forall (a : terminal) (l : t_semty a),
        sym_recognize g (T a) [@existT _ _ a l]
  | NT_rec : 
      forall (x  : nonterminal) (ys : list symbol) (w : list token),
        PM.In (x, ys) g
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

  Lemma tree_derivation__sym_recognize :
    forall g s w v,
      tree_derivation g s w v
      -> sym_recognize g s w.
  Proof.
    intros g ys w v hs.
    induction hs using tree_derivation_mutual_ind
      with (P0 := fun ys w f (hg : forest_derivation g ys w f) => 
                    gamma_recognize g ys w); eauto.
  Qed.

  Lemma gamma_recognize_terminal_head :
    forall g a suf w,
      gamma_recognize g (T a :: suf) w
      -> exists l w',
        w = (@existT _ _ a l) :: w'
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
        /\ PM.In (x, rhs) g
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
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' hg; sis.
    - exists []; exists w''; repeat split; auto.
    - inversion hg as [| s ss wpre wsuf hs hg']; subst; clear hg. 
      apply Ih in hg'; destruct hg' as [w [w' [? [hg' hg'']]]]; subst.
      exists (wpre ++ w); exists w'; repeat split; auto; apps.
  Qed.

  Lemma gamma_recognize_fold_head_nt :
    forall g x rhs ys ts,
      PM.In (x, rhs) g
      -> gamma_recognize g (rhs ++ ys) ts
      -> gamma_recognize g (NT x :: ys) ts.
  Proof.
    intros g x rhs ys ts hi hr.
    apply gamma_recognize_split in hr.
    destruct hr as [w [w' [? [hr hr']]]]; subst; eauto.
  Qed.

  Lemma forest_derivation__gamma_recognize :
    forall g ys w v,
      forest_derivation g ys w v
      -> gamma_recognize g ys w.
  Proof.
    intros g ys w v hg.
    induction hg using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) => 
                sym_recognize g s w); eauto.
  Qed.

  Lemma gamma_recognize__exists_forest_derivation :
    forall g ys w,
      gamma_recognize g ys w
      -> exists v,
        forest_derivation g ys w v.
  Proof.
    intros g ys w hg.
    induction hg using gamma_recognize_mutual_ind with
        (P := fun s w (hs : sym_recognize g s w) => 
                exists t, tree_derivation g s w t);
      firstorder; repeat econstructor; eauto.
  Qed.

  (* A stronger, predicate-aware notion of what it means 
     for the stack to accept the remaining input. For the 
     semantic predicate/action version of CoStar, we use 
     this definition in place of the "remaining symbols 
     recognize the remaining input" invariant. *)
  
  Fixpoint lower_frames_accept_suffix
           (gr  : grammar)
           (ss  : list symbol)
           (vs  : symbols_semty ss)
           (frs : list parser_frame)
           (w   : list token) : Prop :=
    match frs with
    | [] => w = []
    | Fr pre vs_pre (NT x :: suf) :: frs' =>
      (exists wpre wsuf vs_suf p f,
          w = wpre ++ wsuf
          /\ sem_values_derivation gr suf wpre vs_suf
          /\ PM.MapsTo (x, ss) (@existT _ _ (x, ss) (p, f)) gr
          /\ p vs = true
          /\ lower_frames_accept_suffix gr
                                        (rev pre ++ NT x :: suf)
                                        (concatTuple (rev pre) (NT x :: suf) (revTuple _ vs_pre) (f vs, vs_suf))
                                        frs'
                                        wsuf)
    | _ => True
    end.

  Lemma lfas_eq :
    forall gr ys ys' vs vs' frs ts (heq : ys = ys'),
      vs' = cast_ss _ _ heq vs
      -> lower_frames_accept_suffix gr ys vs frs ts
      -> lower_frames_accept_suffix gr ys' vs' frs ts.
  Proof.
    intros gr ys ys' vs vs' frs ts ? ? hl; subst.
    rewrite cast_ss_refl; auto.
  Qed.
  
  Lemma lfas_replace_head :
    forall gr ys x zs vs v v' vs'' frs w,
      lower_frames_accept_suffix gr (ys ++ NT x :: zs) (concatTuple ys (NT x :: zs) vs (v, vs'')) frs w
      -> v = v'
      -> lower_frames_accept_suffix gr (ys ++ NT x :: zs) (concatTuple ys (NT x :: zs) vs (v', vs'')) frs w.
  Proof.
    intros; subst; auto.
  Qed.

  Definition stack_accepts_suffix (gr : grammar) (sk : parser_stack) (w : list token) : Prop :=
    match sk with
    | (Fr pre vs_pre suf, frs) =>
      (exists wpre wsuf vs_suf,
          w = wpre ++ wsuf
          /\ sem_values_derivation gr suf wpre vs_suf
          /\ lower_frames_accept_suffix gr
                                        (rev pre ++ suf)
                                        (concatTuple (rev pre) suf (revTuple pre vs_pre) vs_suf)
                                        frs
                                        wsuf)
       end.

  (* General-purpose tactic for solving equalities with dependent types *)
  Ltac t :=
    match goal with
    | |- context[revTuple_cons_case] =>
      unrt
    | |- lower_frames_accept_suffix _ _ (concatTuple _ _ _ ((cast_action _ _ _ _) _, _)) _ _ =>
      eapply lfas_replace_head; eauto
    | |- concatTuple ?xs ?ys ?vx ?vy = cast_ss (?xs' ++ ?ys) (?xs ++ ?ys) ?pf (concatTuple ?xs' ?ys ?vx' ?vy') =>
      eapply concatTuple_eq with (heq := app_inv_tail  _ _ _ pf)
    | |- concatTuple ?pre (?s :: ?suf) _ _ = cast_ss _ _ _ (concatTuple ?pre' ([?s] ++ ?suf) _ _) =>
      eapply concatTuple_eq
    | |- context[cast_ss ?xs ?xs _ _] =>
      rewrite cast_ss_refl
    | |- (?a, ?b) = (?a', ?b') =>
      apply pair_split_eq
    | |- ?f ?vs = (cast_action _ _ _ ?f) ?vs' =>
      eapply cast_action_eq
    | |- context[concatTuple (rev (rev ?xs)) []] =>
      erewrite rrt_anr
    | |- (cast_predicate _ _ _ _) _ = true =>
      eapply cast_predicate_eq_true; eauto
    | |- context[concatTuple (_ ++ [_]) _ (concatTuple _ [_] _ _) _] => erewrite concatTuple_assoc'
    | |- context[cast_ss _ _ _ (cast_ss _ _ _ _)] =>
      erewrite <- cast_ss_ins_trans
    | |- context[revTuple _ (revTuple _ _)] =>
      erewrite revTuple_involutive
    | |- PM.MapsTo _ (@existT _ _ _ (cast_predicate _ _ _ _, cast_action _ _ _ _)) _ =>
      eapply mapsto_cast; eauto
    end.

  Ltac t' := repeat t.
  
  Lemma return_preserves_sas :
    forall gr ce cr cr' pre' vs' pre vs x suf frs p f ts,
      ce = Fr pre' vs' []
      -> cr = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) (f (revTuple _ vs'), vs) suf
      -> PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) gr
      -> p (revTuple _ vs') = true
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> stack_accepts_suffix gr (cr', frs) ts.
  Proof.
    intros gr ce cr cr' pre' vs' pre vs x suf frs p f ts ? ? ? hm hp hs; subst; sis.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hex); subst.
    destruct hex as (wsuf' & wsuf'' & vs_suf' & p' & f' & heq & hd' & hm' & hp' & hl); subst.
    destruct vs_suf.
    apply svd_inv_nil_syms in hd; subst; sis; auto.
    exists wsuf'; exists wsuf''; eexists; repeat split; eauto.
    t'; sis; repeat unct.
    eapply lfas_eq; eauto.
    eapply lfas_replace_head; eauto.
    eapply mapsto_cast with (x' := (x, rev pre'))
                            (z  := (x, rev pre')) in hm'; eauto; apps.
    eapply PMF.MapsTo_fun with (e := @existT _ _ (x, rev pre') (p, f)) in hm'; auto.
    apply inv_grammar_entry_eq in hm'.
    destruct hm' as [hpeq hfeq].
    rewrite hfeq.
    t'.
    erewrite concatTuple_nil_r; eauto.
    t'; auto.
    Unshelve.
    all : apps.
  Qed.

  Lemma failed_predicate_contra :
    forall x ys ys' (p : predicate_semty (x, ys)) (p' : predicate_semty (x, ys')) vs vs'
           (heq : ys = ys') (heq' : (x, ys) = (x, ys')),
      vs' = cast_ss _ _ heq vs
      -> p' = cast_predicate _ _ heq' p
      -> ~ p vs <> p' vs'.
  Proof.
    intros x ys ys' p p' vs vs' ? ? ? ?; subst.
    unfold not; intros hp.
    apply hp.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.
    
  Lemma sas_failed_predicate_contra :
    forall gr ce cr pre' vs' pre vs x suf frs p f ts,
      ce = Fr pre' vs' []
      -> cr = Fr pre vs (NT x :: suf)
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) gr
      -> p (revTuple _ vs') <> false.
  Proof.
    intros gr ce cr pre' vs' pre vs x suf frs p f ts ? ? hs hm hp; subst.
    red in hs.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
    destruct hl as (wsuf' & wsuf'' & vs_suf' & p' & f' & heq & hd' & hm' & hp' & hl); subst.
    destruct vs_suf.
    eapply failed_predicate_contra with
        (x := x)
        (p := p)
        (vs := revTuple _ vs')
        (p' := p')
        (vs'  := concatTuple _ [] (revTuple _ vs') tt); tc.
    - erewrite concatTuple_nil_r; eauto.
    - eapply mapsto_cast with (x' := (x, rev pre'))
                              (z  := (x, rev pre')) in hm'; eauto; apps.
      eapply PMF.MapsTo_fun with (e := @existT _ _ (x, rev pre') (p, f)) in hm'; auto.
    apply inv_grammar_entry_eq in hm'.
    destruct hm' as [hpeq hfeq].
    rewrite hpeq.
    rewrite cast_predicate_roundtrip; auto.
    Unshelve.
    all : apps.
  Qed.

  Lemma sas_find_neq_None :
    forall gr rm cr pre vs x suf frs ts,
      cr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> stack_accepts_suffix gr (cr, frs) ts
      -> NM.find x rm <> None.
  Proof.
    intros gr rm cr pre vs x suf frs ts ? hr hs hf; subst.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
    inv_svs hd hh ht.
    inv_sv hh hm hvs hp.
    apply pm_mapsto_in in hm.
    destruct hr as (_ & _ & hc).
    apply hc in hm.
    destruct hm as [yss [hm hi]].
    apply NMF.find_mapsto_iff in hm; tc.
  Qed.

  (* Inductive definition of a nullable grammar symbol *)
  Inductive nullable_sym (g : grammar) : symbol -> Prop :=
  | NullableSym : forall x ys,
      PM.In (x, ys) g
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
    intros g xs; induction xs as [| x xs Ih]; intros ys hn; sis; auto.
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
      PM.In (x, gamma) g
      -> gamma = pre ++ NT z :: suf
      -> nullable_gamma g pre
      -> nullable_path g (NT x) (NT z)
  | IndirectPath : forall x y z gamma pre suf,
      PM.In (x, gamma) g
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
