Require Import List OrderedType OrderedTypeAlt OrderedTypeEx.
Require Import GallStar.Tactics.
Import ListNotations.

Module Type UsualComparableType.

  Parameter t : Type.

  Parameter compare : t -> t -> comparison.

  Parameter compare_eq :
    forall x y : t,
      compare x y = Eq <-> x = y. 

  Parameter compare_trans :
    forall (c : comparison) (x y z : t),
      compare    x y = c
      -> compare y z = c
      -> compare x z = c.

End UsualComparableType.

Module UOT_from_UCT (C : UsualComparableType) <: UsualOrderedType.

  Definition t := C.t.
  
  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt (x y : t) : Prop :=
    match C.compare x y with
    | Lt => True
    | _  => False
    end.

  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z hlt hlt'.
    destruct (C.compare x y) eqn:hc  ;
      destruct (C.compare y z) eqn:hc' ;
      destruct (C.compare x z) eqn:hc''; auto.
    - eapply C.compare_trans in hc'; eauto; tc.
    - eapply C.compare_trans in hc'; eauto; tc.
  Qed.
  
  Lemma lt_not_eq :
    forall x y, lt x y -> ~ x = y.
  Proof.
    unfold lt; intros x y hl heq.
    apply C.compare_eq in heq.
    rewrite heq in hl; inv hl.
  Qed.

  Lemma compare_refl :
    forall x, C.compare x x = Eq.
  Proof.
    intros x; apply C.compare_eq; auto.
  Qed.
  
  Lemma compare_sym :
    forall x y, C.compare x y = CompOpp (C.compare y x).
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - apply C.compare_eq in hc; subst.
      rewrite compare_refl; auto.
    - destruct (C.compare y x) eqn:hc'; auto.
      + exfalso; apply C.compare_eq in hc'; subst.
        rewrite compare_refl in hc; tc.
      + exfalso; eapply C.compare_trans in hc'; eauto.
        rewrite compare_refl in hc'; tc.
    - destruct (C.compare y x) eqn:hc'; auto.
      + exfalso; apply C.compare_eq in hc'; subst.
        rewrite compare_refl in hc; tc.
      + exfalso; eapply C.compare_trans in hc'; eauto.
        rewrite compare_refl in hc'; tc.
  Qed.

  Definition compare :
    forall x y,
      Compare lt eq x y.
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - apply EQ; apply C.compare_eq; auto.
    - apply LT; unfold lt; rewrite hc; auto.
    - apply GT; unfold lt; rewrite compare_sym in hc.
      destruct (C.compare y x) eqn:hc'; sis; tc; auto.
  Defined.

  Definition eq_dec :
    forall x y : t,
      {x = y} + {x <> y}.
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - left; apply C.compare_eq; auto.
    - right; intros heq; apply C.compare_eq in heq; tc.
    - right; intros heq; apply C.compare_eq in heq; tc.
  Defined.
  
End UOT_from_UCT.

Module Option_as_UOT (E : UsualOrderedType) <: UsualOrderedType.

  Definition t := option E.t.

  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt o o' :=
    match o, o' with
    | None, None     => False
    | None, Some _   => True
    | Some _, None   => False
    | Some x, Some y => E.lt x y
    end.

  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z hl hl';
      destruct x as [x |]; destruct y as [y |]; destruct z as [z |];
        try contradiction; auto.
    eapply E.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq :
    forall x y,
      lt x y -> ~ x = y.
  Proof.
    intros x y hl heq; destruct x as [x |]; destruct y as [y |]; tc; auto.
    inv heq; eapply E.lt_not_eq; eauto.
    red; auto.
  Qed.

  Definition compare :
    forall x y,
      Compare lt eq x y.
  Proof.
    intros x y; destruct x as [x |]; destruct y as [y |].
    - destruct (E.compare x y) as [hl | he | hl].
      + apply LT; unfold lt; auto.
      + apply EQ; red; red in he; subst; auto.
      + apply GT; unfold lt; auto.
    - apply GT; red; auto.
    - apply LT; red; auto.
    - apply EQ; red; auto.
  Defined.

  Definition eq_dec :
    forall x y : t,
      {x = y} + {x <> y}.
  Proof.
    intros x y; destruct (compare x y) as [hl | he | hl].
    - right; apply lt_not_eq; auto.
    - left; subst; auto.
    - right; intros he; subst.
      eapply lt_not_eq; eauto.
  Defined.

End Option_as_UOT.

Module List_as_UOT (E : UsualOrderedType) <: UsualOrderedType.

  Definition t := list E.t.

  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Fixpoint lt xs ys :=
    match xs, ys with
    | [], []             => False
    | [], _ :: _         => True
    | _ :: _, []         => False
    | x :: xs', y :: ys' =>
      match E.compare x y with
      | LT _ => True
      | EQ _ => lt xs' ys'
      | GT _ => False
      end
    end.

  Lemma lt_trans_heads_eq :
    forall x y xs ys zs,
      lt (x :: xs) (y :: ys)
      -> lt (y :: ys) (x :: zs)
      -> y = x.
  Proof.
    intros x y xs ys zs hl hl'; red in hl, hl'.
    destruct (E.compare x y) as [hel | hee | hel];
      destruct (E.compare y x) as [hel' | hee' | hel'];
      try contradiction; auto.
    eapply E.lt_trans in hel'; eauto.
    exfalso; eapply E.lt_not_eq; eauto; red; auto.
  Qed.

  Lemma lt_inv_cons :
    forall x xs ys,
      lt (x :: xs) (x :: ys)
      -> lt xs ys.
  Proof.
    intros x xs ys hl; red in hl.
    destruct (E.compare x x); try contradiction; auto.
    exfalso; eapply E.lt_not_eq; eauto; red; auto.
  Qed.

  Lemma lt_trans_heads_lt_or_eq :
    forall x y z xs ys zs,
      lt (x :: xs) (y :: ys)
      -> lt (y :: ys) (z :: zs)
      -> E.lt x z \/ z = x.
  Proof.
    intros x y z xs ys zs hl hl'; red in hl, hl'.
    destruct (E.compare x y) as [hel | hee | hel];
      destruct (E.compare y z) as [hel' | hee' | hel'];
      try contradiction; auto.
    - left; eapply E.lt_trans; eauto.
    - left; red in hee'; subst; auto.
    - left; red in hee ; subst; auto.
    - right; red in hee; red in hee'; subst; auto.
  Qed.
  
  Lemma lt_trans :
    forall xs ys zs,
      lt xs ys -> lt ys zs -> lt xs zs.
  Proof.
    intros xs; induction xs as [| x xs IH];
      intros ys zs hl hl'; destruct ys as [| y ys]; destruct zs as [| z zs]; try contradiction; auto.
    red; destruct (E.compare x z) as [hel | hee | hel]; auto.
    - fold lt; red in hee; subst.
      assert (heq : y = z) by (eapply lt_trans_heads_eq; eauto); subst.
      apply lt_inv_cons in hl; apply lt_inv_cons in hl'; eauto.
    - eapply lt_trans_heads_lt_or_eq in hl'; eauto.
      destruct hl' as [hl' | ?]; subst.
      + eapply E.lt_trans in hl'; eauto.
        eapply E.lt_not_eq; eauto; red; auto.
      + eapply E.lt_not_eq; eauto; red; auto.
  Qed.
  
  Lemma lt_not_eq :
    forall xs ys,
      lt xs ys -> ~ xs = ys.
  Proof.
    intros xs; induction xs as [| x xs IH];
      intros ys hl heq; destruct ys as [| y ys]; tc; inv heq; auto.
    red in hl; destruct (E.compare y y); tc.
    - eapply E.lt_not_eq; eauto; red; auto.
    - eapply IH; eauto. 
  Qed.

  Definition compare :
    forall xs ys,
      Compare lt eq xs ys.
  Proof.
    intros xs; induction xs as [| x xs IH]; intros ys; destruct ys as [| y ys].
    - apply EQ; red; auto.
    - apply LT; red; auto.
    - apply GT; red; auto.
    - destruct (E.compare x y) as [hl | he | hl] eqn:hc.
      + apply LT; red; rewrite hc; auto.
      + red in he; subst.
        destruct (IH ys) as [hl' | he' | hl'].
        * apply LT; red; rewrite hc; auto.
        * apply EQ; tc.
        * apply GT; red; rewrite hc; auto.
      + apply GT; red.
        destruct (E.compare y x) as [hl' | he' | hl']; auto.
        * red in he'; subst.
          exfalso; eapply E.lt_not_eq; eauto; red; auto.
        * eapply E.lt_trans in hl'; eauto.
          eapply E.lt_not_eq; eauto; red; auto.
  Defined.

  Definition eq_dec :
    forall xs ys : t,
      {xs = ys} + {xs <> ys}.
  Proof.
    intros xs ys; destruct (compare xs ys) as [hl | he | hl].
    - right; apply lt_not_eq; auto.
    - left; subst; auto.
    - right; intros he; subst.
      eapply lt_not_eq; eauto.
  Defined.

End List_as_UOT.

Module Nat_as_OT_Alt <: OrderedTypeAlt := OrderedType_to_Alt Nat_as_OT.

(* Dumping this here for now *)


(*


Lemma foo :
  forall x y,
    compareNT x y = NO.compare (nat_of_nt x) (nat_of_nt y).
Proof.
  intros x y; destruct x; destruct y; auto.
Qed.

Lemma compareNT_sym :
  forall x y,
  compareNT y x = CompOpp (compareNT x y).
Proof.
  intros x y; repeat rewrite foo.
  apply NO.compare_sym.
Qed.

Lemma compareNT_trans :
  forall c x y z,
    compareNT    x y = c
    -> compareNT y z = c
    -> compareNT x z = c.
Proof.
  intros c x y z hc hc'.
  repeat rewrite foo in *.
  eapply NO.compare_trans; eauto.
Qed.

Module NT_as_OT_Alt <: OrderedTypeAlt.
  Definition t := nonterminal.
  Definition compare := compareNT.
  Definition compare_sym := compareNT_sym.
  Definition compare_trans := compareNT_trans.
End NT_as_OT_Alt.

Module NT_as_OT <: OrderedType := OrderedType_from_Alt NT_as_OT_Alt.
*)

(*
  Module NT_as_UOT <: UsualOrderedType.

    Definition t := nonterminal.

    Definition eq       := @eq nonterminal.
    Definition eq_refl  := @eq_refl nonterminal.
    Definition eq_sym   := @eq_sym nonterminal.
    Definition eq_trans := @eq_trans nonterminal.

    Definition lt (x y : nonterminal) : Prop :=
      match compareNT x y with
      | Lt => True
      | _  => False
      end.

    Lemma lt_trans :
      forall x y z, lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros x y z hlt hlt'.
        destruct (compareNT x y) eqn:hb  ;
        destruct (compareNT y z) eqn:hb' ;
        destruct (compareNT x z) eqn:hb''; auto.
      - eapply compareNT_trans in hb'; eauto; tc.
      - eapply compareNT_trans in hb'; eauto; tc.
    Qed.
    
    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros x y hl heq.
      apply compareNT_eq in heq.
      rewrite heq in hl; inv hl.
    Qed.

    Lemma compareNT_refl :
      forall x, compareNT x x = Eq.
    Proof.
      intros x; apply compareNT_eq; auto.
    Qed.

    Lemma compareNT_sym :
      forall x y, compareNT x y = CompOpp (compareNT y x).
    Proof.
      intros x y; destruct (compareNT x y) eqn:hc.
      - apply compareNT_eq in hc; subst.
        rewrite compareNT_refl; auto.
      - destruct (compareNT y x) eqn:hc'; auto.
        + exfalso; apply compareNT_eq in hc'; subst.
          rewrite compareNT_refl in hc; tc.
        + exfalso; eapply compareNT_trans in hc'; eauto.
          rewrite compareNT_refl in hc'; tc.
      - destruct (compareNT y x) eqn:hc'; auto.
        + exfalso; apply compareNT_eq in hc'; subst.
          rewrite compareNT_refl in hc; tc.
        + exfalso; eapply compareNT_trans in hc'; eauto.
          rewrite compareNT_refl in hc'; tc.
    Qed.

    Definition compare :
      forall x y,
        Compare lt eq x y.
    Proof.
      intros x y; destruct (compareNT x y) eqn:hc.
      - apply EQ; apply compareNT_eq; auto.
      - apply LT; unfold lt; rewrite hc; auto.
      - apply GT; unfold lt; rewrite  compareNT_sym in hc.
        destruct (compareNT y x) eqn:hc'; sis; tc; auto.
    Defined.

    Definition eq_dec := nt_eq_dec.
    
  End NT_as_UOT.
 *)
