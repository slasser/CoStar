Require Import List Omega Relations Relation_Operators.
Require Import CoStar.Tactics.
        Import ListNotations.

(* STANDARD LIBRARY-LIKE DEFINITIONS *)

Definition allEqual (A : Type) (beq : A -> A -> bool) (x : A) (xs : list A) : bool :=
  forallb (beq x) xs.

Definition dmap {A B : Type} :
  forall (l : list A) (f : forall (x : A), In x l -> B), list B.
  refine(fix dmap (l : list A) (f : forall x, In x l -> B) :=
           match l as l' return l = l' -> _ with
           | []     => fun _ => []
           | h :: t => fun Heq => (f h _) :: (dmap t _)
           end eq_refl).
  - subst.
    apply in_eq.
  - subst; intros x Hin.
    apply f with (x := x).
    apply in_cons; auto.
Defined.

Lemma dmap_in :
  forall (A B : Type) 
         (l   : list A) 
         (f   : forall a, In a l -> B) 
         (b   : B) 
         (bs  : list B),
    dmap l f = bs
    -> In b bs
    -> (exists a hi, In a l /\ f a hi = b).
Proof.
  intros A B l f b bs hd hi; subst.
  induction l as [| a l IH].
  - inv hi.
  - destruct hi as [hh | ht].
    + exists a; eexists; split; eauto.
      apply in_eq.
    + apply IH in ht; destruct ht as [a' [hi [hi' heq]]].
      exists a'; eexists; split.
      * apply in_cons; auto.
      * apply heq.
Qed.

Definition listMax (xs : list nat) : nat := 
  fold_right max 0 xs.

Lemma listMax_in_le :
  forall (x : nat) (ys : list nat),
    In x ys
    -> x <= listMax ys.
Proof.
  intros x ys Hin; induction ys as [| y ys IH]; simpl in *.
  - inv Hin.
  - destruct Hin as [Heq | Hin]; subst.
    + apply Max.le_max_l.
    + apply IH in Hin.
      eapply le_trans; eauto.
      apply Max.le_max_r.
Qed.

(* Lemmas about standard library definitions *)

Lemma app_nil_r' : forall A (xs : list A), xs = xs ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Ltac rew_nil_r xs :=
  let heq := fresh "heq" in
  assert (heq : xs = xs ++ []) by apply app_nil_r'; rewrite heq; clear heq.

Lemma cons_app_singleton :
  forall A (x : A) (ys : list A),
    x :: ys = [x] ++ ys.
Proof.
  auto.
Qed.

Lemma cons_inv_eq :
  forall A (x x' : A) (xs xs' : list A),
    x :: xs = x' :: xs'
    -> x' = x /\ xs' = xs.
Proof.
  intros A x x' xs xs' heq.
  inv heq; auto.
Qed.

Lemma filter_cons_in :
  forall (A : Type) (f : A -> bool) (l : list A) (hd : A) (tl : list A),
    filter f l = hd :: tl
    -> In hd l.
Proof.
  intros A f l hd tl Hf.
  assert (Hin : In hd (hd :: tl)) by apply in_eq.
  rewrite <- Hf in Hin.
  apply filter_In in Hin; destruct Hin as [Hp _]; auto.
Qed.

Lemma filter_tail_in :
  forall (A : Type) (f : A -> bool) (l : list A) (h x : A) (t : list A) ,
    filter f l = h :: t
    -> In x t
    -> In x l.
Proof.
  intros A f l h x t hf hi.
  assert (hi' : In x (filter f l)).
  { rewrite hf; apply in_cons; auto. }
  apply filter_In in hi'; destruct hi'; auto.
Qed.

Lemma in_singleton_eq :
  forall A (x x' : A),
    In x' [x]
    -> x' = x.
Proof.
  intros A x x' Hin.
  destruct Hin as [Hhd | Htl]; auto.
  inv Htl.
Qed.

Lemma Forall_In :
  forall (A : Type) (P : A -> Prop) (x : A) (xs : list A),
    Forall P xs -> In x xs -> P x.
Proof.
  intros A P x xs hf hi.
  eapply Forall_forall; eauto.
Qed.    
         
Lemma app_left_identity_nil :
  forall A (xs ys : list A),
    xs ++ ys = ys 
    -> xs = [].
Proof.
  intros A xs ys heq.
  eapply app_inv_tail.
  rewrite <- app_nil_l in heq; eauto.
Qed.

Lemma app_double_left_identity_nil :
  forall A (xs ys zs : list A),
    xs ++ ys ++ zs = zs
    -> xs = [] /\ ys = [].
Proof.
  intros A xs ys zs heq.
  apply app_eq_nil.
  eapply app_left_identity_nil; rewrite <- app_assoc; eauto.
Qed.

Lemma cons_neq_tail :
  forall A x (xs : list A),
    (x :: xs) <> xs.
Proof.
  intros A x xs; unfold not; intros heq.
  assert (heq' : [x] ++ xs = [] ++ xs) by apps.
  apply app_inv_tail in heq'; inv heq'.
Qed.

(* Variant of filter_In that removes the conjunction *)
Lemma filter_In' :
  forall A (f : A -> bool) x l,
    In x l 
    -> f x = true 
    -> In x (filter f l).
Proof.
  intros; apply filter_In; auto.
Qed.

Lemma app_cons_group_l :
  forall A (xs zs : list A) (y : A),
    xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof.
  intros A xs zs y; rewrite <- app_assoc; auto.
Qed.

Lemma app_group_endpoints_l :
  forall A (x y : A) (xs ys : list A),
    x :: xs ++ y :: ys = (x :: xs ++ [y]) ++ ys.
Proof.
  intros A x y xs ys; simpl; apps.
Qed.

(* Get the bottom element of a stack, where stack ::= A * list A *)
Fixpoint bottomElt' {A} (h : A) (t : list A) : A :=
  match t with
  | []        => h
  | h' :: t' => bottomElt' h' t'
  end.

Definition bottomElt {A} (stk : A * list A) : A :=
  let (h, t) := stk in bottomElt' h t.

Lemma rev_eq__eq :
  forall A (xs ys : list A),
    rev xs = rev ys -> xs = ys.
Proof.
  intros A xs; induction xs as [| x xs IH]; intros ys heq; sis.
  - destruct ys as [| y ys]; sis; auto.
    apply app_cons_not_nil in heq; inv heq.
  - destruct ys as [| y ys]; sis.
    + symmetry in heq; apply app_cons_not_nil in heq; inv heq.
    + apply app_inj_tail in heq; destruct heq as [heq ?]; subst.
      apply IH in heq; subst; auto.
Qed.

Definition oneToMany {A B : Type} (s : A) (ds : list B) : list (A * B) :=
  map (pair s) ds.

Lemma oneToMany_src_eq :
  forall A B (a a' : A) (b : B) (bs : list B),
    In (a, b) (oneToMany a' bs)
    -> a' = a.
Proof.
  intros A B a a' b bs hi.
  apply in_map_iff in hi. destruct hi as [b' [heq hi]]; inv heq; auto.
Qed.

Lemma oneToMany_dst_in :
  forall A B (a a' : A) (b : B) (bs : list B),
    In (a, b) (oneToMany a' bs)
    -> In b bs.
Proof.
  intros A B a a' b bs hi.
  apply in_map_iff in hi; destruct hi as [? [heq ?]]; inv heq; auto.
Qed.

(* idea : use this for closure_step / closure_multistep *)
Lemma clos_t_rt :
  forall (A : Type) (R : relation A) (x y z : A),
    clos_trans A R x y
    -> clos_refl_trans A R y z
    -> clos_trans A R x z.
Proof.
  intros A R x y z ht hr.
  induction hr; eauto.
  eapply t_trans; eauto.
  apply t_step; auto.
Qed.


Lemma flat_map_nil__f_nil :
  forall X Y (f : X -> list Y) xs x,
    flat_map f xs = []
    -> In x xs
    -> f x = [].
Proof.
  intros X Y f xs x hf hi; induction xs as [| x' xs IH]; sis.
  - inv hi.
  - destruct hi; subst; apply app_eq_nil in hf; destruct hf; auto.
Qed.    

Lemma filter_nil__f_false :
  forall X (f : X -> bool) (x : X) (xs : list X),
    filter f xs = []
    -> In x xs
    -> f x = false.
Proof.
  intros X f x xs hf hi.
  induction xs as [| x' xs IH]; sis.
  - inv hi.
  - destruct hi as [hh | ht]; subst; dm; auto; inv hf.
Qed.

Lemma fold_right_unroll :
  forall X Y (f : X -> Y -> Y) (y : Y) (x : X) (xs : list X),
    fold_right f y (x :: xs) = f x (fold_right f y xs).
Proof.
  auto.
Qed.

Fixpoint tuple' (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod (tuple' xs') x
  end.

Definition tuple (xs : list Type) : Type :=
  tuple' (rev xs).

Lemma fold_left_preserves_list_invar' :
    forall (A B   : Type)
           (f     : A -> B -> A)
           (xs ys : list B)
           (a     : A)
           (P     : A -> list B -> Prop),
      P a xs
      -> (forall a b bs, P a bs -> P (f a b) (bs ++ [b]))
      -> P (fold_left f ys a) (xs ++ ys).
  Proof.
    intros A B f xs ys; revert xs. 
    induction ys as [| y ys IH]; intros xs a P ha hf; sis.
    - rew_anr; auto.
    - apply hf with (b := y) in ha.
      apply IH with (xs := xs ++ [y]) in ha; auto.
      rewrite cons_app_singleton; apps.
  Qed.

  Lemma fold_left_preserves_list_invar :
    forall (A B : Type)
           (f   : A -> B -> A)
           (bs  : list B)
           (a   : A)
           (P   : A -> list B -> Prop),
      P a []
      -> (forall a b bs, P a bs -> P (f a b) (bs ++ [b]))
      -> P (fold_left f bs a) bs.
  Proof.
    intros.
    rewrite <- app_nil_l.
    apply fold_left_preserves_list_invar'; auto.
  Qed.

  Lemma exists_in_app_l :
    forall (A     : Type)
           (xs ys : list A),
      (exists x, In x xs)
      -> exists x, In x (xs ++ ys).
  Proof.
    intros A xs ys [x Hi].
    eexists; apply in_or_app; left; eauto.
  Qed.
