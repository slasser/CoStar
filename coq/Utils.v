Require Import List Omega.
Require Import GallStar.Tactics.
Import ListNotations.

(* DEFINITIONS BUILT FROM STANDARD LIBRARY CONCEPTS *)

(* unwrap a list of options, returning a list of the values wrapped by Some *)
Definition extractSomes {A} (os : list (option A)) : list A :=
  fold_right (fun o l => match o with
                         | None   => l
                         | Some a => a :: l
                         end) [] os.

Definition listMax (xs : list nat) : nat := 
  fold_right max 0 xs.

(* A single (inl a) element of es causes the entire result to be (inl a) *)
Fixpoint sumOfListSum {A B} (es : list (sum A B)) : sum A (list B) :=
  match es with
  | []         => inr []
  | inl a :: _ => inl a
  | inr b :: t =>
    match sumOfListSum t with
    | inl a  => inl a
    | inr bs => inr (b :: bs)
    end
  end.

Definition dflat_map {A B : Type} :
  forall (l : list A) (f : forall x, In x l -> list B), list B.
  refine(fix dfm (l : list A) (f : forall x, In x l -> list B) :=
           match l as l' return l = l' -> _ with
           | []     => fun _ => []
           | h :: t => fun Heq => (f h _) ++ (dfm t _)
           end eq_refl).
  - subst.
    apply in_eq.
  - subst; intros x Hin.
    assert (Ht : In x (h :: t)).
    { apply in_cons; auto. }
    eapply f; eauto.
Defined.

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

Definition allEqual (A : Type) (beq : A -> A -> bool) (x : A) (xs : list A) : bool :=
  forallb (beq x) xs.

(* LEMMAS ABOUT STANDARD LIBRARY DEFINITIONS *)

Lemma app_nil_r' : forall A (xs : list A), xs = xs ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Lemma cons_app_singleton :
  forall A (x : A) (ys : list A),
    x :: ys = [x] ++ ys.
Proof.
  auto.
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
Defined.

Lemma in_singleton_eq :
  forall A (x x' : A), In x' [x] -> x' = x.
Proof.
  intros A x x' Hin.
  destruct Hin as [Hhd | Htl]; auto.
  inv Htl.
Qed.

Lemma list_elt_le_listmax :
  forall (x : nat) (ys : list nat),
    In x ys -> x <= listMax ys.
Proof.
  intros x ys Hin; induction ys as [| y ys IH]; simpl in *.
  - inv Hin.
  - destruct Hin as [Heq | Hin]; subst.
    + apply Max.le_max_l.
    + apply IH in Hin.
      eapply le_trans; eauto.
      apply Max.le_max_r.
Qed.

Lemma sumOfListSum_failure_in_input :
  forall A B (es : list (sum A B)) (a : A),
    sumOfListSum es = inl a
    -> In (inl a) es.
Proof.
  intros A B es a hs.
  induction es as [| e es IH]; sis; tc.
  destruct e as [a' | b].
  - inv hs; auto.
  - dmeq hs; tc.
Qed.

Lemma in_dmap :
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