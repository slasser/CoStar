Require Import List.
Import ListNotations.

(* unwrap a list of options, returning a list of the values wrapped by Some *)
Definition extractSomes {A} (os : list (option A)) : list A :=
  fold_right (fun o l => match o with
                         | None   => l
                         | Some a => a :: l
                         end) [] os.

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

Definition allEqual_opt (A : Type) (beq : A -> A -> bool) (x : A) (xs : list A) : option A :=
  if forallb (beq x) xs then Some x else None.