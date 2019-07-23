Require Import Arith List.
Require Import Defs.
Import ListNotations.

Definition headFrameSize (fr : l_frame) : nat :=
  match fr with
  | (_, _, suf) => List.length suf
  end.

Definition headFrameScore (fr : l_frame) (b : nat) (e : nat) : nat :=
  headFrameSize fr * (b ^ e).

Definition tailFrameSize (fr : l_frame) : nat :=
  match fr with
  | (_, _, suf) =>
    match suf with
    | [] => 0
    | _ :: suf' => List.length suf'
    end
  end.

Definition tailFrameScore (fr : l_frame) (b : nat) (e : nat) : nat :=
  tailFrameSize fr * (b ^ e).

Fixpoint tailFramesScore (frs : list l_frame) (b : nat) (e : nat) : nat :=
  match frs with
  | []         => 0
  | fr :: frs' => tailFrameScore fr b e + tailFramesScore frs' b (1 + e)
  end.

Definition stackScore (stk : l_stack) (b : nat) (e : nat) : nat :=
  let (h_fr, t_frs) := stk
  in  headFrameScore h_fr b e + tailFramesScore t_frs b (1 + e).

Definition stackHeight (stk : l_stack) : nat :=
  let (_, frs) := stk in List.length frs.

Definition rhsLengths (g : grammar) : list nat :=
  map (fun rhs => List.length rhs) (rhss g).

Definition maxRhsLength (g : grammar) : nat :=
  listMax (rhsLengths g).

