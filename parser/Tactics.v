Require Import List.

Ltac sis := simpl in *.

Ltac inv H := inversion H; subst; clear H.

Ltac tc := try congruence.

(* destruct a match in a hypothesis *)
Ltac dmh := match goal with
             | H : context[match ?x with | _ => _ end] |- _ => destruct x
             end.

(* destruct a match in the goal *)
Ltac dmg := match goal with
             | |- context[match ?x with | _ => _ end] => destruct x
             end.

Ltac dm  := (first [dmh | dmg]); auto.

Ltac dms := repeat dm.

(* destruct a match in a hypothesis, and save the equality in the context *)
Ltac dmheq s := let Heq := fresh s in
                match goal with
                | H : context[match ?x with | _ => _ end] |- _ =>
                  destruct x eqn:Heq
                end.

(* destruct a match in the goal, and save the equality in the context *)
Ltac dmgeq s := let Heq := fresh s in
                match goal with
                | |- context[match ?x with | _ => _ end] => destruct x eqn:Heq
                end.

Ltac dmeq s := (first [dmheq s | dmgeq s]); auto.

Ltac dmeqs s := repeat dmeq s.

Ltac apps := try solve [ repeat rewrite app_assoc; auto
                       | repeat rewrite <- app_assoc; auto
                       | repeat rewrite app_nil_r; auto].

Ltac rew_anr := repeat rewrite app_nil_r in *.

