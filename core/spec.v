(** * Specifications

    Section 7 of Swierstra and Baanen, ICFP 2019 (used from Section 3 onwards).

<<
      record Spec (a : Set) (b : a -> Set) : Set where
        constructor [[_,_]]
        field
          pre  : a -> Set
          post : (x : a) -> b x -> Set

      wpSpec : Spec a b -> (P : (x : a) -> b x -> Set) -> (a -> Set)
      wpSpec [[ pre , post ]] P = \x -> pre x /\ (forall y -> post x y -> P x y)
>>

    A specification is a pre/postcondition pair; [wp_spec] maps it to a
    predicate transformer, so specifications and programs are compared in one
    and the same semantic domain. This is what makes the refinement calculus of
    Section 7 possible. *)

From pt_effects.core Require Import wp.

Record spec (A : Type) (B : A -> Type) : Type :=
  Spec { pre : A -> Prop; post : forall x : A, B x -> Prop }.

Arguments Spec {A B} _ _.
Arguments pre {A B} _ _.
Arguments post {A B} _ _ _.

Definition wp_spec {A B} (s : spec A B) : PT A B :=
  fun P x => pre s x /\ (forall y : B x, post s x y -> P x y).

Module SpecNotations.
  Notation "[[ p , q ]]" := (Spec p q) (at level 0, p at level 99, q at level 99).
End SpecNotations.

Import WpNotations.
Import SpecNotations.

(** Strengthening the precondition or weakening the postcondition yields a
    specification that is harder to satisfy, hence refines the original. *)
Lemma wp_spec_strengthen {A B} (p1 p2 : A -> Prop) (q : forall x : A, B x -> Prop) :
  p1 ⊆ p2 -> wp_spec [[p1, q]] ⊑ wp_spec [[p2, q]].
Proof.
  intros H_impl P x [H_pre H_post]. split.
  - exact (H_impl x H_pre).
  - exact H_post.
Qed.

Lemma wp_spec_weaken {A B} (p : A -> Prop) (q1 q2 : forall x : A, B x -> Prop) :
  (forall x y, q2 x y -> q1 x y) -> wp_spec [[p, q1]] ⊑ wp_spec [[p, q2]].
Proof.
  intros H_impl P x [H_pre H_post]. split.
  - exact H_pre.
  - intros y H_q2.
    exact (H_post y (H_impl x y H_q2)).
Qed.
