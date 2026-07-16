(** * Predicate transformers and refinement

    Sections 2 and 3 of Swierstra and Baanen, ICFP 2019.

    For a pure function [f : forall x : A, B x], the weakest precondition
    semantics is

<<
      wp : (f : (x : a) -> b x) -> (P : (x : a) -> b x -> Set) -> (a -> Set)
      wp f P = \x -> P x (f x)
>>

    Note the postcondition [P] is a *relation* between input and output, not
    just a predicate on outputs: this is what lets [wp] state that a function
    is correct with respect to its argument. *)

Definition wp {A : Type} {B : A -> Type} (f : forall x : A, B x) (P : forall x : A, B x -> Prop) (x : A) : Prop :=
  P x (f x).

(** A predicate transformer maps a postcondition to a precondition. *)
Definition PT (A : Type) (B : A -> Type) : Type :=
  (forall x : A, B x -> Prop) -> A -> Prop.

(** ** Refinement

    [pt1] is refined by [pt2] when [pt2] satisfies every specification [pt1]
    does. Contrary to the usual intuition, the *weaker* transformer is on the
    left: [pt2] may demand less and guarantee more. *)
Definition refines {A : Type} {B : A -> Type} (pt1 pt2 : PT A B) : Prop :=
  forall (P : forall x : A, B x -> Prop) (x : A), pt1 P x -> pt2 P x.

(** Pointwise implication of predicates. *)
Definition subset {A : Type} (P Q : A -> Prop) : Prop :=
  forall x : A, P x -> Q x.

Module WpNotations.
  Notation "pt1 ⊑ pt2" := (refines pt1 pt2) (at level 70, no associativity).
  Notation "P ⊆ Q" := (subset P Q) (at level 70, no associativity).
End WpNotations.

Import WpNotations.

Lemma refines_refl {A B} (pt : PT A B) : pt ⊑ pt.
Proof. intros P x H_pt. exact H_pt. Qed.

Lemma refines_trans {A B} (pt1 pt2 pt3 : PT A B) : pt1 ⊑ pt2 -> pt2 ⊑ pt3 -> pt1 ⊑ pt3.
Proof. intros H12 H23 P x H_pt. exact (H23 P x (H12 P x H_pt)). Qed.

Lemma subset_refl {A} (P : A -> Prop) : P ⊆ P.
Proof. intros x HP. exact HP. Qed.

Lemma subset_trans {A} (P Q S : A -> Prop) : P ⊆ Q -> Q ⊆ S -> P ⊆ S.
Proof. intros HPQ HQS x HP. exact (HQS x (HPQ x HP)). Qed.
