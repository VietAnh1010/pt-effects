(** * Partiality

    Section 3 of Swierstra and Baanen, ICFP 2019.

    A single command [Abort] whose response type is empty: there is no way to
    continue after aborting.

<<
      data C : Set where Abort : C
      R : C -> Set
      R Abort = ⊥
      Partial = Free C R
>> *)

From pt_effects.core Require Import free wp.
Import WpNotations.

Inductive C : Type := CAbort.
Definition R (_ : C) : Type := Empty_set.
Definition partial : Type -> Type := free C R.

(** The continuation is the empty eliminator: aborting has no successor. *)
Definition abort {A} : partial A := Step CAbort (fun r : R CAbort => match r with end).

(** ** Semantics

    [must_pt] insists a computation succeeds: an aborting program satisfies no
    postcondition at all. This is the "total correctness" reading; the paper
    also discusses [mayPT], which accepts abortion. *)
Definition must_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step CAbort _ => False
  end.

Definition wp_partial {A B} (f : forall x : A, partial (B x)) : PT A B :=
  fun P => wp f (must_pt P).

(** The domain of a partial function: those inputs on which it does not abort. *)
Definition dom {A B} (f : forall x : A, partial (B x)) : A -> Prop :=
  wp_partial f (fun _ _ => True).

(** ** Reasoning principles *)

Lemma must_pt_inv {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  must_pt P x m -> exists y, m = Pure y /\ P x y.
Proof.
  intros H_pt.
  destruct m as [y | c k]; simpl in *.
  - exists y. split.
    + reflexivity.
    + exact H_pt.
  - destruct c as [].
    contradiction.
Qed.

Lemma must_pt_pure {A B} (P : forall x : A, B x -> Prop) (x : A) (y : B x) :
  P x y -> must_pt P x (Pure y).
Proof. intros HP. exact HP. Qed.

Lemma must_pt_mono {A B} (P Q : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  (forall y : B x, P x y -> Q x y) -> must_pt P x m -> must_pt Q x m.
Proof.
  intros H_impl H_pt.
  apply must_pt_inv in H_pt as [y [-> HP]].
  exact (must_pt_pure Q x y (H_impl y HP)).
Qed.

(** [abort] refines nothing: it satisfies no postcondition. *)
Lemma must_pt_abort {A B} (P : forall x : A, B x -> Prop) (x : A) : ~ must_pt P x abort.
Proof. intros H_absurd. contradiction. Qed.

(** Every partial program is defined on the inputs where it is correct. *)
Lemma wp_partial_dom {A B} (f : forall x : A, partial (B x)) (P : forall x : A, B x -> Prop) :
  wp_partial f P ⊆ dom f.
Proof.
  intros x.
  exact (must_pt_mono P (fun _ _ => True) x (f x) (fun _ _ => I)).
Qed.
