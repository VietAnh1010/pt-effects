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
    postcondition at all. This is the "total correctness" reading. *)
Definition must_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step CAbort _ => False
  end.

(** [may_pt] is the dual, "partial correctness" reading: an aborting program
    satisfies every postcondition. Section 6 needs it to state the soundness of
    [wp_rec] against the fuel-driven semantics - a run that exhausts its fuel
    has not computed a wrong answer, it has computed no answer, and must not
    count as a failure.

<<
      mayPT : (a -> Set) -> (Partial a -> Set)
      mayPT P (Pure x)       = P x
      mayPT P (Step Abort _) = ⊤
>>

    The paper's [mayPT] takes a bare predicate on results. This takes the same
    indexed relation between input and output as [must_pt], so that the two are
    interchangeable and the lemmas below mirror each other exactly; take [B]
    constant to recover the paper's form. *)
Definition may_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step CAbort _ => True
  end.

(** ** [must_pt] *)

Lemma must_pt_inv {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  must_pt P x m -> exists y, m = Pure y /\ P x y.
Proof.
  intros H_pt.
  destruct m as [y | c k]; simpl in *.
  - exists y. split.
    + reflexivity.
    + exact H_pt.
  - destruct c as []. contradiction.
Qed.

Lemma must_pt_pure {A B} (P : forall x : A, B x -> Prop) (x : A) (y : B x) :
  P x y -> must_pt P x (Pure y).
Proof. intros HP. exact HP. Qed.

Lemma must_pt_mono {A B} (P Q : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  P x ⊆ Q x -> must_pt P x m -> must_pt Q x m.
Proof.
  intros H_impl H_pt.
  apply must_pt_inv in H_pt as [y [-> HP]].
  exact (H_impl y HP).
Qed.

(** [abort] refines nothing: it satisfies no postcondition. *)
Lemma must_pt_abort {A B} (P : forall x : A, B x -> Prop) (x : A) : ~ must_pt P x abort.
Proof. intros H_pt. contradiction. Qed.

(** ** [may_pt]

    The mirror image of the [must_pt] rules above. *)

Lemma may_pt_inv {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  may_pt P x m ->
  (exists y, m = Pure y /\ P x y) \/
  (exists k, m = Step CAbort k).
Proof.
  intros H_pt.
  destruct m as [y | c k]; simpl in *.
  - left. exists y. split.
    + reflexivity.
    + exact H_pt.
  - right. destruct c as [].
    exists k. reflexivity.
Qed.

Lemma may_pt_pure {A B} (P : forall x : A, B x -> Prop) (x : A) (y : B x) :
  P x y -> may_pt P x (Pure y).
Proof. intros HP. exact HP. Qed.

Lemma may_pt_mono {A B} (P Q : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  P x ⊆ Q x -> may_pt P x m -> may_pt Q x m.
Proof.
  intros H_impl H_pt.
  apply may_pt_inv in H_pt as [[y [-> HP]] | [k ->]].
  - exact (H_impl y HP).
  - exact I.
Qed.

Lemma may_pt_abort {A B} (P : forall x : A, B x -> Prop) (x : A) : may_pt P x abort.
Proof. exact I. Qed.

(** [must_pt] is the stronger of the two. *)
Lemma must_pt_may_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  must_pt P x m -> may_pt P x m.
Proof.
  intros H_pt.
  apply must_pt_inv in H_pt as [y [-> HP]].
  exact HP.
Qed.

Definition wp_partial {A B} (f : forall x : A, partial (B x)) : PT A B :=
  fun P => wp f (must_pt P).

(** The domain of a partial function: those inputs on which it does not abort. *)
Definition dom {A B} (f : forall x : A, partial (B x)) : A -> Prop :=
  wp_partial f (fun _ _ => True).

(** Every partial program is defined on the inputs where it is correct. *)
Lemma wp_partial_dom {A B} (f : forall x : A, partial (B x)) (P : forall x : A, B x -> Prop) :
  wp_partial f P ⊆ dom f.
Proof.
  intros x.
  exact (must_pt_mono P (fun _ _ => True) x (f x) (fun _ _ => I)).
Qed.
