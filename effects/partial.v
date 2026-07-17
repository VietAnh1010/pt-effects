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

    [must_pt] holds only if the computation succeeds: an aborting program
    satisfies no postcondition. This is the "total correctness" reading. *)
Definition must_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step _ _ => False
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
    indexed relation between input and output as [must_pt], so the two are
    interchangeable and the lemmas below have the same shape; take [B]
    constant to recover the paper's form. *)
Definition may_pt {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step _ _ => True
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
  - contradiction.
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

(** [abort] satisfies no postcondition. *)
Lemma must_pt_abort {A B} (P : forall x : A, B x -> Prop) (x : A) : ~ must_pt P x abort.
Proof. intros H_pt. contradiction. Qed.

(** ** [may_pt]

    The duals of the [must_pt] rules above. *)

Lemma may_pt_inv {A B} (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) :
  may_pt P x m ->
  (exists y, m = Pure y /\ P x y) \/
  (exists k, m = Step CAbort k).
Proof.
  intros H_pt.
  destruct m as [y | [] k]; simpl in *.
  - left. exists y. split.
    + reflexivity.
    + exact H_pt.
  - right. exists k. reflexivity.
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

(** ** Refinement (Section 3.2)

    [wp_partial] induces a refinement relation on Kleisli arrows into [partial],
    characterised in the paper by

<<
      refinement : (f g : a -> Partial b) ->
        (wpPartial f ⊑ wpPartial g) <-> forall x -> (f x = g x) \/ (f x = abort)
>>

    The literal second clause [f x = abort] is not provable without functional
    extensionality: an aborting [f x] is [Step CAbort k] for some
    [k : Empty_set -> _], and [Step CAbort k = abort] reduces to
    [k = fun r => match r with end], an equality of functions out of [Empty_set].
    Stating the clause as [exists k, f x = Step CAbort k] avoids comparing
    continuations, so the proof stays axiom-free. *)
Lemma refinement {A B} (f g : forall x : A, partial (B x)) :
  wp_partial f ⊑ wp_partial g <-> (forall x, f x = g x \/ (exists k, f x = Step CAbort k)).
Proof.
  unfold wp_partial, wp, must_pt, refines. split.
  - intros H_refines x.
    specialize (H_refines (fun x' y => f x' = Pure y) x). simpl in *.
    destruct (f x) as [y | [] k].
    + left. specialize (H_refines eq_refl).
      destruct (g x) as [y' | c k].
      * exact H_refines.
      * contradiction.
    + right. exists k. reflexivity.
  - intros Hf P x H_pt.
    destruct (Hf x) as [<- | [k Hk]].
    + exact H_pt.
    + rewrite -> Hk in H_pt.
      contradiction.
Qed.

(** ** Alternative semantics: a default handler (Section 3.4)

    [wp_partial] holds only if a computation succeeds. An aborting computation
    can instead be handled by supplying a default result: [default_handler] runs
    it that way, and [default_pt] / [wp_default] are the matching predicate
    transformer, which requires the postcondition of the default value on abort.
    [d] is a default per input [x], so that [P x (d x)] is well typed for a
    dependent [B]; take [d] constant to recover the paper's single value. *)
Definition default_handler {A} (d : A) (m : partial A) : A :=
  match m with
  | Pure x => x
  | Step _ _ => d
  end.

Definition default_pt {A B} (d : forall x : A, B x) (P : forall x : A, B x -> Prop) (x : A) (m : partial (B x)) : Prop :=
  match m with
  | Pure y => P x y
  | Step _ _ => P x (d x)
  end.

Definition wp_default {A B} (d : forall x : A, B x) (f : forall x : A, partial (B x)) : PT A B :=
  fun P => wp f (default_pt d P).

(** [wp_default] is sound for [default_handler]: when the computed precondition
    holds, running the handler satisfies the postcondition. *)
Lemma soundness {A B} (d : forall x : A, B x) (P : forall x : A, B x -> Prop) (f : forall x : A, partial (B x)) (x : A) :
  wp_default d f P x -> P x (default_handler (d x) (f x)).
Proof.
  unfold wp_default, wp, default_pt, default_handler.
  destruct (f x) as [y | c k].
  - intros HP. exact HP.
  - intros HP. exact HP.
Qed.
