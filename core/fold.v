(** * Compositionality

    Section 4.2 of Swierstra and Baanen, ICFP 2019.

    Any predicate transformer defined as a fold over the free monad distributes
    over [bind]:

<<
      compositionality : (c : Free C R a) (f : a -> Free C R b) ->
        forall P -> pt (c >>= f) P == pt c (wp f P)
>>

    the analogue of [wp (c1; c2, R) = wp (c1, wp (c2, R))] from imperative
    program logics. Here it is [compositionality]; restricted to Kleisli arrows
    it gives [compositionality_left] and [compositionality_right]. Section 4 proves
    the state case separately, as [state.state_pt_bind]. *)

From Stdlib Require Import FunctionalExtensionality.
From pt_effects.core Require Import free wp.

Import FreeNotations.
Import WpNotations.
Local Open Scope free_scope.

(** ** The fold over the free monad

    The carrier is an arbitrary [X], not [Prop]. At [X := Prop] this is the
    paper's [pt], with [must_pt], [may_pt], [all] and [any] as instances; at
    [X := S -> Prop] it is [state.state_pt], which a [Prop] carrier cannot
    express. Generality stops at [fold_bind]: [⊑] is [Prop]-valued, so
    everything below lives at [X := Prop]. *)
Definition alg (C : Type) (R : C -> Type) (X : Type) : Type :=
  forall c : C, (R c -> X) -> X.

Fixpoint fold {C R X A} (p : A -> X) (s : alg C R X) (m : free C R A) : X :=
  match m with
  | Pure x => p x
  | Step c k => s c (fun r => fold p s (k r))
  end.

(** The compositionality law as a definitional equality, the literal rendering
    of the paper's [≡]. Needs extensionality, since the abstract algebra is
    applied to continuations that agree only pointwise. The refinement rules no
    longer depend on it: they use [compositionality], an [<->] form that trades
    this axiom for [alg_monotone]. It is kept as the closest reading of the
    paper. [state.state_pt_bind] is the same law for state, axiom-free because
    its algebra is concrete. *)
Lemma fold_bind {C R X A B} (p : B -> X) (s : alg C R X) (m : free C R A) (k : A -> free C R B) :
  fold p s (bind m k) = fold (fun x => fold p s (k x)) s m.
Proof.
  induction m as [x | c k' IH]; simpl.
  - reflexivity.
  - rewrite -> (functional_extensionality _ _ IH).
    reflexivity.
Qed.

(** Monotonicity, which the paper states of [pt] (proved below as [fold_mono]):

<<
      monotonicity : P ⊆ Q -> (c : Free C R a) -> pt c P -> pt c Q
>>

    [alg_monotone] captures it as a property of the algebra alone; every algebra
    in the paper has it. *)
Definition alg_monotone {C R} (F : alg C R Prop) : Prop :=
  forall (c : C) (P Q : R c -> Prop), P ⊆ Q -> F c P -> F c Q.

(** [compositionality] as an [<->]: the funext-free counterpart of [fold_bind],
    with [alg_monotone] replacing the pointwise-equality rewrite. This is
    the form the refinement rules use, so both [compositionality_left] and
    [compositionality_right] carry the [alg_monotone] hypothesis - where the
    paper needs monotonicity only for the latter. *)
Lemma compositionality {C R A B} (F : alg C R Prop) (P : B -> Prop) (m : free C R A) (k : A -> free C R B) :
  alg_monotone F -> fold P F (bind m k) <-> fold (fun x => fold P F (k x)) F m.
Proof.
  intros H_monotone.
  induction m as [x | c k' IH]; simpl.
  - tauto.
  - split.
    + exact (H_monotone c _ _ (fun r => proj1 (IH r))).
    + exact (H_monotone c _ _ (fun r => proj2 (IH r))).
Qed.

(** ** Predicate transformer semantics

    Weakest preconditions for Kleisli arrows: [wp] composed with [fold]
    pointwise. *)
Definition wp_free {C R A B} (F : alg C R Prop) (f : forall x : A, free C R (B x)) : PT A B :=
  fun P => wp f (fun x => fold (P x) F).

(** ** Kleisli composition

    Section 4.2's central results: [⊑] is a congruence for [>=>], so predicate
    transformers may be substituted freely during refinement proofs, just as
    referential transparency allows substituting pure expressions during
    equational reasoning. Together they make these transformers an ordered monad
    [Katsumata and Sato 2013]. *)

(** Refinement on the *first* argument of a Kleisli composition. Carries
    [alg_monotone] only to invoke [compositionality]; the paper's
    compositionality-left needs no monotonicity at all. *)
Theorem compositionality_left {C' R A B C} (F : alg C' R Prop) (f1 f2 : A -> free C' R B) (g : B -> free C' R C) :
  alg_monotone F ->
  wp_free F f1 ⊑ wp_free F f2 ->
  wp_free F (f1 >=> g) ⊑ wp_free F (f2 >=> g).
Proof.
  unfold wp_free, wp, kleisli.
  intros H_monotone H_refines P x HP.
  apply (proj2 (compositionality _ _ _ _ H_monotone)).
  apply (H_refines (fun x y => fold (P x) F (g y)) x).
  exact (proj1 (compositionality _ _ _ _ H_monotone) HP).
Qed.

(** The paper's [monotonicity]. *)
Lemma fold_mono {C R A} (F : alg C R Prop) (P Q : A -> Prop) (m : free C R A) :
  alg_monotone F -> P ⊆ Q -> fold P F m -> fold Q F m.
Proof.
  intros H_monotone H_impl.
  induction m as [x | c k IH]; simpl.
  - exact (H_impl x).
  - exact (H_monotone c (fun r => fold P F (k r)) (fun r => fold Q F (k r)) IH).
Qed.

(** Refinement on the *second* argument. Uses [alg_monotone] twice: once for
    [compositionality] (as [compositionality_left] does), and again through
    [fold_mono], to reach inside the postcondition where the two sides differ
    and [⊑] alone cannot. *)
Theorem compositionality_right {C' R A B C} (F : alg C' R Prop) (f : A -> free C' R B) (g1 g2 : B -> free C' R C) :
  alg_monotone F ->
  wp_free F g1 ⊑ wp_free F g2 ->
  wp_free F (f >=> g1) ⊑ wp_free F (f >=> g2).
Proof.
  unfold wp_free, wp, kleisli.
  intros H_monotone H_refines P x HP.
  apply (proj2 (compositionality _ _ _ _ H_monotone)).
  apply (fold_mono F _ _ (f x) H_monotone (H_refines (fun _ => P x))).
  exact (proj1 (compositionality _ _ _ _ H_monotone) HP).
Qed.
