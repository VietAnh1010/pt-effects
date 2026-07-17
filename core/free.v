(** * Free monads

    Section 2 of Wouter Swierstra and Tim Baanen, "A predicate transformer
    semantics for effects", ICFP 2019.

    An effect is described by a type of commands [C] together with, for each
    command [c], the type [R c] of responses the environment may give. The
    paper writes this as

<<
      data Free (C : Set) (R : C -> Set) (a : Set) : Set where
        Pure : a -> Free C R a
        Step : (c : C) (k : R c -> Free C R a) -> Free C R a
>>

    The Agda development uses [Set] throughout; here the responses live in
    [Type] and predicates land in [Prop] (see [pt_effects.core.wp]). *)

From Stdlib Require Import FunctionalExtensionality.

Inductive free (C : Type) (R : C -> Type) (A : Type) : Type :=
| Pure : A -> free C R A
| Step : forall c : C, (R c -> free C R A) -> free C R A.

Arguments Pure {C R A} _.
Arguments Step {C R A} _ _.

Fixpoint bind {C R A B} (m : free C R A) (f : A -> free C R B) : free C R B :=
  match m with
  | Pure x => f x
  | Step c k => Step c (fun r => bind (k r) f)
  end.

Fixpoint map {C R A B} (f : A -> B) (m : free C R A) : free C R B :=
  match m with
  | Pure x => Pure (f x)
  | Step c k => Step c (fun r => map f (k r))
  end.

Definition kleisli {C' R A B C} (f : A -> free C' R B) (g : B -> free C' R C) (x : A) : free C' R C :=
  bind (f x) g.

Module FreeNotations.
  Declare Scope free_scope.
  Delimit Scope free_scope with free.
  Bind Scope free_scope with free.

  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : free_scope.
  Notation "f <$> m" := (map f m) (at level 65, right associativity) : free_scope.
  Notation "f >=> g" := (kleisli f g) (at level 55, right associativity) : free_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : free_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : free_scope.
End FreeNotations.

(** ** Monad laws

    The [Step] cases need functional extensionality: two continuations that
    agree pointwise are not definitionally equal in Rocq. The Agda development
    gets this for free from its use of extensional equality reasoning. *)

Lemma bind_pure_l {C R A B} (x : A) (f : A -> free C R B) : bind (Pure x) f = f x.
Proof. reflexivity. Qed.

Lemma bind_pure_r {C R A} (m : free C R A) : bind m Pure = m.
Proof.
  induction m as [x | c k IH]; simpl.
  - reflexivity.
  - rewrite -> (functional_extensionality _ _ IH).
    reflexivity.
Qed.

Lemma bind_assoc {C' R A B C} (m : free C' R A) (f : A -> free C' R B) (g : B -> free C' R C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  induction m as [x | c k IH]; simpl.
  - reflexivity.
  - rewrite -> (functional_extensionality _ _ IH).
    reflexivity.
Qed.

(** A [bind] can only produce a [Pure] when both arguments do. *)
Lemma bind_eq_pure {C R A B} (m : free C R A) (f : A -> free C R B) (y : B) :
  bind m f = Pure y -> exists x, m = Pure x /\ f x = Pure y.
Proof.
  intros H_eq.
  destruct m as [x | c k]; simpl in *.
  - exists x. split.
    + reflexivity.
    + exact H_eq.
  - discriminate.
Qed.
