(** * Mutable state

    Section 4 of Swierstra and Baanen, ICFP 2019.

<<
      data C : Set where
        Get : C
        Put : S -> C
      R : C -> Set
      R Get     = S
      R (Put _) = ⊤
      State = Free C R
>>

    NOTE: this file and the other effect files each define their own [C] and
    [R], following the paper. When mixing effects in one file, [Require] them
    qualified ([From pt_effects.effects Require state.] then [state.get])
    rather than [Require Import]-ing several at once. *)

From pt_effects.core Require Import free wp spec.

Inductive C (S : Type) : Type :=
| Get : C S
| Put : S -> C S.

Arguments Get {S}.
Arguments Put {S} _.

Definition R {S : Type} (c : C S) : Type :=
  match c with
  | Get => S
  | Put _ => unit
  end.

Definition state (S : Type) : Type -> Type := free (C S) R.

Definition get {S : Type} : state S S :=
  Step Get Pure.

Definition put {S : Type} (s : S) : state S unit :=
  Step (Put s) (fun _ => Pure tt).

(** The intended, effectful semantics: thread the state through. *)
Fixpoint run {S A} (m : state S A) (s : S) : A * S :=
  match m with
  | Pure x => (x, s)
  | Step c k =>
      match c return (R c -> state S A) -> A * S with
      | Get => fun k => run (k s) s
      | Put s' => fun k => run (k tt) s'
      end k
  end.

(** ** Predicate transformer semantics

<<
      statePT : (P : a × S -> Set) -> State a -> (S -> Set)
      statePT P (Pure x)         = \s -> P (x, s)
      statePT P (Step Get k)     = \s -> statePT P (k s) s
      statePT P (Step (Put s) k) = \_ -> statePT P (k tt) s
>> *)
Fixpoint state_pt {S A} (P : A * S -> Prop) (m : state S A) (s : S) : Prop :=
  match m with
  | Pure x => P (x, s)
  | Step c k =>
      match c return (R c -> state S A) -> Prop with
      | Get => fun k => state_pt P (k s) s
      | Put s' => fun k => state_pt P (k tt) s'
      end k
  end.

Definition wp_state {S A B} (f : A -> state S B) (P : A * S -> B * S -> Prop) : A * S -> Prop :=
  fun '(x, s) => state_pt (P (x, s)) (f x) s.

(** ** Exercises

    [soundness] is the paper's key lemma for this section: the predicate
    transformer semantics agrees with the [run] semantics. Prove by induction
    on [f x], generalising the state. *)

Lemma soundness_aux {S A} (P : A * S -> Prop) (m : state S A) :
  forall s, state_pt P m s -> P (run m s).
Proof.
  induction m as [x | c k IH]; simpl; intros s.
  - intros HP. exact HP.
  - destruct c as [| s'].
    + exact (IH s s).
    + exact (IH tt s').
Qed.

Theorem soundness {S A B} (P : A * S -> B * S -> Prop) (f : A -> state S B) (s : S) (x : A) :
  wp_state f P (x, s) -> P (x, s) (run (f x) s).
Proof.
  unfold wp_state.
  exact (soundness_aux (P (x, s)) (f x) s).
Qed.

(** State-specific Hoare-triple style rules. *)
Lemma state_pt_get {S A} (P : A * S -> Prop) (k : S -> state S A) (s : S) :
  state_pt P (bind get k) s <-> state_pt P (k s) s.
Proof. tauto. Qed.

Lemma state_pt_put {S A} (P : A * S -> Prop) (k : unit -> state S A) (s s' : S) :
  state_pt P (bind (put s') k) s <-> state_pt P (k tt) s'.
Proof. tauto. Qed.

(** [state_pt] distributes over [bind]. *)
Lemma state_pt_bind {S A B} (P : B * S -> Prop) (m : state S A) (k : A -> state S B) :
  forall s, state_pt P (bind m k) s <-> state_pt (fun '(x, s') => state_pt P (k x) s') m s.
Proof.
  induction m as [x | c k' IH]; simpl; intros s.
  - tauto.
  - destruct c as [| s'].
    + exact (IH s s).
    + exact (IH tt s').
Qed.
