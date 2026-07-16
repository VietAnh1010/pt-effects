(** * Nondeterminism

    Section 5 of Swierstra and Baanen, ICFP 2019.

<<
      data C : Set where
        Fail   : C
        Choice : C
      R : C -> Set
      R Fail   = ⊥
      R Choice = Bool
      ND = Free C R
>> *)

From Stdlib Require Import List.
From pt_effects.core Require Import free wp spec.
Import ListNotations.

Inductive C : Type :=
| Fail : C
| Choice : C.

Definition R (c : C) : Type :=
  match c with
  | Fail => Empty_set
  | Choice => bool
  end.

Definition nondet : Type -> Type := free C R.

Definition fail {A} : nondet A :=
  Step Fail (fun r : R Fail => match r with end).

Definition choice {A} (m1 m2 : nondet A) : nondet A :=
  Step Choice (fun r : R Choice => if r then m1 else m2).

(** The intended semantics: collect all results. *)
Fixpoint run {A} (m : nondet A) : list A :=
  match m with
  | Pure x => [x]
  | Step c k =>
      match c return (R c -> nondet A) -> list A with
      | Fail => fun _ => []
      | Choice => fun k => run (k true) ++ run (k false)
      end k
  end.

(** ** Demonic and angelic semantics

    Two transformers: [all] requires every branch to satisfy [P] (so [fail]
    trivially succeeds), [any] requires some branch to (so [fail] never does).

<<
      All P (Pure x)        = P x
      All P (Step Fail _)   = ⊤
      All P (Step Choice k) = All P (k True) ∧ All P (k False)

      Any P (Pure x)        = P x
      Any P (Step Fail _)   = ⊥
      Any P (Step Choice k) = Any P (k True) ∨ Any P (k False)
>> *)

Fixpoint all {A} (P : A -> Prop) (m : nondet A) : Prop :=
  match m with
  | Pure x => P x
  | Step c k =>
      match c return (R c -> nondet A) -> Prop with
      | Fail => fun _ => True
      | Choice => fun k => all P (k true) /\ all P (k false)
      end k
  end.

Fixpoint any {A} (P : A -> Prop) (m : nondet A) : Prop :=
  match m with
  | Pure x => P x
  | Step c k =>
      match c return (R c -> nondet A) -> Prop with
      | Fail => fun _ => False
      | Choice => fun k => any P (k true) \/ any P (k false)
      end k
  end.

Definition wp_all {A B} (f : forall x : A, nondet (B x)) : PT A B :=
  fun P x => all (P x) (f x).

Definition wp_any {A B} (f : forall x : A, nondet (B x)) : PT A B :=
  fun P x => any (P x) (f x).

(** ** Exercises

    The paper's completeness/soundness results for this section: the [all] and
    [any] transformers agree with the list semantics. Prove by induction on
    [m]; [in_app_iff] and [Forall_app] / [Exists_app] from the standard
    library are the useful lemmas. *)

Theorem all_run {A} (P : A -> Prop) (m : nondet A) : all P m <-> Forall P (run m).
Proof.
  induction m as [x | c k IH]; simpl.
  - rewrite -> Forall_cons_iff.
    rewrite -> Forall_nil_iff.
    tauto.
  - symmetry. destruct c as [|].
    + exact (Forall_nil_iff P).
    + rewrite -> (IH true).
      rewrite -> (IH false).
      exact (Forall_app P (run (k true)) (run (k false))).
Qed.

Theorem any_run {A} (P : A -> Prop) (m : nondet A) : any P m <-> Exists P (run m).
Proof.
  induction m as [x | c k IH]; simpl.
  - rewrite -> Exists_cons.
    rewrite -> Exists_nil.
    tauto.
  - symmetry. destruct c as [|].
    + exact (Exists_nil P).
    + rewrite -> (IH true).
      rewrite -> (IH false).
      exact (Exists_app P (run (k true)) (run (k false))).
Qed.

(** [all] is the demonic reading, so it is monotone in [P]. *)
Lemma all_mono {A} (P Q : A -> Prop) (m : nondet A) :
  (forall x, P x -> Q x) -> all P m -> all Q m.
Proof.
  intros H_impl HP.
  rewrite -> all_run in HP.
  rewrite -> all_run.
  exact (Forall_impl Q H_impl HP).
Qed.

Lemma any_mono {A} (P Q : A -> Prop) (m : nondet A) :
  (forall x, P x -> Q x) -> any P m -> any Q m.
Proof.
  intros H_impl HP.
  rewrite -> any_run in HP.
  rewrite -> any_run.
  exact (Exists_impl Q H_impl HP).
Qed.
