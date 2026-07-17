(** * The Add example

    Section 3.3 of Swierstra and Baanen, ICFP 2019. An [ADD] instruction for a
    stack machine: replace the top two elements with their sum, aborting when the
    stack has fewer than two. [add] refines its specification [add_spec] - the
    Section 3 template of relating a program to a pre/postcondition pair through
    [wp_partial]. *)

From Stdlib Require Import Arith List.
From pt_effects.core Require Import free wp spec.
From pt_effects.effects Require Import partial.

Import ListNotations.
Import FreeNotations.
Import WpNotations.
Local Open Scope free_scope.

(** The postcondition, a relation between the input and output stacks. *)
Inductive Add : list nat -> list nat -> Prop :=
| add_step (x1 x2 : nat) (xs : list nat) : Add (x1 :: x2 :: xs) (x1 + x2 :: xs).

Definition add_spec : spec (list nat) (fun _ => list nat) :=
  Spec (fun xs => length xs > 1) Add.

(** Pop the top of the stack, aborting when it is empty. *)
Definition pop {A} (xs : list A) : partial (A * list A) :=
  match xs with
  | [] => abort
  | x :: xs' => Pure (x, xs')
  end.

Definition add (xs : list nat) : partial (list nat) :=
  let* '(x1, xs) := pop xs in
  let* '(x2, xs) := pop xs in
  Pure (x1 + x2 :: xs).

(** [add] refines [add_spec]: on a stack of at least two elements it replaces the
    top two by their sum. *)
Theorem correctness : wp_spec add_spec ⊑ wp_partial add.
Proof.
  intros P xs [H_pre H_post].
  unfold add_spec, pre, post, wp_partial, wp in *.
  destruct xs as [| x1 [| x2 xs]]; simpl in *.
  - contradict (Nat.nlt_0_r 1 H_pre).
  - contradict (Nat.lt_irrefl 1 H_pre).
  - exact (H_post (x1 + x2 :: xs) (add_step x1 x2 xs)).
Qed.
