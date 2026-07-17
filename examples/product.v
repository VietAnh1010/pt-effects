(** * The fastProduct example

    Section 3.4 of Swierstra and Baanen, ICFP 2019. [product] multiplies a list
    of naturals; [fast_product] short-circuits to an abort as soon as it meets a
    zero. Giving it [wp_partial] semantics would require the input to be
    zero-free, so instead the aborting computation is interpreted by [wp_default]
    and the handler [default_handler] (both in [pt_effects.effects.partial]),
    which supply a default result on abort. [correctness] relates [fast_product]
    back to [product]. *)

From Stdlib Require Import Arith List.
From pt_effects.core Require Import free wp spec.
From pt_effects.effects Require Import partial.

Import ListNotations.
Import FreeNotations.
Import WpNotations.
Local Open Scope free_scope.

Definition product (xs : list nat) : nat := fold_right Nat.mul 1 xs.

Fixpoint fast_product (xs : list nat) : partial nat :=
  match xs with
  | [] => Pure 1
  | 0 :: _ => abort
  | x :: xs' => Nat.mul x <$> fast_product xs'
  end.

(** [fast_product] computes [product], aborting exactly when the product is
    zero. This is the structural fact behind [correctness], stated without a
    postcondition so the induction on the list goes through. *)
Lemma fast_product_correct (xs : list nat) :
  product xs <> 0 /\ fast_product xs = Pure (product xs) \/
  product xs = 0 /\ (exists k, fast_product xs = Step CAbort k).
Proof.
  induction xs as [| [| x'] xs' IHxs']; simpl.
  - left. split.
    + discriminate.
    + reflexivity.
  - right. split.
    + reflexivity.
    + exists (fun r : R CAbort => match r with end). reflexivity.
  - destruct IHxs' as [[H_neq ->] | [-> [k ->]]]; simpl.
    + left. split.
      * intros H_eq. exact (H_neq (proj1 (proj1 (Nat.eq_add_0 _ _) H_eq))).
      * reflexivity.
    + right. split.
      * exact (Nat.mul_0_r x').
      * exists (fun r => Nat.mul (S x') <$> k r). reflexivity.
Qed.

(** [fast_product] refines [product] under the default-handler semantics: on
    abort the handler returns [0], which is the product of a list containing a
    zero. *)
Theorem correctness : wp product ⊑ wp_default (fun _ => 0) fast_product.
Proof.
  intros P xs HP.
  unfold wp_default, wp, default_pt in *.
  destruct (fast_product_correct xs) as [[_ ->] | [H_eq [k ->]]].
  - exact HP.
  - rewrite -> H_eq in HP. exact HP.
Qed.
