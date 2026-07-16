(** * The expression language with division

    Section 3 of Swierstra and Baanen, ICFP 2019. This is the paper's running
    example for partiality and the worked template for the other sections:
    define a big-step relation, an interpreter in the free monad, and prove the
    interpreter correct with respect to the relation via [wp_partial]. *)

From Stdlib Require Import Arith.
From pt_effects.core Require Import free wp spec.
From pt_effects.effects Require Import partial.

Import FreeNotations.
Import WpNotations.
Local Open Scope free_scope.

Inductive expr : Type :=
| Val : nat -> expr
| Div : expr -> expr -> expr.

Inductive eval : expr -> nat -> Prop :=
| eval_val (n : nat) : eval (Val n) n
| eval_div (l r : expr) (v1 v2 : nat) : eval l v1 -> eval r (S v2) -> eval (Div l r) (v1 / S v2).

Notation "e ⇓ n" := (eval e n) (at level 70, no associativity).

Fixpoint denote (e : expr) : partial nat :=
  match e with
  | Val n => Pure n
  | Div e1 e2 =>
      let* v1 := denote e1 in
      let* v2 := denote e2 in
      match v2 with
      | 0 => abort
      | S _ => Pure (v1 / v2)
      end
  end.

Fixpoint safe_div (e : expr) : Prop :=
  match e with
  | Val _ => True
  | Div e1 e2 => ~ e2 ⇓ 0 /\ safe_div e1 /\ safe_div e2
  end.

(** ** Correctness

    [correct] is the paper's [SafeDiv ⊆ wpPartial ⟦_⟧ _⇓_]: the syntactic
    precondition is enough to guarantee the interpreter both terminates and
    agrees with the big-step relation. *)
Theorem correct : safe_div ⊆ wp_partial denote eval.
Proof.
  intros e. unfold wp_partial, wp.
  induction e as [n | e1 IHe1 e2 IHe2]; simpl.
  - intros _. exact (eval_val n).
  - intros [Hnz [Hs1 Hs2]].
    destruct (must_pt_inv _ _ _ (IHe1 Hs1)) as [v1 [-> He1]].
    destruct (must_pt_inv _ _ _ (IHe2 Hs2)) as [v2 [-> He2]].
    destruct v2 as [| v2']; simpl.
    + contradiction.
    + exact (eval_div e1 e2 v1 v2' He1 He2).
Qed.

(** ** Soundness and completeness

    [sound] and [complete] together say [dom ⟦_⟧] and [wpPartial ⟦_⟧ _⇓_]
    coincide: the interpreter is correct exactly where it is defined. *)

Theorem sound : dom denote ⊆ wp_partial denote eval.
Proof.
  intros e. unfold dom, wp_partial, wp.
  induction e as [n | e1 IHe1 e2 IHe2]; simpl.
  - intros _. exact (eval_val n).
  - intros H_pt.
    apply must_pt_inv in H_pt as [n [H_eq _]].
    apply bind_eq_pure in H_eq as [v1 [Hd1 H_eq]].
    apply bind_eq_pure in H_eq as [v2 [Hd2 H_eq]].
    rewrite -> Hd1 in IHe1 |- *.
    rewrite -> Hd2 in IHe2 |- *.
    destruct v2 as [| v2']; simpl in *.
    + discriminate.
    + exact (eval_div e1 e2 v1 v2' (IHe1 I) (IHe2 I)).
Qed.

Theorem complete : wp_partial denote eval ⊆ dom denote.
Proof. exact (wp_partial_dom denote eval). Qed.

(** ** Relating the two

    [safe_div] is a sufficient but not necessary condition: it implies
    [dom denote], via [correct] and [complete]. *)
Theorem safe_div_dom : safe_div ⊆ dom denote.
Proof. exact (subset_trans safe_div (wp_partial denote eval) (dom denote) correct complete). Qed.

(** The specification [[safe_div, _⇓_]] is refined by the interpreter. This
    is the Section 7 reading of [correct]: a program refines a spec. *)
Theorem denote_refines_spec : wp_spec (Spec safe_div eval) ⊑ wp_partial denote.
Proof.
  intros P e [H_pre H_post].
  unfold pre, post, wp_partial, wp in *.
  exact (must_pt_mono eval P e (denote e) H_post (correct e H_pre)).
Qed.
