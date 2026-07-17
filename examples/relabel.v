(** * Relabelling a tree

    Section 4.1 of Swierstra and Baanen, ICFP 2019: the running example for the
    state effect. [relabel] replaces every leaf of a tree with a fresh label,
    left to right, threading a counter through the state.

    The specification the paper proves:
      - the shape of the tree is preserved;
      - the labels of the result are exactly [seq s (size t)], the consecutive
        run of naturals starting at the initial state;
      - the final state is [s + size t].

    Use [state.state_pt_bind] from [pt_effects.effects.state] to decompose
    [relabel] compositionally. *)

From Stdlib Require Import Arith List.
From pt_effects.core Require Import free wp spec.
From pt_effects.effects Require Import state.

Import ListNotations.
Import FreeNotations.
Import WpNotations.
Local Open Scope free_scope.

Inductive tree (A : Type) : Type :=
| Leaf : A -> tree A
| Node : tree A -> tree A -> tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | Leaf _ => 1
  | Node l r => size l + size r
  end.

Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf x => [x]
  | Node l r => flatten l ++ flatten r
  end.

(** Draw the next label and advance the counter. *)
Definition fresh : state nat nat :=
  let* n := get in
  let* _ := put (S n) in
  Pure n.

Fixpoint relabel {A} (t : tree A) : state nat (tree nat) :=
  match t with
  | Leaf _ => let* n := fresh in Pure (Leaf n)
  | Node l r =>
      let* l' := relabel l in
      let* r' := relabel r in
      Pure (Node l' r')
  end.

(** ** Exercises *)

Theorem relabel_size {A} (t : tree A) :
  forall s, size (fst (run (relabel t) s)) = size t.
Proof.
  induction t as [x | t1 IHt1 t2 IHt2]; simpl; intros s.
  - reflexivity.
  - rewrite -> run_bind.
    specialize (IHt1 s).
    destruct (run (relabel t1) s) as [t1' s']. simpl in *.
    rewrite -> run_bind.
    specialize (IHt2 s').
    destruct (run (relabel t2) s') as [t2' s'']. simpl in *.
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

Theorem relabel_state {A} (t : tree A) :
  forall s, snd (run (relabel t) s) = s + size t.
Proof.
  induction t as [x | t1 IHt1 t2 IHt2]; simpl; intros s.
  - rewrite -> Nat.add_1_r.
    reflexivity.
  - rewrite -> run_bind.
    specialize (IHt1 s).
    destruct (run (relabel t1) s) as [t1' s']. simpl in *.
    rewrite -> run_bind.
    specialize (IHt2 s').
    destruct (run (relabel t2) s') as [t2' s'']. simpl in *.
    rewrite -> IHt2.
    rewrite -> IHt1.
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

(** The main result of Section 4.1, stated against [run]. *)
Theorem relabel_flatten {A} (t : tree A) :
  forall s, flatten (fst (run (relabel t) s)) = seq s (size t).
Proof.
  induction t as [x | t1 IHt1 t2 IHt2]; simpl; intros s.
  - reflexivity.
  - rewrite -> run_bind.
    specialize (IHt1 s).
    assert (H_eq := relabel_state t1 s).
    destruct (run (relabel t1) s) as [t1' s']. simpl in *.
    rewrite -> H_eq.
    rewrite -> run_bind.
    specialize (IHt2 (s + size t1)).
    destruct (run (relabel t2) (s + size t1)) as [t2' s'']. simpl in *.
    rewrite -> IHt2.
    rewrite -> IHt1.
    rewrite -> seq_app.
    reflexivity.
Qed.

Definition relabel_spec (A : Type) : spec (tree A * nat) (fun _ => tree nat * nat)%type :=
  Spec (fun _ => True) (fun '(t, s) '(t', s') => flatten t' = seq s (size t) /\ s' = s + size t).

(** The same result stated in the predicate transformer style the paper
    actually uses - this is the version worth doing, since it exercises
    [wp_state] rather than reasoning about [run] directly. *)

Lemma relabel_correct_aux {A} (P : tree nat * nat -> Prop) (t : tree A) :
  forall s, (forall p, (let '(t', s') := p in flatten t' = seq s (size t) /\ s' = s + size t) -> P p) -> state_pt P (relabel t) s.
Proof.
  revert P.
  induction t as [x | t1 IHt1 t2 IHt2]; simpl; intros P s H_post.
  - apply H_post. simpl. split.
    + reflexivity.
    + rewrite -> Nat.add_1_r.
      reflexivity.
  - rewrite -> state_pt_bind. apply IHt1.
    intros [t1' s'] [Ht1' Hs'].
    rewrite -> state_pt_bind. apply IHt2.
    intros [t2' s''] [Ht2' Hs''].
    apply H_post. simpl. split.
    + rewrite -> Ht1'.
      rewrite -> Ht2'.
      rewrite -> Hs'.
      rewrite -> seq_app.
      reflexivity.
    + rewrite -> Hs''.
      rewrite -> Hs'.
      rewrite -> Nat.add_assoc.
      reflexivity.
Qed.

Theorem relabel_correct {A} :
  wp_spec (relabel_spec A) ⊑ wp_state relabel.
Proof.
  intros P [t s] [_ H_post].
  unfold relabel_spec, post, wp_state, wp in *.
  exact (relabel_correct_aux (P (t, s)) t s H_post).
Qed.
