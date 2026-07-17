# pt-effects

A Rocq port of Wouter Swierstra and Tim Baanen, [*A Predicate Transformer
Semantics for Effects*](https://webspace.science.uu.nl/~swier004/publications/2019-icfp.pdf)
(ICFP 2019). The paper is in Agda; this is a study port.

## Building

```sh
make build      # rocq makefile -f _RocqProject, then build
make clean
make cleanall   # also removes the generated Makefile.rocq
```

Requires Rocq 9.0 (tested against 9.0.0).

## Layout

| Path | Namespace | Paper |
| --- | --- | --- |
| `core/free.v` | `pt_effects.core.free` | §2 - the free monad `Free C R a`, `bind`, monad laws |
| `core/wp.v` | `pt_effects.core.wp` | §2-3 - `wp`, predicate transformers `PT`, refinement `⊑`, `⊆` |
| `core/fold.v` | `pt_effects.core.fold` | §4.2 - `alg`, `fold`, `wp_free`, `fold_bind`, `compositionality`, `compositionality_left`/`_right` |
| `core/spec.v` | `pt_effects.core.spec` | §7 - `Spec` records, `wp_spec` |
| `effects/partial.v` | `pt_effects.effects.partial` | §3, §6 - `Abort`, `must_pt`, `may_pt`, `wp_partial`, `dom` |
| `effects/state.v` | `pt_effects.effects.state` | §4 - `Get`/`Put`, `run`, `state_pt`, `wp_state` |
| `effects/nondet.v` | `pt_effects.effects.nondet` | §5 - `Fail`/`Choice`, `all`, `any` |
| `effects/rec.v` | `pt_effects.effects.rec` | §6 - `Rec`, `call`, `petrol`, `invariant`, `wp_rec`, `soundness` |
| `effects/refine.v` | `pt_effects.effects.refine` | §7 - refinement calculus |
| `examples/div.v` | `examples.div` | §3 - the expression/division example |
| `examples/relabel.v` | `examples.relabel` | §4.1 - tree relabelling |

## Porting notes

Where the Rocq version differs from the Agda:

- **`Set` vs `Prop`.** In the paper, predicates have type `Set`; here they have
  type `Prop`, and response types have type `Type`. So `R Abort = ⊥` becomes
  `R Abort = Empty_set` (a `Type`), while `must_pt`'s abort case is `False` (a
  `Prop`).
- **Functional extensionality.** The `Step` cases of the monad laws require
  `extensionality`: two continuations that agree pointwise are not
  definitionally equal in Rocq. Agda does not need this. The axiom is used only
  in `core/free.v` (`bind_pure_r`, `bind_assoc`) and `core/fold.v` (`fold_bind`).
  The refinement rules `compositionality_left`/`_right` do not use it: they are
  proved from `compositionality`, an `<->` form of `fold_bind` that instead
  assumes the algebra monotone (`alg_monotone`). No other declaration depends on
  the axiom.
- **§4.2 `compositionality`'s relational form is not ported.** The `wp` in the
  paper's `pt c (wp f P)` is not the `wp` of §2: there `P` is a relation, here it
  is a predicate on results, as required by `pt (c >>= f) P`. Supplying a
  predicate where the relational `wp_free` expects a relation requires
  `fun _ => P`, and the result is convertible with the bind law. So the
  relational form is not stated; the bind law is stated on predicates instead, as
  `compositionality` (an `<->`, assuming the algebra monotone) and `fold_bind`
  (an `=`, using extensionality), and `compositionality_left`/`_right` are
  derived from `compositionality` directly.
- **The fold's carrier is arbitrary.** The paper's general `pt` has codomain
  `Set`, but `statePT` has codomain `s -> Set`, which places the state parameter
  outside the general result type; this is why §4.2 proves the law twice.
  `fold.fold` has an arbitrary codomain `X`, so `state_pt` is its
  `X := S -> Prop` instance and `fold_bind` holds for both. Refinement requires
  `Prop`, so `wp_free` and every declaration below it fix `X := Prop`.
- **`may_pt` is indexed.** In the paper, `mayPT` takes a predicate on results,
  while `mustPT` takes a relation between input and output. Here both take the
  indexed relation, so the two families are interchangeable and their lemmas have
  the same shape.
- **§6 `soundness`.** Ported verbatim as `rec.soundness`, but the paper's
  hypothesis `∀ i → wpRec spec f P i` implicitly requires `∀ i → pre spec i`,
  since `wpSpec` has `pre` as a conjunct. This holds for the paper's `f91Spec`,
  whose precondition is constantly `⊤`, but for a spec with a nontrivial
  precondition the hypothesis is unsatisfiable and the theorem is vacuous.
  `rec.soundness_pre` is the same result under
  `∀ i → pre spec i → wpRec spec f P i`, with the conclusion guarded to match;
  prefer it.
