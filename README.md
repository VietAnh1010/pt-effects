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
| `core/wp.v` | `pt_effects.core.wp` | §2–3 - `wp`, predicate transformers `PT`, refinement `⊑`, `⊆` |
| `core/fold.v` | `pt_effects.core.fold` | §4.2 - `alg`, `fold`, `wp_free`, `fold_bind`, `compositionality_left`/`_right` |
| `core/spec.v` | `pt_effects.core.spec` | §7 - `Spec` records, `wp_spec` |
| `effects/partial.v` | `pt_effects.effects.partial` | §3, §6 - `Abort`, `must_pt`, `may_pt`, `wp_partial`, `dom` |
| `effects/state.v` | `pt_effects.effects.state` | §4 - `Get`/`Put`, `run`, `state_pt`, `wp_state` |
| `effects/nondet.v` | `pt_effects.effects.nondet` | §5 - `Fail`/`Choice`, `all`, `any` |
| `effects/rec.v` | `pt_effects.effects.rec` | §6 - `Rec`, `call`, `petrol`, `invariant`, `wp_rec`, `soundness` |
| `effects/refine.v` | `pt_effects.effects.refine` | §7 - refinement calculus |
| `examples/div.v` | `examples.div` | §3 - the expression/division example |
| `examples/relabel.v` | `examples.relabel` | §4.1 - tree relabelling |

## Porting notes

Places where the Rocq version departs from the Agda:

- **`Set` vs `Prop`.** The paper's predicates land in Agda's `Set`; here they
  land in `Prop`, and response types live in `Type`. So `R Abort = ⊥` becomes
  `R Abort = Empty_set` (a `Type`), while `must_pt`'s abort case is `False` (a
  `Prop`).
- **Functional extensionality.** The `Step` cases of the monad laws need
  `extensionality` - two continuations agreeing pointwise are not
  definitionally equal in Rocq. Agda's development sidesteps this. Confined to
  `core/free.v` (`bind_pure_r`, `bind_assoc`) and `core/fold.v` (`fold_bind`,
  and so `compositionality_left`/`_right`); nothing else depends on it.
- **§4.2 `compositionality` is not stated.** The `wp` in the paper's
  `pt c (wp f P)` is not §2's: there `P` is relational, here it is a bare
  predicate on results, forced by `pt (c >>= f) P`. Injecting one into the
  relational `wp_free` needs `fun _ => P`, and the result is convertible with
  `fold_bind`. So only `fold_bind` is stated, and
  `compositionality_left`/`_right` rest on it directly.
- **The fold's carrier is arbitrary.** The paper's general `pt` lands in `Set`,
  but `statePT` folds into `s -> Set`, putting state outside the general result -
  which is why §4.2 proves it twice. `fold.fold` folds into any `X`, so
  `state_pt` is its `X := S -> Prop` instance and `fold_bind` covers both cases.
  Refinement needs `Prop`, so `wp_free` and everything below it is fixed there.
- **`may_pt` is indexed.** The paper's `mayPT` takes a bare predicate on
  results, where `mustPT` takes a relation between input and output. Here both
  take the indexed relation, so the two families are interchangeable and their
  lemmas mirror each other.
- **§6 `soundness`.** Ported verbatim as `rec.soundness`, but the paper's
  hypothesis `∀ i → wpRec spec f P i` silently forces `∀ i → pre spec i`, since
  `wpSpec` has `pre` as a conjunct. That is fine for the paper's `f91Spec`,
  whose precondition is constantly `⊤`, but for a spec with a real precondition
  the hypothesis becomes unsatisfiable and the theorem says nothing at all.
  `rec.soundness_pre` is the same result under `∀ i → pre spec i → wpRec spec f P i`,
  with the conclusion guarded to match; prefer it.
