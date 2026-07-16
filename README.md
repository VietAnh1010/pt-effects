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
| `core/spec.v` | `pt_effects.core.spec` | §7 - `Spec` records, `wp_spec` |
| `effects/partial.v` | `pt_effects.effects.partial` | §3 - `Abort`, `must_pt`, `wp_partial`, `dom` |
| `effects/state.v` | `pt_effects.effects.state` | §4 - `Get`/`Put`, `run`, `state_pt`, `wp_state` |
| `effects/nondet.v` | `pt_effects.effects.nondet` | §5 - `Fail`/`Choice`, `all`, `any` |
| `effects/rec.v` | `pt_effects.effects.rec` | §6 - `Rec`, `call`, `petrol` |
| `effects/refine.v` | `pt_effects.effects.refine` | §7 - refinement calculus |
| `examples/div.v` | `examples.div` | §3 - the expression/division example |
| `examples/relabel.v` | `examples.relabel` | §4.1 - tree relabelling |

## Porting notes

Places where the Rocq version necessarily departs from the Agda:

- **`Set` vs `Prop`.** The paper's predicates land in Agda's `Set`; here they
  land in `Prop`, and response types live in `Type`. So `R Abort = ⊥` becomes
  `R Abort = Empty_set` (a `Type`), while `must_pt`'s abort case is `False` (a
  `Prop`).
- **Functional extensionality.** The `Step` cases of the monad laws need
  `extensionality` - two continuations agreeing pointwise are not
  definitionally equal in Rocq. Agda's development sidesteps this. Only
  `core/free.v` depends on it.
