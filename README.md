# Directed-cycle probability via reliability

An approximation-preserving reduction from directed-cycle probability to directed
two-terminal reliability, with a Lean 4 formalisation of the graph, sampling,
and statistical core.

**Status:** the written reduction is complete; the Lean formalisation is partial.
Lean verifies the witness identity, its reliability factorisation, and a robust
estimator with failure probability at most 1/4 under explicit weight-estimation
and sampling-law contracts. The complete randomized-oracle implementation and
polynomial bit-cost theorem are **not yet formalised**. See the exact boundary
in [FORMALIZATION.md](FORMALIZATION.md).

- [Problem and public status](PROBLEM.md)
- [Written solution and external theorem](SOLUTION.md)
- [Formalisation map and remaining obligations](FORMALIZATION.md)
- [Graph-specific estimator theorem](DirectedCycleFPRAS/CycleEstimator.lean)
- [Reduction of witness weights to reliability](DirectedCycleFPRAS/ReliabilityIdentity.lean)

For each edge e=(u,v), use the event that e is present and v reaches u without e.
Its probability is `p_e * Rel_(G-e)(v,u)`. These events cover exactly the cyclic
subgraphs. Selecting a witness proportionally to its probability and sampling
conditionally gives an outcome with probability proportional to its number of
witnesses. Correcting by the inverse of that count yields an unbiased union
estimator. The Lean development also controls approximate versions of this law.

## Build

Requires [elan](https://github.com/leanprover/elan) and Python 3 for the checks.
The toolchain is Lean **4.35.0**; mathlib is pinned to its matching release and
an exact dependency manifest is included.

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_formalization.py
python3 scripts/run_cycle_fpras_checks.py
```

`check_formalization.py` runs the build and audits the named public theorems.
The audit permits only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. There are no admitted proofs or project-defined axioms.
The Python regression tests use an **exponential exact reliability oracle** and
bounded-error test oracles. They do not implement the external reliability FPRAS
and are not the justification for the Lean theorems.

## What is verified

The main statistical theorem, `Digraph.cycle_estimator_success`, concerns
independent edge retention with probabilities in [0,1], including loops and
parallel arcs. Write W for total witness mass, Z for cycle probability, and
q for the ideal size-biased mixture. For W>0 and 0<epsilon<=1, it proves that
`ceil(1024*m^2/epsilon^2)` independent samples give relative error at most
epsilon except with probability at most 1/4, provided:

- the supplied estimate w satisfies `|w-W| <= epsilon*W/4`;
- the supplied sampling law p satisfies `sum_x |p(x)-q(x)| <= epsilon/(16*m)`.

These contracts are explicit hypotheses, not hidden axioms. Additional checked
lemmas establish stability of normalised weights and sequential sampling, and
identify every witness weight with a deleted-edge reliability probability.
Instantiating all these pieces with the randomized oracle and finite-bit sampler
is the remaining formalisation work.

## Provenance

Extracted from a3nm-012 in `../open-problems`; written proof dated 2026-10-25,
Lean development begun 2026-11-12. This work was developed with AI assistance.
Independent review and novelty checking remain pending. The substantial
external reliability result is due to Feng, Fu, and Guo; the classical
witness-union estimator is not claimed as new. See [SOLUTION.md](SOLUTION.md).
