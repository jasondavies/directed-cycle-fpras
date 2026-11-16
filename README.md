# An FPRAS for directed-cycle probability

An approximation-preserving reduction from directed-cycle probability to
directed two-terminal reliability. Combined with the reliability theorem of
Feng, Fu, and Guo and the finite-bit implementation developed here, it gives
an FPRAS for independent rational edge retention, including parallel edges
and self-loops. The running time is polynomial in the binary input length,
`1/epsilon`, and `log(1/delta)`, even when the cycle probability is
exponentially small. Zero-probability instances are detected exactly.
The revised manuscript also gives conditional sampling in time polynomial
in `log(1/eta)` and proves hardness of approximating acyclicity probability.

Read the [paper](paper/directed-cycle-fpras.pdf)
([LaTeX source](paper/directed-cycle-fpras.tex)). It presents the reduction,
its error analysis, the bit-cost argument, and the verification boundary.

**Verification status.** Lean verifies the original edge-witness estimator,
including its composed fair-bit and output-size bounds and the subtype and
parent-pointer correspondences. Accuracy assumes `AlgSAccurate`. The revised
vertex witnesses, corrected estimator, conditional sampler, sharper bounds,
and hardness proposition have written proofs and finite checks; they are not
yet formalized. The external accuracy proof and machine-level runtime also
remain outside Lean. See the [formalization map](validation/FORMALIZATION.md).

This is a research draft. Independent expert review and novelty assessment
remain pending. The union-estimation framework is classical. The revision
develops a reliability cover and recorded-probability correction from review suggestions;
novelty of the correction principle is not claimed. The work was developed
with AI assistance.

## The reduction

Split a vertex into incoming and outgoing terminals. The event that it lies
on a retained cycle is exactly a two-terminal reliability event. Any supplied
feedback vertex set of the support gives a cover of all cyclic outcomes;
all vertices are always a valid choice. Write `k` for its size and `m` for
the number of edge variables.

Choose a witness using approximate weights, expose a conditional proposal,
and record the nominal branch-probability product `g`. For a proposal `X`
through witness `i`, accept with probability
`mu(X) / (2 * t(X) * weight[i] * g)`, where `t` counts compatible witnesses.
The recorded factors cancel in the accurate-oracle, exact-choice reference
process. Acceptance has probability `Z/(2*W_hat) >= 1/(4k)` and accepted
configurations have exactly the product law conditioned on cyclicity.

Counting uses `O(k/epsilon^2)` proposals per constant-confidence run, followed
by median amplification. The oracle accuracy is `1/(16*(m+1))`, independent
of `epsilon`. Adaptive-oracle and finite-bit coupling transfer the guarantees
to a bounded implementation. The paper separates these written results from
the older Lean program.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | Manuscript source, PDF, and Makefile. |
| `DirectedCycleFPRAS/` | Lean proofs; `DirectedCycleFPRAS.lean` imports the library. |
| `validation/` | Axiom audit, generated check reports, and the detailed formalization map. |
| `scripts/` | Reproducible checks and Python models. |
| `research/` | Problem statement, supporting proof notes, discretization details, and unsent feedback drafts. |

The main Lean statements are
[`cycle_fpras_of_estimator`](DirectedCycleFPRAS/PositiveOracle.lean) for the
oracle reduction and [`cycleFPRAS_spec`](DirectedCycleFPRAS/ConcreteResources.lean)
for the expanded program. The
[original edge-witness proof](research/SOLUTION.md) and
[discretization note](research/DISCRETISATION.md) document the earlier estimator
and the shared oracle construction;
the [problem note](research/PROBLEM.md) records the original question and sources.

## Reproduce

Requires Lean **4.35.0** via [elan](https://github.com/leanprover/elan), the
pinned mathlib dependency, and Python 3. No third-party Python packages are needed.

```sh
lake exe cache get              # first setup
bash scripts/check.sh          # build, axiom audit, and finite checks
make -C paper                  # requires LaTeX and latexmk
```

The audit covers 100 declarations and permits only `propext`,
`Classical.choice`, and `Quot.sound`; there are no proof admissions or
project-defined axioms. Reports are written to `validation/`.

Python checks use exact enumeration or test oracles on small graphs. They
are finite regression evidence, not a polynomial-time reliability
implementation or a proof of equivalence with Lean. The default checks
enumerate randomized oracle transcripts for the corrected rejection model,
check its counting and conditional-sampling identities, and check the hardness
gadget on all simple undirected graphs with at most four vertices. They also
compare the two Algorithm S ports at `M=1`; run
`python3 scripts/algs_transcription/run.py 1,2,3` for the larger exact suite.

## Next steps

1. Obtain expert review of the reduction, finite-bit adaptation, and novelty.
2. Formalize vertex splitting, the adaptive-transcript cancellation, and the
   corrected estimator and sampler, retaining the existing correspondence laws.
3. Review the external accuracy transfer and prepare a release with confirmed
   authorship and publication metadata.

The external accuracy proof and a machine-level runtime formalization are
separate, substantially larger projects. Neither is claimed in this draft.
