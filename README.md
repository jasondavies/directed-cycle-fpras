# An FPRAS for directed-cycle probability

This repository gives an approximation-preserving reduction from directed-cycle
probability to directed two-terminal reliability. It provides approximate
counting and sampling conditioned on cyclicity for independent rational edge
retention, including loops and parallel edges. A supplied feedback vertex set
controls the number of witnesses. Approximating acyclicity probability is hard
unless RP = NP.

Read the [paper](paper/directed-cycle-fpras.pdf), or its
[LaTeX source](paper/directed-cycle-fpras.tex). The
[formalization map](validation/FORMALIZATION.md) connects the paper to Lean.

## The idea

Split a vertex into incoming and outgoing terminals. The event that it lies
on a retained cycle becomes a two-terminal reliability event. A feedback vertex
set of the positive support covers every cyclic outcome; all vertices suffice.
Write `k` for the cover size and `m` for the number of edge variables.

Choose a witness using estimated weights, generate a conditional proposal,
and record the product `g` of its nominal branch probabilities. Accept a
configuration `X` generated through witness `i` with probability
`mu(X) / (2 * t(X) * weight[i] * g)`, where `t` counts compatible witnesses.
The recorded factors cancel. In the accurate-oracle, exact-choice process,
acceptance probability is `Z/(2*W_hat) >= 1/(4k)` and the accepted configuration
has exactly the product law conditioned on cyclicity.

Counting uses `ceil(64*k/epsilon²)` proposals per run, followed by median
amplification. Sampling stops at the first acceptance, with a cap of
`4*k*ceil(log2(3/eta))`. Reliability accuracy is `1/(16*(m+1))`, independent of
both error targets. Adaptive-oracle and finite-bit coupling bound implementation
error.

## Lean results

The entry point is [DirectedCycleFPRAS.lean](DirectedCycleFPRAS.lean).
The development checks the vertex cover, adaptive rejection identity, counting
and conditional-sampling guarantees, oracle-call and fair-bit budgets, rational
counting-output size, and the acyclicity/independent-set reduction.

- [`Digraph.cycleFPRAS_correct`](DirectedCycleFPRAS/Parameters.lean): the counting
  program with its budgets fixed and Algorithm S calls expanded.
- [`Digraph.cycleSampler_cyclic_correct`](DirectedCycleFPRAS/Parameters.lean): the
  bounded conditional sampler, in the bounded-test formulation of total variation.
- [`Digraph.concreteVertex_bitCost`](DirectedCycleFPRAS/ConcreteVertex.lean) and
  [`Digraph.concreteVertex_height`](DirectedCycleFPRAS/RejectionHeight.lean):
  resource bounds for the same counting program.
- [`AcyclicityReduction.edge_retention_probability`](DirectedCycleFPRAS/AcyclicityReduction.lean):
  the exact probability identity used by the complement-hardness proposition.

Algorithm S and its accuracy theorem are proved in Lean:
[`Digraph.algS_accuracy`](DirectedCycleFPRAS/AlgorithmSAccuracy.lean) establishes
Feng–Fu–Guo's Theorem 9 for the concrete program, and `algSEstimator_correct`
transfers it to the finite-bit estimator. The counting and sampling theorems
have no oracle-accuracy assumption. The proof includes deferred edge exposure,
DFS snapshot splitting, conditional moments, and the complete stopped round
process. Induced-subtype and parent-pointer correspondences are also checked.
Independent-set complexity hardness is cited; machine-level running time is
justified by the written bit analysis.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | Manuscript, PDF, and Makefile. |
| `DirectedCycleFPRAS/` | Lean probability, reduction, resource, and Algorithm S proofs. |
| `validation/` | Formalization map, principal-theorem axiom audit, and generated reports. |
| `scripts/` | Exact finite checks and executable Python models. |
| `research/` | Problem provenance, oracle discretization details, and unsent feedback drafts. |

## Reproduce

Requires Lean **4.35.0** via [elan](https://github.com/leanprover/elan), pinned
mathlib, and Python 3. The Python checks need no third-party packages.

```sh
lake exe cache get              # first setup
bash scripts/check.sh          # Lean build, axiom audit, and finite checks
make -C paper                  # requires LaTeX and latexmk
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound` and rejects
proof admissions and project-defined axioms. Reports are written to `validation/`.

Python checks enumerate adaptive oracle transcripts, verify the counting and
sampling identities, and check the hardness gadget on all simple undirected
graphs with at most four vertices. They also compare two independently written
Algorithm S ports at `M=1`; run `python3 scripts/algs_transcription/run.py 1,2,3`
for the larger exact suite. These checks are finite evidence, not a refinement
proof between Python and Lean or an implementation of the reliability FPRAS.

## Research status

This is a research draft developed with AI assistance. Independent expert review
and targeted novelty assessment remain pending; [feedback requests](research/feedback-drafts.txt)
are drafted and unsent. The publication case rests on the directed-cycle
consequence of the reliability cover. Union estimation follows Karp–Luby–Madras;
rejection correction and the accurate-oracle argument follow
[Jerrum–Valiant–Vazirani (1986)](https://ics.uci.edu/~vazirani/JVV.pdf).
See the [problem note](research/PROBLEM.md) and
[oracle discretization note](research/DISCRETISATION.md) for context.
