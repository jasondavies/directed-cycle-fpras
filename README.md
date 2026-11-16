# Directed-cycle probability via reliability

An approximation-preserving reduction from directed-cycle probability to
directed two-terminal reliability. Combined with the reliability theorem of
Feng, Fu, and Guo and the finite-bit implementation developed here, it gives
an FPRAS for independent rational edge retention, including parallel edges
and self-loops. The running time is polynomial in the binary input length,
`1/epsilon`, and `log(1/delta)`, even when the cycle probability is
exponentially small. Zero-probability instances are detected exactly.

Read the [paper](paper/directed-cycle-fpras.pdf)
([LaTeX source](paper/directed-cycle-fpras.tex)). It presents the reduction,
its error analysis, the bit-cost argument, and the verification boundary.

**Verification status.** Lean checks the probabilistic reduction and explicit
resource bounds. The final theorem, `Digraph.cycleFPRAS_spec`, combines
accuracy, total fair-bit usage, and rational output size for one program
with every oracle call expanded and both amplification stages included.
Accuracy assumes the stated guarantee for the transcribed Algorithm S.
Lean also proves whole-program output-law equivalence for induced vertex/edge
subtypes with inherited arc order and for an explicit parent-pointer traversal.
The external accuracy proof, its larger-budget variance argument, and
machine-level runtime remain outside Lean. See the [formalization map](validation/FORMALIZATION.md).

This is a research draft. Independent expert review and novelty assessment
remain pending. The union estimator is classical; the proposed contribution
is its application through reliability queries, with adaptive-error and
finite-bit analysis. The work was developed with AI assistance.

## The reduction

For each edge `e=(u,v)`, use the event that `e` is present and `v` reaches `u`
without `e`. Its probability is `p_e * Rel_(G-e)(v,u)`. These `m` events cover
exactly the cyclic outcomes, although the graph may have exponentially many
cycles.

Choose an event proportionally to its probability and sample conditionally
on it. If the sampled graph belongs to `t` witness events, give it score
`1/t`. The expected score is the cycle probability divided by the sum of
witness probabilities, and is at least `1/m`. Reliability estimates provide
both the weights and conditional samples. The proof controls approximate
choices and adaptive oracle failures without conditioning on all calls
succeeding.

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
[written proof](research/SOLUTION.md) and
[discretization note](research/DISCRETISATION.md) give supporting details;
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
compare the two Algorithm S ports at `M=1`; run
`python3 scripts/algs_transcription/run.py 1,2,3` for the larger exact suite.

## Next steps

1. Obtain expert review of the reduction, finite-bit adaptation, and novelty.
2. Review the transfer of the cited accuracy theorem, especially the
   larger-budget variance argument, against the verified correspondence laws.
3. Prepare a reviewed release with confirmed authorship and publication metadata.

The external accuracy proof and a machine-level runtime formalization are
separate, substantially larger projects. Neither is claimed in this draft.
