# An FPRAS for directed-cycle probability

This repository gives an approximation-preserving reduction from directed-cycle
probability to directed two-terminal reliability. It provides approximate
counting and sampling conditioned on cyclicity for independent rational edge
retention, including loops and parallel edges. A supplied feedback vertex set
controls the number of witnesses. Approximating acyclicity probability is hard
unless RP = NP.

Start with the [paper](paper/directed-cycle-fpras.pdf)
([LaTeX source](paper/directed-cycle-fpras.tex)). The
[formalization map](validation/FORMALIZATION.md) connects it to Lean;
[Challenge.lean](Challenge.lean) gives the independent Palomar statements and
[Solution.lean](Solution.lean) their proved implementations.

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

The library entry point is [DirectedCycleFPRAS.lean](DirectedCycleFPRAS.lean).
The runnable counting and sampling programs are
[`Digraph.executableFPRAS` and `Digraph.executableConditionalSampler`](DirectedCycleFPRAS/ExecutableFPRAS.lean).
Their correctness theorems concern execution on uniformly random finite bit
tapes, with all parameters fixed and actual Algorithm S calls included.

Lean checks the witness reduction, corrected rejection, counting and sampling
accuracy, exact zero detection, random-bit budgets, arithmetic-size bounds, and
the independent-set/acyclicity gadget. The counting and sampling proofs have no
oracle-accuracy assumption:
[`Digraph.algS_accuracy`](DirectedCycleFPRAS/AlgorithmSAccuracy.lean) proves
Feng–Fu–Guo's Theorem 9 for Algorithm S. Subtype restriction, parent-pointer
correspondence, and the executable rational refinement are also checked.

Polynomial machine runtime is established by the paper's written bit-complexity
analysis; independent-set inapproximability is cited. See the
[formalization map](validation/FORMALIZATION.md) for declarations and scope,
and the [discretization note](validation/DISCRETISATION.md) for the oracle's
finite-bit implementation.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | Manuscript, PDF, and Makefile. |
| `DirectedCycleFPRAS/` | Lean proofs and executable algorithms. |
| `validation/` | Proof map, discretization note, audits, checks, and generated reports. |
| `scripts/` | Validation commands and finite Python models. |
| `Challenge.lean`, `Solution.lean`, `comparator.json` | Palomar statements and proved counterparts. |
| `formalization.yaml`, `LICENSE` | Provenance, verification scope, and Apache-2.0 licensing. |

## Reproduce

Requires Lean **4.35.0** via [elan](https://github.com/leanprover/elan), pinned
mathlib, and Python 3. The regression checks need no third-party Python packages.

```sh
lake exe cache get              # first setup
bash scripts/check.sh          # Lean build, axiom audit, and finite checks
make -C paper                  # requires LaTeX and latexmk
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound` and rejects
proof admissions and project-defined axioms in the proof development. Deliberate
Challenge holes are excluded; their Solution counterparts are audited.

Finite checks cover adaptive rejection, the hardness gadget, executable rational
operations, and two independent Python ports of Algorithm S. Run
`python3 scripts/algs_transcription/run.py 1,2,3` for larger exact comparisons,
or `python3 scripts/algs_transcription/extended_checks.py` for pool and arc-order
checks and Monte Carlo diagnostics. These are regression evidence; the Python
models have no Lean refinement proof.

For Palomar metadata validation, Comparator checks, and submission instructions,
see [validation/PALOMAR.md](validation/PALOMAR.md). The repository uses the default
root layout at [Palomar's submission form](https://submit.palomar-registry.org/).

## Provenance and review

The motivating question is due to
[Antoine Amarilli](https://cstheory.stackexchange.com/q/53359).
Union estimation follows Karp–Luby–Madras; rejection correction and the
accurate-oracle argument follow Jerrum–Valiant–Vazirani. The paper and
[metadata](formalization.yaml) give the full sources and attribution.

This research draft was developed with AI assistance. Independent expert review
and targeted novelty assessment remain pending.
