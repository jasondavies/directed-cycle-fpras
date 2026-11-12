# Directed-cycle probability via reliability

An approximation-preserving reduction from directed-cycle probability to directed
two-terminal reliability, with a Lean 4 formalisation of the reduction's
probabilistic correctness.

**Status:** the written reduction is complete. Lean verifies the correctness of
the whole oracle algorithm: given a randomized reliability oracle that is
accurate with probability at least 3/4 per call, the algorithm's output has
relative error at most epsilon with probability at least 3/4, using explicit
numbers of samples, oracle calls, random bits and charged local operations,
and bounds on the size of every query and of the output. There is no machine
model, so polynomial running time is assembled from these verified bounds by a
written argument, and the reliability FPRAS itself is a hypothesis. See the exact boundary in
[FORMALIZATION.md](FORMALIZATION.md).

**Cost model:** the cited reliability theorem is stated in a unit-cost model
with real uniform random draws. [DISCRETISATION.md](DISCRETISATION.md) argues
that the paper's simple algorithm can be run on fair random bits with
polynomial bit complexity, which is what the bit-model claim needs. Lean
checks this for a transcription of that algorithm, taking the paper's
Theorem 9 as a hypothesis.

- [Problem and public status](PROBLEM.md)
- [Written solution and external theorem](SOLUTION.md)
- [Formalisation map and remaining obligations](FORMALIZATION.md)
- [Running the reliability oracle on random bits](DISCRETISATION.md)
- [The algorithm and the reduction theorems](DirectedCycleFPRAS/Reduction.lean)
- [Graph-specific estimator theorem](DirectedCycleFPRAS/CycleEstimator.lean)
- [Reduction of witness weights to reliability](DirectedCycleFPRAS/ReliabilityIdentity.lean)

For each edge e=(u,v), use the event that e is present and v reaches u without e.
Its probability is `p_e * Rel_(G-e)(v,u)`. These events cover exactly the cyclic
subgraphs. Selecting a witness proportionally to its probability and sampling
conditionally gives an outcome with probability proportional to its number of
witnesses. Correcting by the inverse of that count yields an unbiased union
estimator. Conditional sampling exposes one edge at a time, using two residual
reliability estimates per edge.

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

The algorithm is `Digraph.cycleAlgorithm`, a randomized program whose only
oracle queries are reliability instances on the input graph with some edge
probabilities replaced by 0 or 1. Write m for the number of edges and Z for the
cycle probability. For independent edge retention with probabilities in [0,1],
including loops and parallel arcs, and 0<epsilon<=1:

- `Digraph.cycle_fpras_of_constant_confidence`: if every oracle call on such an
  instance of positive reliability has relative error at most
  `epsilon/(128*m*(m+1))` with probability at least 3/4, using fresh randomness,
  then with `n = ceil(2048*m^2/epsilon^2)` samples and each query answered by
  the median of `6*ceil(log2(8*T))` calls, `T = m + 2*m*n`, the output is
  within relative error epsilon of Z except with probability at most 1/4.
- `Digraph.cycle_fpras_confidence`: the median of `O(log(1/delta))` such runs
  fails with probability at most delta.
- `Digraph.cycle_fpras_of_estimator`: the same from one hypothesis, a
  reliability estimator that is accurate with probability 3/4 on finite
  directed multigraphs with probabilities in (0,1], which is the input class
  of the cited theorem. Zero-probability edges are deleted before each call.
- `Digraph.cycleAlgorithm_of_cycleMass_eq_zero`: if Z=0 the algorithm makes no
  oracle call and returns exactly 0.
- `Digraph.cycleAlgorithm_failure`: the same for a general per-call failure
  probability gamma, with failure at most the Chebyshev term plus `T*gamma`.
  Queries are adaptive; the proof couples the oracle with a repaired one and
  never conditions on all calls succeeding.
- `Digraph.cycleAlgorithm_queryBound` and `Digraph.cycleAlgorithm_bitBound`:
  at most T oracle calls, and all internal randomness is at most `n*(m+1)`
  uniform draws of `bitBudget m epsilon` bits.
- `Digraph.cycleAlgorithm_workBound`: at most `2*m + n*(6*m+2)` charged local
  operations (reachability tests and steps of discrete choices). The charges
  are annotations in the program, trusted like cslib's `TimeM` ticks.
- `Digraph.cycleAlgorithm_sat`: every query is a residual instance of the
  input, and if input probabilities and oracle answers are fractions with
  numerator and denominator at most `Hp` and `Ho`, the output is a fraction
  with numerator and denominator at most `(2*Hp*Ho)^m * n * m!`.
- `Digraph.cycleAlgorithm_weightSat`: every weight used in a discrete choice
  has numerator and denominator at most `2*Hp*Ho`.

The oracle contract is an explicit hypothesis, not a hidden axiom, and
`Digraph.cycleAlgorithm_exactOracle` shows it is satisfiable. Supporting
results include the witness identity, the weight/reliability identity, exact
and approximate sequential conditional sampling, the support test for the zero
case, the rounding error of fixed-bit choices, and median amplification. The
earlier statistical theorem `Digraph.cycle_estimator_success`, which takes the
sampling law as an input, remains and is what the reduction instantiates.

What is still only a written argument: turning these counts and size bounds
into a machine-level running time, and the Hoeffding route to confidence `1-delta`. Details are in [FORMALIZATION.md](FORMALIZATION.md).

## Provenance

Extracted from a3nm-012 in `../open-problems`; written proof dated 2026-10-25,
Lean development begun 2026-11-12. This work was developed with AI assistance.
Independent review and novelty checking remain pending. The substantial
external reliability result is due to Feng, Fu, and Guo; the classical
witness-union estimator is not claimed as new. See [SOLUTION.md](SOLUTION.md).
