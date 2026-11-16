# Formalisation scope

The project uses finite real-valued probability laws, finite sums and products,
and relational reachability. These are mathematical semantics; a finite sum
being executable by exhaustive enumeration does not make it polynomial-time.
All theorems below are checked by Lean. No `sorry`, project axioms, or native
computation oracle is used to obtain them.

`Digraph.cycleFPRAS_spec` is the main composed theorem: one program satisfies
the accuracy bound, a total fair-bit budget including both amplification
stages, and a rational output-size bound. Accuracy assumes `AlgSAccurate`;
the resource bounds do not. Whole-program subtype and parent-pointer
correspondences are proved. The external accuracy proof, its larger-budget
variance argument, and machine-level runtime are outside Lean.

**Revision boundary.** The manuscript now leads with vertex/feedback-set
witnesses and corrected rejection. The existing Lean program still uses the
original edge-witness inverse-multiplicity estimator and its original budgets.
Vertex splitting, adaptive-transcript cancellation, the new conditional
sampler, sharpened concentration, and acyclicity hardness are not formalized.
`scripts/check_corrected_rejection.py` provides exact finite evidence for the
new model, not a Lean proof or an implementation of the reliability FPRAS.

This file is the detailed reference. Start with the
[paper](../paper/directed-cycle-fpras.pdf) for the mathematical argument.

## Modules

| Module | Verified content |
| --- | --- |
| `GraphWitness` | A nonempty closed directed walk exists iff some retained edge has a return walk after that edge is deleted; loops and parallel edges are allowed. |
| `WitnessMixture` | Witness multiplicities and weights; `Z <= W <= m*Z`; zero-mass equivalence; normalised mixture; equality with the conditional-witness sampling recipe; expected inverse multiplicity `Z/W >= 1/m`. |
| `Perturbation` | L1 control of bounded expectations, mixtures, and witness selection; relative errors in weights give at most `4*alpha` L1 error after normalisation. |
| `FiniteLaw` | Normalised finite laws, sequential sampling, Markov and Chebyshev inequalities, and a sequential L1 error bound allowing adaptive state. |
| `IndependentSamples` | Explicit independent product laws, zero centered mean, variance additivity, and the sample-average tail bound. |
| `Estimator` | Multiplication of relative approximations; the robust estimator bound; a concrete sample budget with failure probability at most 1/4. |
| `CycleEstimator` | Independent Bernoulli edge-retention law, equality of cycle probability with witness-union mass, and the robust estimator applied to this graph model. |
| `ReliabilityIdentity` | Product-law factorisation at a designated edge and `w_e = p_e * Rel_(G-e)(target(e),source(e))`. |
| `ProductLaw` | Pinning an edge probability to 0 or 1; the one-edge decomposition `R(q) = q_f R(q[f:=1]) + (1-q_f) R(q[f:=0])`; independence of an event from an irrelevant edge; a monotone event has positive probability iff it holds on the positive-probability support; exact sequential decomposition of a conditional product law. |
| `OracleProgram` | Randomized programs with adaptive oracle queries (`Prog`), oracles with fresh finite randomness per call (`Oracle`), expectation semantics, output laws, independent repetitions equal the explicit product law, oracle-call counting, and the good-oracle coupling `Prog.exp_le_repair`. |
| `RandomBits` | A discrete choice implemented by one uniform `b`-bit integer and cumulative intervals; each alternative's mass is within `2^(-b)` of its target, so the L1 error is at most `k/2^b`; a predicate counting uniform `b`-bit draws on every path. |
| `ConditionalSampler` | The edge-exposure sampler `expose` with guarded oracle calls and its L1 distance to the exact conditional law: at most `4*alpha + 2/2^b` per exposed edge, for a randomized oracle whose answers are always `alpha`-accurate. |
| `Amplification` | The law of `k` independent seeds, the lower sample median (zero for an empty sample), proved to be an input value whenever the sample is nonempty, and `Oracle.amplify_failure`: per-call failure at most 1/4 becomes at most `(7/8)^k`. |
| `Confidence` | The median of `k` independent runs of a real-valued program fails with probability at most `(7/8)^k`; the reduction at confidence `1 - delta`. |
| `Resources` | Charged local-operation count, the invariant that every query is a feasible residual instance, a size calculus for fractions, the output size bound, and division-free selection. |
| `PositiveOracle` | Removing deterministic coordinates of a product law; deleting zero-probability edges preserves reliability; the reduction from an estimator for multigraphs with probabilities in `(0,1]`. |
| `Discretise` | Replacing every exact choice of an adaptive program by a `b`-bit draw changes any `[0,1]` expectation by at most `N/2^b`, `N` the total number of alternatives on a path. |
| `AlgorithmS` | A transcription of the cited paper's Algorithm S as a program; its count of random alternatives, a common-denominator bound on its output size, and the guarantee of its `b`-bit version given the paper's Theorem 9. |
| `AlgorithmSEstimator` | A call-free program as a randomized real with a finite seed space; the `b`-bit Algorithm S as a `ReliabilityEstimator`, its correctness and answer size; the end-to-end theorem `cycle_fpras_of_algS`. |
| `ProgramComposition` | Query inlining preserves the law, including amplified queries; sample medians preserve rational height; a varying-width fair-bit cost composes through inlining and repetition. |
| `ConcreteResources` | The call-free program `cycleFPRAS` and `cycleFPRAS_spec`: accuracy, total fair-bit budget, and rational output height together, including zero sample budgets and equal-terminal residual queries. |
| `AlgorithmSInvariants` | DFS stack/cardinality potential, sufficient DFS and round fuel, closed-set exploration, the path-flag identity, and generated count equals pool length. |
| `FirstOpen` | Exact partial-assignment factorization, first-open event probabilities, their disjoint mixture, and the conditional product-law identity. |
| `AlgorithmSRestriction` | Equality of the entire Algorithm S output law under probability changes outside a closed set containing the source; in particular, zeroing unreachable edges. This retains the ambient vertex and edge types and the same sample budget. |
| `AlgorithmSPools` | Positive estimates correspond to nonempty pools; initialization and round updates preserve pool invariants; supported records contain their target; padded-index sampling is uniform and invariant under pool permutation; the actual first-open choice realizes the conditional product law when its conditioning mass is positive. |
| `AlgorithmSStopping` | Early stopping has the same recorded-snapshot law as recording at the target pop and then finishing DFS; the finishing traversal also satisfies the fuel bound. |
| `ReindexLaw` | Normalized finite choices preserve expectations under injective reindexing when omitted weights vanish; the default fallback is retained. |
| `AlgorithmSOrdered` | Algorithm S with explicit arc order, first-open ranks, and separate DFS/round fuel; its canonical specialization equals `algS`. |
| `AlgorithmSSubtypes` | Actual induced vertex/edge types; inherited arc list is complete and duplicate-free when the original is; scan, DFS, choices, pools, and whole rounds preserve the output law. `algS_reachable_subtype` specializes to reachable vertices, keeping the sample budget and ambient fuel. |
| `AlgorithmSParents` | Explicit parent table and vertex-only stack; installing a parent preserves old path tests and gives the flag recurrence for the new vertex. Scan and full DFS simulate the flag version; sufficient fuel empties the finishing traversal's stack. |
| `AlgorithmSParentProgram` | A separate parent-pointer iteration, Generate, and rounds program. `parentAlgS_law` proves equality of the complete output law for probabilities in `[0,1]` and `M > 0`; `parentAlgS_inducedClosed` combines both correspondences. |
| `Reduction` | Two-terminal reliability, the support test, the witness queries, the complete algorithm `Digraph.cycleAlgorithm`, its call and bit budgets, and the reduction theorems below. |

The entry point `DirectedCycleFPRAS.lean` imports all modules. `validation/Axioms.lean`
prints the dependencies of the principal results.

## The reduction theorems

Throughout, `m` is the number of edges, `Z` the cycle probability, and a
*query* is a triple `(q, s, t)`: edge probabilities on the fixed input graph
and two terminals. Its exact answer is `Digraph.reliability q s t`. A query is
*valid* for input `p` (`Digraph.Valid`) when every `q e` is `p e`, `0` or `1`
and the reliability is positive. An answer `r` is *accurate*
(`Digraph.Accurate alpha`) when `|r - R| <= alpha * R`.

The algorithm `Digraph.cycleAlgorithm p bits n` is a `Prog`:

1. If the positive-probability support is acyclic, return 0 with no oracle call.
2. For each edge `e`, estimate `w_e = p_e * Rel(p[e:=0], target e, source e)`.
3. Repeat `n` times: choose a witness `e` proportionally to the estimates,
   fix `e` present, and expose every edge in turn. Each exposure asks for the
   two residual reliabilities and chooses the bit proportionally to
   `q_f * R_1` and `(1-q_f) * R_0`.
4. Return `(sum of estimates) * (average of 1/t(X_j))`.

Every oracle call is guarded by reachability in the support: an infeasible
instance gets the answer 0 and no call is made. Every discrete choice consumes
one uniform `bits`-bit integer. Unusable weights fall back to a fixed
alternative.

| Theorem | Statement |
| --- | --- |
| `Digraph.cycleAlgorithm_queryBound` | At most `m + 2*m*n` oracle calls on every execution path. |
| `Digraph.cycleAlgorithm_bitBound` | Every internal random choice is a uniform `bits`-bit draw, and at most `n*(m+1)` draws occur on every path. |
| `Digraph.cycleAlgorithm_workBound` | At most `2*m + n*(6*m + 2)` charged local operations on every path. |
| `Digraph.cycleAlgorithm_sat` | For `n > 0`, if the input probabilities are fractions with numerator and denominator at most `Hp` and the oracle's answers likewise at most `Ho`, then every query asked is a residual instance passing the support test, and the output is a fraction with numerator and denominator at most `(2*Hp*Ho)^m * n * m!`. |
| `Digraph.cycleAlgorithm_ideal` | If *every* answer to a valid query is `eps/(128 m (m+1))`-accurate (the oracle may still be randomized) and `(3m+1)/2^bits <= eps/(32 m)`, then `Pr[|Zhat - Z| > eps*Z] <= 1/(n (eps/(16 m))^2)`. |
| `Digraph.cycleAlgorithm_failure` | If instead each call on a valid query is inaccurate with probability at most `gamma`, the bound is the same plus `(m + 2*m*n) * gamma`. |
| `Digraph.cycle_fpras_reduction` | With `n = ceil(2048 m^2/eps^2)`, `bits = bitBudget m eps` and `(m + 2*m*n) * gamma <= 1/8`: failure probability at most 1/4. |
| `Digraph.cycle_fpras_of_constant_confidence` | If each call on a valid query is accurate with probability at least 3/4, then the algorithm run against the median of `6 * ceil(log2(8 T))` independent calls, `T = m + 2*m*n`, fails with probability at most 1/4. |
| `Digraph.cycle_fpras_confidence` | Under the same contract, the median of `6 * ceil(log2(ceil(1/delta)))` independent runs fails with probability at most `delta`, for every `delta > 0`. |
| `Digraph.cycle_fpras_of_estimator` | The same conclusion from a single hypothesis: a randomized estimator that, on every finite directed multigraph with probabilities in `(0,1]` and positive reliability, has relative error at most `eps/(128 m (m+1))` with probability at least 3/4. Each query is answered by deleting its zero-probability edges and calling the estimator. |
| `Digraph.cycle_fpras_of_algS` | The same conclusion with a concrete oracle, the `b`-bit Algorithm S, and a single hypothesis, `AlgSAccurate alpha` for every `alpha` in `(0,1)`: the exact Algorithm S is accurate with probability 7/8. All randomness, of the reduction and of the oracle, is fair bits. |
| `Digraph.cycleAlgorithm_weightSat` | The algorithm consists of oracle calls and weighted draws only, and every weight handed to a draw is a fraction with numerator and denominator at most `2*Hp*Ho`; by `height_partialSum` the partial sums compared in selection are at most `(4*Hp*Ho)^(m+1)`. |
| `Digraph.cycleAlgorithm_of_cycleMass_eq_zero` | If `Z = 0` the algorithm is literally `ret 0`: no oracle call, no randomness, output exactly 0. |
| `Digraph.cycleAlgorithm_exactOracle` | The exact oracle meets the contract, so the hypotheses are satisfiable. |

The accuracy theorems apply to `0 < eps <= 1` and probabilities in `[0,1]`,
allow loops and parallel edges, and include `Z = 0`. Individual resource
theorems have the hypotheses displayed above; `cycleFPRAS_spec` assembles
the total bounds for the final program. `cycleAlgorithm_ideal` and
`cycleAlgorithm_failure` implicitly need `m >= 1` through their hypothesis on
`bits`; the later theorems treat the edgeless graph separately.
The oracle is constrained only on valid queries; on every other input it may
answer arbitrarily.

### The composed program and its resource bounds

`Digraph.cycleFPRAS p eps delta : Prog Empty ℝ` expands every oracle call
into discretised Algorithm S, with the inner oracle median and outer run
median both included. `Digraph.concreteCycle_law` proves its law equals the
previous abstract-oracle program. `Digraph.cycleFPRAS_spec` gives the three
claims about this same program: failure at most `delta`, a bound on **all**
fair bits on every execution, and rational output height on every branch.
Accuracy retains the explicit `AlgSAccurate` hypothesis. The resource claims
do not depend on that hypothesis.

Write `n = |V|`, `m = |E|`, `N = reductionBudget m eps`,
`T = m + 2*m*N`, `k = amplifyRounds T`, `r = confidenceRuns delta`,
`a = eps/(128*m*(m+1))`, and `b = bitBudget m eps`.
The complete fair-bit bound is

```text
b * r * N * (m+1) + r * T * k * oracleBitBudget n m a.
```

`oracleBitBudget` sums `algSBits n j Mj * algSChoices n j Mj` over
`0 <= j <= m`, with `Mj = algSSamples n j a`. This safely bounds every
possible positive-edge subgraph without requiring monotonicity in `j`.
For input denominators at most `H >= 1`, `oracleHeight n m H a` similarly
bounds the base oracle answers uniformly over these subgraphs. The final
height is at most

```text
max 1 ((2 * H * oracleHeight n m H a)^m * N * m!).
```

Neither median increases height. In particular, even-sized samples select
an actual input value, rather than an arbitrary real between the two middle
values. Empty samples return zero. The total height statements also cover
`M = 0`, an edgeless positive part, and equal terminals; they do not assume
that a feasible residual query has a positive Algorithm S sample budget.

### How the original edge-witness argument maps to Lean

| Written step (research/SOLUTION.md) | Lean |
| --- | --- |
| Section 1, witness family and mixture | `cyclic_iff_exists_witness`, `Mass.mixture_eq_conditioned_sum`, `Mass.mixture_score` |
| Section 1, `w_e = p_e Rel_(G-e)(v,u)` | `weight_eq_edge_mul_reliability`, `deletedReliability_eq_exact`, `weight_eq_edge_mul_exact` |
| Section 2, branch weights `b_0, b_1` and exact conditional sampling | `eventMass_split`, `condWeight_split`, `conditional_eq_condWeight` |
| Section 2, support reachability decides feasibility | `eventMass_pos_iff`, `reliability_pos_iff`, `Prog.guarded` |
| Section 2, `4*alpha` per choice, `4(m+1)*alpha` in total | `normalised_weights_l1`, `expose_l1`, `sampler_l1` |
| Section 2, averaging over random oracle estimates | `l1_average_le`, used inside `expose_l1` |
| Section 3, independent runs given the initial estimates | `Prog.exp_replicate`, `exp_initWeights_le` |
| Section 3, fictitious oracle and coupling without conditioning | `Oracle.repair`, `Prog.exp_le_repair` |
| Section 3, median amplification | `Oracle.amplify`, `Oracle.amplify_failure`, `amplifyRounds_bound` |
| Section 3, zero case | `cycleMass_pos_iff`, `cycleAlgorithm_no_edges` |
| Section 4, `k/2^b` per `b`-bit choice | `bitLaw_error`, `bitLaw_l1`, `Prog.exp_draw` |
| Section 4, residual instances do not grow | `Derived`, `derived_pin`, `cycleAlgorithm_sat`; the oracle contract is restricted to them |
| Section 4, output bit length `O(m log m) + O(log N)` beyond the weights | `score_eq_div_factorial`, `sampleSum_common_denominator`, `cycleAlgorithm_sat` |
| Section 4, choices need only rational comparisons | `hit_normLaw_iff`, `cycleAlgorithm_weightSat`, `height_partialSum` |
| Section 4, delete zero-probability edges before calling the oracle | `eventMass_restrict`, `reliability_positivePart`, `oracleOfEstimator` |

### Original parameters and the revised manuscript

The following table compares the preserved original argument in
`research/SOLUTION.md` with Lean. It is not the revised paper's algorithm.

| Quantity | Original written proof | Formal |
| --- | --- | --- |
| Concentration | Hoeffding, `log(1/delta)` | Chebyshev, failure 1/8, then a median of runs |
| Samples | `ceil(200 m^2 eps^-2 ceil(log2(4/delta)))` | `ceil(2048 m^2/eps^2)` |
| Oracle accuracy | `eps/(100 m (m+1))` | `eps/(128 m (m+1))` |
| Rounding of choices | separate failure budget `delta/4` by coupling | L1 error `(3m+1)/2^bits`, absorbed into the sampling-law budget |
| Oracle failure budget | `delta/(4T)` per call | `T * gamma <= 1/8`, with `gamma = (7/8)^k` after amplification |
| Range of `eps` | `(0, 1/2]` | `(0, 1]` |

The revised manuscript instead uses `k` vertex witnesses, oracle accuracy
`1/(16*(m+1))`, and `ceil(64*k/eps^2)` Bernoulli proposals per complete run.
It uses Chebyshev and a median of independent complete runs, with separate
whole-run coupling budgets for oracle failure and rounding. A second theorem
uses a capped rejection sampler. None of these new algorithm-specific bounds
is supplied by `cycleFPRAS_spec`.

## What is not formalised

1. **A machine-level running time.** `Prog` is a mathematical decision tree,
   not a machine model. What Lean proves is the list of ingredients:
   oracle calls (`cycleAlgorithm_queryBound`), random bits
   (`cycleAlgorithm_bitBound`), charged local operations
   (`cycleAlgorithm_workBound`), the size of every query and of the output
   (`cycleAlgorithm_sat`), and that selection needs no division
   (`hit_normLaw_iff`). What remains a written step:
   - The local-operation charges are annotations placed in `Prog.guarded`
     (one support-reachability test), `Prog.draw` (one step per alternative)
     and the final aggregation (`n*m` witness tests and two sums). Lean proves
     their total, not that each charge matches a real cost; these charges are part of the model. The initial cyclicity test of the
     support and the handful of arithmetic operations next to each guard or
     draw are not charged separately.
   - Each charged operation is a reachability test on the input graph or
     `O(1)` arithmetic operations and comparisons on fractions. That these
     take polynomial time in the operand sizes is standard and not formalised.
   - Size bounds are proved for the queries, the output, every weight handed
     to a discrete choice (`cycleAlgorithm_weightSat`) and the partial sums
     the selection rule compares (`height_partialSum`). `WeightSat` asserts
     that the program can be presented as draws on weights of that size; it
     does not inspect a concrete data representation.
2. **The external theorem.** The reliability FPRAS of Feng, Fu and Guo is a
   hypothesis: `ReliabilityEstimator.Correct`, an estimator accurate with
   probability at least 3/4 on finite directed multigraphs with probabilities
   in `(0,1]`, at the single accuracy level the theorem names. This matches
   the input class of their Theorem 1 as stated in arXiv:2608.02523v2, which
   allows parallel arcs and self-loops and takes rational probabilities in
   `(0,1]`. Its existence and its cost are outside this repository.

   **Cost model.** The paper's running times count unit-cost arithmetic
   operations and draws of uniform real variables; it gives no bit-complexity
   bound. The formal hypothesis asks for a finite seed space, and
   `cycleAlgorithm_sat` for a size bound `Ho` on answers.
   [DISCRETISATION.md](../research/DISCRETISATION.md) shows that the paper's Algorithm S,
   run on `b`-bit choices, is such an estimator, and Lean checks it for a
   transcription of Algorithm S. `Digraph.cycle_fpras_of_algS` is the
   resulting end-to-end theorem. Its only hypothesis is `AlgSAccurate alpha`
   for every `alpha` in `(0,1)`: the exact Algorithm S, as transcribed, has
   relative error more than `alpha` with probability at most 1/8. The
   correspondence laws now include actual induced vertex/edge subtypes and
   a separately defined parent-pointer program, each equivalent in full
   output law to `algS`. Closure, fuel, pool invariants and uniform draws,
   first-open conditioning, and early stopping are also checked.

   `algS_inducedClosed` keeps the original sample budget and fuel and filters
   the original arc list. First-open ranks are the original indices restricted
   to surviving arcs; they need not be consecutive. A fresh canonical order
   on the subtype is not assumed to give the same law. The theorem holds for
   every sample budget, including zero. `parentAlgS_law` assumes `M > 0` and
   probabilities in `[0,1]`; it uses pool invariants on supported choices.
   Its state stores actual parent pointers, and the path test is relational
   reachability along those pointers, not an assumed Boolean label. These
   are mathematical program semantics, not a verified pointer-chasing implementation.

   The identification of the published pseudocode with this mathematical
   model still calls for review. In particular, the external
   martingale/concentration proof and the larger-budget variance argument
   transferring Theorem 9 to the unreduced budget are not formalized.
   Exact enumeration supplies separate finite evidence, as recorded in the note.
3. **The revised estimator and confidence proof.** Lean reaches arbitrary
   confidence by a median of `O(log(1/delta))` independent constant-confidence
   runs (`cycle_fpras_confidence`). The revised paper uses the same architecture
   for a different, corrected rejection estimator. Its cancellation identity,
   Bernoulli mean bound, and conditional sampler are not formalized. The
   original composed fair-bit bound includes both repetitions: `r*T*k` base
   oracle runs are accounted for in `concreteCycle_bitCost`.
4. **Simple-graph oracles.** Not needed for the cited theorem, which accepts
   multigraphs. The subdivision of parallel arcs described at the end of
   Section 4, for a hypothetical oracle restricted to simple graphs, is not
   formalised.
5. **Link to the Python model.** `scripts/cycle_fpras_reduction.py` follows the
   same algorithm but has not been proved equivalent to `cycleAlgorithm`.

Two modelling choices are worth knowing when reading the statements. Oracle
answers are real numbers and each call's seed law may depend on the query but
not on the history, which is what "fresh randomness" means here. And the
theorems are about the specific program `cycleAlgorithm`: `Prog` itself does
not restrict programs to computable ones, so the claim that the algorithm uses
only the graph, the input probabilities, oracle answers and random bits is
checked by reading its definition, not by a theorem.

## Trust and reproduction

Pinned toolchain: `leanprover/lean4:v4.35.0`.
Pinned mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Run `python3 scripts/check_formalization.py`; the report is written to
`validation/lean-verification.json`. This checks the actual theorem dependencies,
not just a text search. The Python model has a separate finite regression suite;
it has not been proved equivalent to the Lean definitions.
