# Formalisation scope

The project uses finite real-valued probability laws, finite sums and products,
and relational reachability. These are mathematical semantics; a finite sum
being executable by exhaustive enumeration does not make it polynomial-time.
All theorems below are checked by Lean. No `sorry`, project axioms, or native
computation oracle is used to obtain them.

**In one sentence:** Lean verifies the probabilistic correctness of the whole
oracle reduction, with explicit counts of samples, oracle calls, random bits
and charged local operations, and bounds on the size of every query and of the
output. There is no machine model, so "polynomial time" is assembled from
those bounds by a short written argument, and the reliability FPRAS itself is
a hypothesis.

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
| `Amplification` | The law of `k` independent seeds, a median defined by its characterising property, and `Oracle.amplify_failure`: per-call failure at most 1/4 becomes at most `(7/8)^k`. |
| `Confidence` | The median of `k` independent runs of a real-valued program fails with probability at most `(7/8)^k`; the reduction at confidence `1 - delta`. |
| `Resources` | Charged local-operation count, the invariant that every query is a feasible residual instance, a size calculus for fractions, the output size bound, and division-free selection. |
| `Reduction` | Two-terminal reliability, the support test, the witness queries, the complete algorithm `Digraph.cycleAlgorithm`, its call and bit budgets, and the reduction theorems below. |

The entry point `DirectedCycleFPRAS.lean` imports all modules. `AxiomAudit.lean`
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
| `Digraph.cycleAlgorithm_sat` | If the input probabilities are fractions with numerator and denominator at most `Hp` and the oracle's answers likewise at most `Ho`, then every query asked is a residual instance passing the support test, and the output is a fraction with numerator and denominator at most `(2*Hp*Ho)^m * n * m!`. |
| `Digraph.cycleAlgorithm_ideal` | If *every* answer to a valid query is `eps/(128 m (m+1))`-accurate (the oracle may still be randomized) and `(3m+1)/2^bits <= eps/(32 m)`, then `Pr[|Zhat - Z| > eps*Z] <= 1/(n (eps/(16 m))^2)`. |
| `Digraph.cycleAlgorithm_failure` | If instead each call on a valid query is inaccurate with probability at most `gamma`, the bound is the same plus `(m + 2*m*n) * gamma`. |
| `Digraph.cycle_fpras_reduction` | With `n = ceil(2048 m^2/eps^2)`, `bits = bitBudget m eps` and `(m + 2*m*n) * gamma <= 1/8`: failure probability at most 1/4. |
| `Digraph.cycle_fpras_of_constant_confidence` | If each call on a valid query is accurate with probability at least 3/4, then the algorithm run against the median of `6 * ceil(log2(8 T))` independent calls, `T = m + 2*m*n`, fails with probability at most 1/4. |
| `Digraph.cycle_fpras_confidence` | Under the same contract, the median of `6 * ceil(log2(ceil(1/delta)))` independent runs fails with probability at most `delta`, for every `delta > 0`. |
| `Digraph.cycleAlgorithm_of_cycleMass_eq_zero` | If `Z = 0` the algorithm is literally `ret 0`: no oracle call, no randomness, output exactly 0. |
| `Digraph.cycleAlgorithm_exactOracle` | The exact oracle meets the contract, so the hypotheses are satisfiable. |

All of them hold for `0 < eps <= 1`, arbitrary `p : E -> [0,1]`, loops and
parallel edges, and include the case `Z = 0`. `cycleAlgorithm_ideal` and
`cycleAlgorithm_failure` implicitly need `m >= 1` through their hypothesis on
`bits`; the later theorems treat the edgeless graph separately.
The oracle is constrained only on valid queries; on every other input it may
answer arbitrarily.

### How the written argument maps to Lean

| Written step (SOLUTION.md) | Lean |
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
| Section 4, choices need only rational comparisons | `hit_normLaw_iff` |

### Differences from the written parameters

The formal proof is a constant-confidence version with its own constants. The
differences are deliberate and do not affect polynomiality.

| Quantity | Written | Formal |
| --- | --- | --- |
| Concentration | Hoeffding, `log(1/delta)` | Chebyshev, failure 1/8, then a median of runs |
| Samples | `ceil(200 m^2 eps^-2 ceil(log2(4/delta)))` | `ceil(2048 m^2/eps^2)` |
| Oracle accuracy | `eps/(100 m (m+1))` | `eps/(128 m (m+1))` |
| Rounding of choices | separate failure budget `delta/4` by coupling | L1 error `(3m+1)/2^bits`, absorbed into the sampling-law budget |
| Oracle failure budget | `delta/(4T)` per call | `T * gamma <= 1/8`, with `gamma = (7/8)^k` after amplification |
| Range of `eps` | `(0, 1/2]` | `(0, 1]` |

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
     their total, not that each charge matches a real cost; this is the same
     trust as a `TimeM` tick in cslib. The initial cyclicity test of the
     support and the handful of arithmetic operations next to each guard or
     draw are not charged separately.
   - Each charged operation is a reachability test on the input graph or
     `O(1)` arithmetic operations and comparisons on fractions. That these
     take polynomial time in the operand sizes is standard and not formalised.
   - Size bounds are proved for the queries and the output. The intermediate
     branch weights and partial sums are sums and products of at most `m + 1`
     input probabilities and oracle answers, so the `Height` lemmas bound them
     the same way, but no theorem enumerates them.
   cslib has multi-tape Turing machines with time bounds; compiling this
   algorithm to one, with randomness and oracle access, would be a separate
   and much larger project.
2. **The external theorem.** The reliability FPRAS of Feng, Fu and Guo is a
   hypothesis: an `Oracle` that is accurate on valid queries with probability
   at least 3/4 at the single accuracy level the theorem names. Its existence,
   its cost as a function of that accuracy, and its internal randomness are
   outside this repository.
3. **The written route to confidence `1 - delta`.** Lean reaches arbitrary
   confidence by a median of `O(log(1/delta))` independent constant-confidence
   runs (`cycle_fpras_confidence`). The written proof instead uses Hoeffding
   inside a single run; that argument is not formalised. Counts of base oracle
   calls after amplification (queries times repetitions) are not stated as a
   theorem.
4. **Simple-graph oracles.** Queries are posed on the input multigraph with
   some probabilities set to 0 or 1. Deleting zero-probability edges,
   discarding loops and subdividing parallel arcs for an oracle that requires
   simple graphs (end of Section 4) are not formalised.
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
`sources/lean-verification.json`. This checks the actual theorem dependencies,
not just a text search. The Python model has a separate finite regression suite;
it has not been proved equivalent to the Lean definitions.
