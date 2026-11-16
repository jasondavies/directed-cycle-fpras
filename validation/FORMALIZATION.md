# Formalization map

The Lean development follows the paper's vertex-witness corrected rejection
algorithm. Its entry point is [DirectedCycleFPRAS.lean](../DirectedCycleFPRAS.lean).
It uses finite real-valued laws, finite sums, and relational reachability.
Those are mathematical semantics: exhaustive evaluation of a finite sum is
not asserted to be an efficient implementation.

## Main statements

| Paper result | Lean declaration | Source |
| --- | --- | --- |
| Counting with all budgets fixed | `Digraph.cycleFPRAS_correct` | [Parameters](../DirectedCycleFPRAS/Parameters.lean) |
| Sampling conditioned on cyclicity | `Digraph.cycleSampler_cyclic_correct` | [Parameters](../DirectedCycleFPRAS/Parameters.lean) |
| Exact zero detection | `Digraph.vertexAlgorithm_zero` | [VertexAlgorithm](../DirectedCycleFPRAS/VertexAlgorithm.lean) |
| Counting fair-bit budget | `Digraph.concreteVertex_bitCost` | [ConcreteVertex](../DirectedCycleFPRAS/ConcreteVertex.lean) |
| Sampling fair-bit budget | `Digraph.concreteVertexSample_bitCost` | [VertexSampling](../DirectedCycleFPRAS/VertexSampling.lean) |
| Counting output size and residual queries | `Digraph.concreteVertex_height`, `Digraph.vertexAlgorithm_sat` | [RejectionHeight](../DirectedCycleFPRAS/RejectionHeight.lean) |
| Acyclicity/independent-set probability identity | `AcyclicityReduction.edge_retention_probability` | [AcyclicityReduction](../DirectedCycleFPRAS/AcyclicityReduction.lean) |

Algorithm S accuracy is proved by **`algSAccurate`** for `0 < α ≤ 1`.
`algSEstimator_correct` establishes the finite-bit reliability contract; the
counting and sampling theorems instantiate it at
`rejectionAccuracy m = 1/(16*(m+1))`. They have no oracle-accuracy premise.
The external independent-set inapproximability theorem is cited in the paper;
Lean proves the exact reduction to its counting problem.

## Reduction and probability proofs

| Modules | Checked content |
| --- | --- |
| `GraphWitness`, `GraphProbability`, `ProductLaw`, `Reliability` | Directed graphs with edge identities; independent retention; residual pinning; conditional product laws; reliability and exact support tests. |
| `VertexWitness` | Splitting a vertex preserves edge identities and makes cycle membership a reachability event. A feedback set of the positive support covers all positive-mass cyclic configurations. Its union mass equals the cycle probability. |
| `WitnessMixture`, `FiniteLaw`, `IndependentSamples`, `BoundedScores` | Finite measures and overlap bounds `Z ≤ W ≤ kZ`; product laws for independent samples; variance additivity; `Var(Y) ≤ E(Y)` for `0 ≤ Y ≤ 1`; the `64k/eps²` Chebyshev bound. |
| `ProposalLaws`, `RecordedExposure` | Supported-execution invariants, relative-error normalization, recorded nominal branch products, feasible support, inverse-probability cancellation, and the multiplicative likelihood envelope. |
| `CorrectedRejection`, `RecordedRejection` | Clipped, total rejection rule; exact accepted subdistribution `mu(x)/(2*W_hat)`; a proved envelope at oracle accuracy `1/(16*(m+1))`. |
| `RejectionCounting`, `WitnessAlgorithm` | Conditional counting accuracy and its composition with random initial witness estimates. |
| `RejectionSampling`, `WitnessSampling` | First acceptance with a fixed cap; exact mixture of the conditional law and timeout fallback; exponential timeout bound; composition with random initial weights. |
| `VertexAlgorithm`, `VertexSampling`, `ConcreteVertex`, `Parameters` | Instantiation with vertex witnesses, exact zero handling, finite-bit counting and sampling, oracle amplification, and expanded Algorithm S programs with concrete parameter choices. |
| `AcyclicityReduction` | Fair vertex gates and deterministic connectors; acyclicity iff the selected vertices are independent; probability exactly `#IS/2^n` in the independent edge-retention model. |

`recordedExpose_inverse` cancels the nominal branch probability at each choice
**before** summing over fresh oracle seeds. It therefore covers adaptive oracle
transcripts; it does not assume that the recorded product is the marginal
proposal probability. `recordedExpose_envelope` and `rejectionAccuracy_envelope`
prove that clipping the acceptance probability does not change accurate runs.

The sampling guarantee is stated for every test function taking values in
`[0,1]`. In particular, it bounds every event-probability difference, which is
the total-variation guarantee on the finite output space. Under a feedback
cover, `vertex_conditional_expectation` identifies the target with the
independent-edge law conditioned on cyclicity. The timeout fallback is the
entire positive support.

## Programs and resources

`Prog` has return, oracle-query, finite-choice, and charged-work constructors.
Its `Oracle` supplies a fresh finite seed on each query. `Prog.exp` gives
expectation semantics, while `Prog.inline` replaces queries by call-free
programs and preserves those semantics.

- `Prog.exp_le_repair` and `Prog.exp_repair_abs` compare actual and repaired
  oracles without conditioning on universal oracle success.
- `Prog.exp_discretise_le` bounds the effect of replacing choices by uniform
  `b`-bit draws by `A/2^b`, where `A` bounds the sum of alternatives along a path.
  Recorded proposal probabilities remain nominal and unrounded.
- `Prog.finiteBit_failure` and `Prog.finiteBit_error` compose the two couplings.
- `Oracle.amplify_failure` and `Prog.medianOf_failure` give failure at most
  `(7/8)^r` after `r` repetitions. `confidenceRuns δ` supplies a logarithmic
  repetition count.

For `D` proposals, `k` witnesses and `m` edges, the reduction uses

```
T = k + 2*m*D                   amplified reliability queries
A = D*(k + 2*m + 2)             alternatives across finite choices
```

Counting takes `D = ceil(64*k/eps²)`, gives each coupling budget `1/16`, and
uses `confidenceRuns δ` outer repetitions. Sampling takes
`D = 4*k*ceil(log2(3/eta))` and gives timeout and both couplings budget `eta/3`.
`choiceWidth` and `oracleRepetitions` implement the corresponding logarithmic
precision and amplification budgets, with checked inequalities.

For a base reliability program with uniform fair-bit budget `C`, inner count
`h`, and choice width `b`, one complete run costs at most `b*A + T*h*C` bits.
Counting multiplies this by the outer repetition count. `oracleBitBudget`
supplies `C` uniformly over all possible positive-edge subtypes of a split
query, including degenerate cases.

`Height H x` means that `x` has a signed numerator and positive denominator,
both bounded in magnitude by `H`. If each oracle answer has height `H_o`,
the counting output has height at most

```
countHeight k D H_o = 2*(2*H_o)^k * max(1,D).
```

This uses the integer acceptance count; it does not sum unrelated rational
importance weights. `concreteVertex_height` substitutes the proved Algorithm S
answer bound `oracleHeight` and applies to the same expanded program as the
accuracy and fair-bit theorems, including failed-oracle histories.

The written bit analysis covers temporary rational arithmetic, graph operations,
and their machine cost. Lean verifies the stated resource predicates and output
size; it does not provide a machine-level running-time semantics.

## Algorithm S

| Modules | Checked content |
| --- | --- |
| `PositiveOracle` | Delete zero-probability edges without changing reliability. |
| `AlgorithmS`, `AlgorithmSEstimator`, `AlgorithmSOracle` | Exact transcription; finite-bit choices; common-denominator bounds; finite seed representation; transfer of exact accuracy to the finite-bit estimator; total answer-size and fair-bit bounds. |
| `AlgorithmSInvariants`, `AlgorithmSStopping` | Stack potential, sufficient DFS and round fuel, closed-set exploration, path flags, early stopping, and finishing traversal. |
| `FirstOpen`, `AlgorithmSPools` | First-open conditional product law, pool positivity and membership, indexed sampling with multiplicities, and permutation invariance. |
| `AlgorithmSRestriction`, `AlgorithmSOrdered`, `ReindexLaw`, `AlgorithmSSubtypes` | Closed-set invariance and full output-law equality on induced vertex/edge subtypes, with inherited ordering, sample budget, and ambient fuel. |
| `AlgorithmSParents`, `AlgorithmSParentProgram` | Explicit parent paths and a separate parent-pointer program; equality of the complete output law; composition with induced-subtype restriction. |
| `HarrisReliability`, `AlgorithmSOutflow` | Harris's inequality (FFG Lemma 4), `Rel(s,v)*Rel(v,w) ≤ Rel(s,w)`, the arc-extension bound, and Lemma 8 for the concrete first-open weights and argmax rule. |
| `AlgorithmSKernel`, `AlgorithmSMoments` | Exact weighted proposal law, including zero cut mass; equality of Generate's scored output law with independent sums; exact means and variances; cancellation of the empirical pool size, including empty pools. |
| `AlgorithmSPrediction` | DFS reach scores and empirical predictions; resolved predictions equal stored estimates; the expectation of the actual Generate/update pair; the algebraic update formula used by the unbiasedness proof. |
| `PredictionMartingale` | Local bounded-record variance calculation; finite-program martingale second moments and relative-error tail; `algSSamples` satisfies the numerical bounds using ambient graph counts. Its generic iteration bounds are instantiated by `AlgorithmSAccuracy`. |
| `ProgramComposition`, `Resources` | Inlining, median properties, fair-bit composition, resource invariants, and rational height arithmetic. |
| `DeferredEdges`, `AlgorithmSDeferred` | Adaptive read-once exposure has the product law; the actual DFS satisfies the read-once invariant; restarting at a recorded snapshot uses fresh edges. |
| `AlgorithmSSearch`, `AlgorithmSReach` | Deterministic search completeness and soundness; initial prediction equals reliability; restarted scores obey the Harris reliability-ratio bound. |
| `AlgorithmSFlags`, `AlgorithmSSnapshot`, `AlgorithmSSplit`, `AlgorithmSUnbiased` | Flag linearity, snapshot decomposition, FFG equation (8), and unbiasedness of the concrete update (Lemma 10). |
| `AlgorithmSVariance` | Concrete one-round prediction variance (Lemma 11) and the two normalized second-moment bounds, including zero-reliability vertices. |
| `AlgorithmSTerminal`, `AlgorithmSRounds` | Zero-outflow exits, supported-state invariants, absorbing rounds, and equality of the complete output law with the terminal prediction. |
| `AlgorithmSAccuracy` | Theorem 9 for the actual program, sufficient ambient sample budgets, and finite-bit estimator correctness. |

The proof of Theorem 9 follows this chain:

1. `sDfs_deferred` and `sDfs_restart_deferred` identify adaptive DFS with a
   single independently retained graph, including forced first-open edges.
   `reachScore_initial` identifies the initial score with reliability.
2. `reachScore_split` proves FFG equation (8). The weighted proposal identity
   then yields `prediction_generate_unbiased`; the concrete score bound
   yields `prediction_generate_variance` and its normalized consequences.
3. `roundStep_mean` and `roundStep_variance` apply these identities to every
   supported round, with stopping states absorbing. `algS_steps_law` identifies
   the actual returned estimate with the final prediction.
4. `algS_accuracy` applies the finite-program martingale estimate and
   Chebyshev's inequality. With `M > 0`, positive target reliability,
   `2*n²*m ≤ M`, and `2*n³*m ≤ δ*α²*M`, it proves relative-error failure at
   most `δ`. The proof works directly on the ambient graph: zero-reliability
   vertices contribute zero to the normalized prediction sum.
5. `algSAccurate` supplies `M = ceil(16*n³*m/α²)` and failure `1/8`, handling
   equal terminals separately. `algSEstimator_correct` adds the finite-bit
   coupling error and proves the estimator contract with failure `1/4`.

`algS_inducedClosed`, `algS_reachable_subtype`, `parentAlgS_law`, and
`parentAlgS_inducedClosed` additionally check the structural correspondence
with reachable-set restriction and explicit parent pointers. The
[oracle note](../research/DISCRETISATION.md) explains the bit implementation
and its relation to the published pseudocode.

## Audit and reproduction

Run `bash scripts/check.sh` to build the library, audit the declarations in
[Axioms.lean](Axioms.lean), and regenerate the finite-check reports. The audit
allows only `propext`, `Classical.choice`, and `Quot.sound`; it also rejects proof
admissions and project-defined axioms throughout the source tree.

Python models provide exact finite regression checks, including randomized
oracle transcripts and two Algorithm S ports. There is no Python-to-Lean
refinement proof. Algorithm S accuracy follows from the Lean proofs;
machine-level runtime follows from the written arithmetic analysis.
