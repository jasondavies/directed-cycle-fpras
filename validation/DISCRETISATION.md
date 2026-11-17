# Running the reliability oracle on random bits

This note closes the gap between the cost model of the cited reliability
theorem and the bit model used in [the manuscript](../paper/directed-cycle-fpras.pdf). All three steps
below are checked in Lean for a transcription of the paper's Algorithm S
(`DirectedCycleFPRAS/AlgorithmS.lean`, theorem `Digraph.algS_discretised`).
Lean also proves Algorithm S's accuracy bound: deferred-edge DFS laws and
snapshot splitting give the concrete conditional moments, and an absorbing
round process connects the martingale estimate to the returned value.
`Digraph.algS_accuracy` is the general relative-error theorem;
`algSAccurate` supplies the constant-confidence budget used here. Whole-program
subtype reindexing and explicit parent-pointer correspondence are checked too.
The [formalization map](FORMALIZATION.md#algorithm-s) gives the
proof dependencies.

The counting and conditional-sampling programs use this oracle at accuracy
`1/(16*(m+1))`, independent of their error targets. Their concrete Lean entry
points are `Digraph.cycleFPRAS` and `Digraph.cycleSampler`.

## The gap

Feng, Fu and Guo, *Approximating two-terminal network reliability*
(arXiv:2608.02523v2), count "unit-cost arithmetic operations and independent
draws of uniform random variables on (0, 1)". They give no bit-complexity
bound and no bound on the length of the output. The manuscript's reduction
needs an oracle that uses finitely many random bits, runs in time polynomial
in the binary input length, and returns a rational of polynomial length.

## Which algorithm

The paper contains two directed algorithms. The main one (Theorem 1, time
`O~(n m eps^-2)`) uses persistent data structures and a step cap. The simple
one, Algorithm S (Section 2.3, Theorem 9), is slower but has a fixed loop
structure. An FPRAS only needs some polynomial, so we discretise Algorithm S.

**Theorem 9 of the paper.** For a directed graph with
`n` vertices and `m` arcs satisfying the standing assumption, open
probabilities `p` in `(0,1]`, `s != t` and `eps, delta` in `(0,1)`,
Algorithm S with `M = ceil(2 n^3 m / (eps^2 delta))` performs
`O(n^4 m^2 / (eps^2 delta))` unit-cost operations and outputs an estimate
within a factor `1 +- eps` of `Rel(s,t)` with probability at least `1 - delta`.

Before Algorithm S the paper returns 1 if `s = t`, deletes the vertices
unreachable from `s`, and returns 0 if `t` was deleted. These steps are
deterministic graph searches.

## The discretised algorithm S'

Let the input probabilities be `p_e = a_e / b_e` with `L` bits each, and let
`B` be the product of all `b_e`, so `B <= 2^(m L)`. Algorithm S' is
Algorithm S with `delta = 1/8`, with all arithmetic done exactly on rationals,
and with every random action implemented by the `b`-bit cumulative-interval
rule: draw a uniform integer `U` in `[0, 2^b)` and select the alternative whose
cumulative-weight interval contains `U / 2^b`. The value of `b` is fixed below.

### Step 1: every random action is a finite choice with rational weights

Inspecting Algorithm S and Algorithm 2 (Generate), the random actions are:

| Action | Alternatives | Weights |
| --- | --- | --- |
| 1(a) choose a resolved vertex `u` | at most `n` | `qhat_u * gamma_u` |
| 1(b) draw a snapshot from the pool of `u` | at most `M` | uniform |
| 1(c) at `u`, choose the first open arc of the cut, as in the paper's cost accounting | at most `m` | `p_(e_j) * prod_(i<j) (1 - p_(e_i))` |
| 1(c) reveal the state of any other examined arc | 2 | `p_e`, `1 - p_e` |

Here `gamma_u = 1 - prod (1 - p_e)` over the cut arcs leaving `u`. A DFS run
examines each arc at most once, so one iteration of Generate makes at most
`m + 3` choices whose numbers of alternatives sum to at most `n + M + 3m`.
There are at most `n - 1` rounds of `M` iterations. Hence on every execution
the numbers of alternatives sum to at most

    N_alt = (n - 1) * M * (n + M + 3m).

No other randomness is used. In particular no real number is ever drawn: the
paper's "coin with a known bias" is exactly a two-alternative choice.

### Step 2: the effect of `b`-bit choices

A `b`-bit choice among `k` alternatives assigns each alternative a probability
within `2^-b` of its target (`bitLaw_error`), so its law is within `k / 2^b` in
L1 distance. Later choices depend on earlier outcomes, since the weights
`qhat_u` and the pools are random. The sequential coupling handles this: for
any program whose choices have at most `N` alternatives in total along every
path, replacing every exact choice by a `b`-bit draw changes the probability
of every event by at most `N / 2^b`. This is `Prog.exp_discretise_le` in
`DirectedCycleFPRAS/Discretise.lean`, proved for adaptive programs.

Take `b = ceil(log2(8 * N_alt))`. Then for every event,

    | Pr_S'[event] - Pr_S[event] | <= 1/8.

With Theorem 9 at `delta = 1/8`,

    Pr[ S' is not within 1 +- eps ] <= 1/8 + 1/8 = 1/4.

So S' meets the constant-confidence guarantee, with `b = O(log(n m / eps))`
and at most `(n - 1) * M * (m + 3) * b` random bits on every execution.

### Step 3: all numbers have polynomial length

- Every `gamma_u`, and every weight in action 1(c), is a multiple of `1/B`
  in `[0,1]`.
- `qhat_s = 1`. In round `r` the algorithm sets
  `qhat_v = Phihat * N / M` with `Phihat = sum_(u in R) qhat_u * gamma_u` and
  `0 <= N <= M`. By induction, after `r` rounds every `qhat` is a multiple of
  `1 / (M B)^r`: `Phihat` is a multiple of `1 / ((M B)^(r-1) * B)`, and
  dividing by `M` gives `1 / (M B)^r`.
- `qhat_v <= Phihat <= |R| * max qhat`, so after `r` rounds every `qhat` is at
  most `n^r`.

There are at most `n - 1` rounds. So every number the algorithm stores is a
fraction with denominator at most `(M B)^n` and numerator at most
`n^n (M B)^n`, that is, `O(n (m L + log(n m / eps)))` bits. The selection rule
compares `U * W` with `2^b * S` for partial sums `S` and total `W` of weights
(`hit_normLaw_iff`), which adds `b` bits. Choosing the maximising arc in
Step 2(a) is a comparison of such fractions.

Consequently:

- arithmetic operands have polynomial length. With stored cumulative weights
  and indexed pools, the written implementation has the polynomial bit bound
  in the manuscript's appendix. The generic executable selector has additional
  scans and is covered by the larger bound described below;
- the output is a fraction with numerator and denominator at most
  `Ho = n^n (M B)^n`.

### Conclusion

For rational `eps` in `(0,1)`, S' is a randomized algorithm that uses finitely
many fair random bits, runs in time polynomial in the binary input length and
`1/eps` on every execution, returns a rational of polynomial length, and is
within `1 +- eps` of `Rel(s,t)` with probability at least 3/4. It returns
exactly 0 when the reliability is 0.

This establishes the reliability contract used by the Lean reduction: S' is a
`ReliabilityEstimator` with a finite seed space, it satisfies
`ReliabilityEstimator.Correct eps`, and its answers satisfy the size bound
`Ho` used by `vertexAlgorithm_sat` and `concreteVertex_height`. With
`Digraph.cycleFPRAS_correct`, the reduction gives an FPRAS for
directed-cycle probability in the bit model.

## What is formalised

`DirectedCycleFPRAS/AlgorithmS.lean` defines `Digraph.algS`, a transcription
of Algorithm S and Generate as a program with exact discrete choices and no
oracle calls, and proves:

| Step | Lean theorem | Statement |
| --- | --- | --- |
| 1 | `algS_choiceBound` | Along every execution the alternatives sum to at most `n * M * ((n+1) + (M+1) + (m+1) + (n+1)*2m)`. |
| 2 | `Prog.exp_discretise_le` | Running on `b`-bit draws changes any probability by at most that number over `2^b`. |
| 3 | `algS_sat` | With input probabilities `a_e / b_e`, every possible output is a fraction with numerator and denominator at most `((n*m + 1) * M * B)^n`. |
| link | `algSEstimator_correct`, `Digraph.cycleFPRAS_correct` | The `b`-bit Algorithm S, as a randomized real with a finite seed space, meets the estimator contract; hence the counting and sampling theorems use the proved `algSAccurate` at `1/(16*(m+1))`, with no oracle-accuracy premise (an edgeless graph is handled without the oracle). `algSEstimator_height_total` gives the answer size including zero sample budgets. |
| all | `algS_discretised` | If the exact algorithm fails with probability at most 1/8, the `b`-bit version fails with probability at most 1/4, uses only uniform `b`-bit draws, and keeps the size bound. |

The following additional obligations are checked:

| Obligation | Lean theorem(s) | Scope |
| --- | --- | --- |
| Rational medians | `median_mem`, `median_height`, `Oracle.amplify_height` | Nonempty medians are sample values; both amplification stages preserve height. Empty medians return zero. |
| Complete program resources | `concreteVertex_law`, `concreteVertex_bitCost`, `concreteVertex_height`, `concreteVertexSample_bitCost` | Inlines the oracle and both amplifications; counts all fair bits and bounds every final output, including zero-budget cases. |
| Reachable-set restriction | `sDfs_closed`, `algS_restrict`, `algS_zero_unreachable` | Arbitrary probability changes outside a closed set containing the source preserve the full output law, at fixed `M` and with the ambient types retained. |
| Induced types | `orderedAlgS_canonical`, `algS_inducedClosed`, `algS_reachable_subtype` | Reindexes vertices and edges, retaining the original arc order, restricted first-open ranks, sample budget, and ambient fuel; preserves the full output law, including zero-budget cases. |
| Explicit parents | `ParentState.flags_discover`, `parentDfs_initial_law`, `parentAlgS_law`, `parentAlgS_inducedClosed` | Updates actual parent pointers and tests their paths; equality of full output laws for probabilities in `[0,1]` and `M > 0`, using valid pools on supported choices. `parentExplore_done` and `parentDfs_initial_fuel` justify finishing the traversal. |
| Fuel | `sDfs_initial_fuel`, `algS_round_fuel` | Extra fuel changes neither DFS from a valid snapshot nor the complete rounds program. |
| Pools | `initial_poolInvariant`, `PoolInvariant.update`, `sIter_records`, `sGenerate_records`, `sRounds_nonneg` | The invariants hold initially, are preserved in every continuing round, and ensure valid snapshots contain their starting/recorded vertex. |
| Uniform pool sampling | `poolDraw_expectation`, `poolDraw_perm` | Padded finite indices sample the list uniformly, respecting duplicates and invariant under permutation. |
| First-open sampling | `firstOpen_mass`, `firstOpen_mixture`, `firstOpen_normLaw_conditional` | Exact event weights and joint conditional law for the actual optional-edge choice when the conditioning mass is positive. The unnormalized factorization also covers zero-mass events. |
| Early stopping and flags | `sDfs_earlyStop`, `path_flag` | Record-then-finish and early-stop DFS have the same snapshot law; the Boolean path fold is true exactly when all nonroot path vertices avoid the resolved set. |

The Lean constants are cruder than the ones above: the DFS is charged `2m`
alternatives per popped vertex instead of using that each arc is examined
once, each weighted choice has one extra null alternative, and the numerator
bound does not use `gamma_u <= 1`. All remain polynomial.

The transcription differs from the paper's pseudocode in ways that do not
change the law of the output:

- the DFS stops when `v` is popped, since the record is determined then;
- loops are bounded by fuel: `n + 1` pops per DFS and `n` rounds;
- the pool draw is indexed by `Fin (M+1)` with weight on the valid indices;
- it covers Algorithm S proper. The paper first returns 1 if `s = t`,
  deletes the vertices unreachable from `s`, and returns 0 if `t` is deleted.
  The transcription returns 1 when `s = t` by itself, and the reduction only
  calls the oracle on instances of positive reliability, so `t` is never
  deleted. `algS_reachable_subtype` proves equality with the induced graph
  using its inherited order and the same sample budget and ambient fuel.

`ArithmeticBounds` also bounds the temporary branch weights, normalized
probabilities, cumulative sums, recorded products, and rejection calculations.
These bounds support the written polynomial-time analysis of rational
arithmetic and graph operations.

## Accuracy and correspondence

`Digraph.algS_accuracy` proves the relative-error bound on the ambient graph,
without deleting unreachable vertices. Its hypotheses are `M > 0`, input
probabilities in `[0,1]`, positive target reliability, positive accuracy, and
the sufficient budgets

```
2*n²*m ≤ M
2*n³*m ≤ delta*eps²*M.
```

`algSAccurate` instantiates these inequalities with
`M = ceil(16*n³*m/eps²)` and `delta = 1/8` for `0 < eps ≤ 1`.
The equal-terminal case returns exactly one, even when the sample budget is
zero. Unreachable vertices contribute zero to the normalized prediction sum,
so the proof does not require a separate transfer of accuracy to a larger
sample budget. `algSEstimator_correct` composes this theorem with rounding.

The subtype and parent-pointer theorems establish correspondence between
formal programs. `parentAlgS_inducedClosed` combines the full parent-pointer
program with induced-subtype restriction. The parent path is defined through
stored pointers; that program stores no Boolean eligibility flags. These
formal statements can be checked against the published pseudocode by reading
the definitions. Polynomial machine cost for rational arithmetic is a written
argument; the development has no machine-level time semantics.

### Executable Lean refinement

`RatProg` represents exact rational choices with explicit finite indices.
`RatProg.compile` replaces each choice by a bounded fair-bit draw;
`compile_error` proves a total error of at most `A/2^b`. The bit interpreter
consumes only the selected continuation, and its consumption bound includes
all inlined oracle calls. Rational and real choice orders need not coincide:
the coupling theorem compares each implementation to the same exact law.

The Algorithm S accuracy proof is parameterized by `ArcEnumeration`, a
complete duplicate-free edge list. `RationalAlgorithmS` supplies executable
rational DFS, pools, and rounds; `RationalAlgorithmSAccuracy` proves the
nominal and compiled accuracy guarantees for an explicitly supplied order.
The split-vertex callback retains zero-probability edges, since the accuracy
theorem already covers probabilities in `[0,1]`.

The executable graph searches and rejection arithmetic are connected to the
relational and real-valued definitions by refinement theorems. Rational lower
medians implement both amplification stages. The formalization map lists the
entry points, resource bounds, and verification scope.

### Executable comparisons

`scripts/algs_transcription/` contains a Python port of the Lean definitions
(`lean_port.py`) and a separately written port of the paper's pseudocode
(`paper_port.py`). Run `python3 scripts/algs_transcription/run.py 1,2,3` to compare
their exact output distributions for `M = 1, 2, 3` on eleven graphs with at most
five vertices and eight arcs. The cases cover parallel arcs, self-loops, arcs
into the source, unreachable vertices, probability one, equal terminals, and
unreachable targets. The script checks equality of the two laws and equality
of their means with brute-force reliability, writing
`validation/algs-transcription-results.json`. `python3 scripts/algs_transcription/extended_checks.py` additionally checks
pool ordering and literal enumeration, varies arc orders, and performs
Monte Carlo diagnostics at `M = 40`.

These comparisons are regression evidence. They are not a Python-to-Lean
refinement proof; Algorithm S's concentration guarantee comes from the Lean
proof above.

Not covered: the fast algorithm of Theorem 1. Its bit-model cost is not
analysed here, so the resulting running time for the cycle FPRAS is a
polynomial of higher degree than the unit-cost bounds suggest. That does not
affect the existence of the FPRAS.

## Operation counts of the executable

The sharp displayed runtime bounds in the manuscript apply to stored cumulative
weights and indexed pools, with a uniform pool index `floor(U*length/2^b)`.
The Lean executable instead uses `RatLaw.norm`, `searchUpper`, and `List.getD`.
Its pool choice has `M+1` alternatives. Each threshold recomputes a cumulative
sum, and a normalized weight can recompute its total. A full pool therefore
admits at least quadratic summand visits per draw. The threshold-count theorem
is not a bound on the work performed inside a threshold.

The appendix separately bounds direct evaluation of the supplied definitions
by `O(P^12 H^3)`, using numbered finite inputs and table representations.
Here `P` includes graph sizes, every loop budget, the global draw width, and
`execCountChoices` or `execSampleChoices`; `H` includes the checked rational
size bounds, draw width, and index lengths. Raw-weight scans, generic
normalization and selection, list access, graph guards, median selection,
and continuation overhead are all included. This deliberately loose bound is
polynomial in input length and the accuracy parameters. It is not the sharper
bound of the indexed implementation or a formal theorem about compiled Lean.
