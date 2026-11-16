# Running the reliability oracle on random bits

This note closes the gap between the cost model of the cited reliability
theorem and the bit model used in [SOLUTION.md](SOLUTION.md). All three steps
below are checked in Lean for a transcription of the paper's Algorithm S
(`DirectedCycleFPRAS/AlgorithmS.lean`, theorem `Digraph.algS_discretised`).
Lean also checks the correspondence lemmas listed below. A complete
equivalence to the paper's pseudocode and the paper's Theorem 9 remain
outside Lean; accuracy is an explicit hypothesis.

## The gap

Feng, Fu and Guo, *Approximating two-terminal network reliability*
(arXiv:2608.02523v2), count "unit-cost arithmetic operations and independent
draws of uniform random variables on (0, 1)". They give no bit-complexity
bound and no bound on the length of the output. The reduction in SOLUTION.md
needs an oracle that uses finitely many random bits, runs in time polynomial
in the binary input length, and returns a rational of polynomial length.

## Which algorithm

The paper contains two directed algorithms. The main one (Theorem 1, time
`O~(n m eps^-2)`) uses persistent data structures and a step cap. The simple
one, Algorithm S (Section 2.3, Theorem 9), is slower but has a fixed loop
structure. An FPRAS only needs some polynomial, so we discretise Algorithm S.

**Theorem 9 of the paper (used as a black box).** For a directed graph with
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

- every arithmetic operation is on integers of polynomial length, so the
  `O(n^4 m^2 / eps^2)` unit-cost operations of Theorem 9 cost polynomial time
  in the bit model, on every execution;
- the output is a fraction with numerator and denominator at most
  `Ho = n^n (M B)^n`.

### Conclusion

For rational `eps` in `(0,1)`, S' is a randomized algorithm that uses finitely
many fair random bits, runs in time polynomial in the binary input length and
`1/eps` on every execution, returns a rational of polynomial length, and is
within `1 +- eps` of `Rel(s,t)` with probability at least 3/4. It returns
exactly 0 when the reliability is 0.

This is exactly the hypothesis of the Lean reduction: S' is a
`ReliabilityEstimator` with a finite seed space, it satisfies
`ReliabilityEstimator.Correct eps`, and its answers satisfy the size bound
`Ho` assumed by `cycleAlgorithm_sat` and `cycleAlgorithm_weightSat`. With
`Digraph.cycle_fpras_of_estimator`, the reduction then gives an FPRAS for
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
| link | `algSEstimator_correct`, `Digraph.cycle_fpras_of_algS` | The `b`-bit Algorithm S, as a randomized real with a finite seed space, meets the estimator contract; hence the cycle reduction holds with `AlgSAccurate alpha` for all `alpha` in `(0,1)` as its only hypothesis (an edgeless graph is handled without the oracle). `algSEstimator_height_total` gives the answer size including zero sample budgets. |
| all | `algS_discretised` | If the exact algorithm fails with probability at most 1/8, the `b`-bit version fails with probability at most 1/4, uses only uniform `b`-bit draws, and keeps the size bound. |

The following additional obligations are checked:

| Obligation | Lean theorem(s) | Scope |
| --- | --- | --- |
| Rational medians | `median_mem`, `median_height`, `Oracle.amplify_height` | Nonempty medians are sample values; both amplification stages preserve height. Empty medians return zero. |
| Complete program resources | `concreteCycle_law`, `concreteCycle_bitCost`, `concreteCycle_height_total`, `cycleFPRAS_spec` | Inlines the oracle and both amplifications; counts all fair bits and bounds every final output, including zero-budget cases. |
| Reachable-set restriction | `sDfs_closed`, `algS_restrict`, `algS_zero_unreachable` | Arbitrary probability changes outside a closed set containing the source preserve the full output law, at fixed `M` and with the ambient types retained. |
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
  deleted. The deletion of unreachable vertices is not transcribed; see the
  next section.

Size bounds are proved for the estimates and the output. That each
arithmetic operation on such numbers takes polynomial time is not formalised,
as there is no machine model.

## What this rests on

1. **Theorem 9 of the paper**, as the hypothesis `AlgSAccurate` about the
   transcription. The external martingale proof is used as a cited result,
   not re-proved here. `AlgSAccurate` is slightly
   stronger than Theorem 9 as stated: it is asserted for every instance with
   probabilities in `(0,1]` and positive reliability, without first deleting
   the vertices unreachable from `s`, and with `M` computed from the
   unreduced `n` and `m`. Algorithm S never resolves or discovers an
   unreachable vertex, so its run on the unreduced graph is its run on the
   reduced graph with a larger `M`, and the proof of Theorem 9 only uses a
   lower bound on `M`: its last step is `Var <= (2 n^3 m / M) q_t^2`. This
   larger-budget justification remains written. The closed-set and
   unreachable-edge invariance parts are formalized, while actual
   reindexing to induced vertex/edge subtypes with an inherited arc order
   remains written; Lemma 5 in the
   [research manuscript](../paper/directed-cycle-fpras.pdf) gives the restriction argument.
   `AlgSAccurate alpha` is false for `alpha <= 0`: at zero the sample budget
   is zero and a positive-reliability instance with distinct terminals
   returns zero; at negative accuracy the allowed absolute error is negative.
   Thus the end-to-end
   theorem assumes it only for `alpha` in `(0,1)`, the paper's range.
   `AlgSAccurate` also includes `s = t` and `n = 1`, where the output is
   exactly 1.
2. **Fidelity of the transcription** to the paper's pseudocode. The table
   above records the checked supporting lemmas. There is not yet a single
   equivalence theorem to an independently formalized paper algorithm:
   subtype reindexing and the link to an explicit parent-pointer traversal
   remain written. Code review and exact finite comparisons provide
   additional evidence; they do not establish general equivalence or replace
   independent expert review.

   *Test.* `scripts/algs_transcription/` holds a Python port of the Lean
   definitions (`lean_port.py`) and a separately written port of the paper's
   pseudocode (`paper_port.py`). From the repository root,
   `python3 scripts/algs_transcription/run.py 1,2,3` computes, in exact
   rational arithmetic, the full output distribution of each for `M = 1, 2,
   3` on eleven graphs with at most 5 vertices and 8 arcs (parallel arcs,
   self-loops, arcs into `s`, unreachable vertices, probabilities equal to
   1, `s = t`, unreachable `t`). On every instance the two distributions are
   equal and the mean equals the reliability computed by brute force. The
   script exits nonzero on a mismatch and records its results in
   `validation/algs-transcription-results.json`. Equal-terminal and
   unreachable-target cases are checked against the paper's preprocessing.
   `run2.py` repeats this under random arc orders and adds a Monte Carlo run at `M = 40`. The ports are faithful
   to their sources by reading only, and the test says nothing about
   concentration at the real `M`.
3. **Polynomial cost of rational arithmetic** on numbers of the proved size.

Not covered: the fast algorithm of Theorem 1. Its bit-model cost is not
analysed here, so the resulting running time for the cycle FPRAS is a
polynomial of higher degree than the unit-cost bounds suggest. That does not
affect the existence of the FPRAS.
