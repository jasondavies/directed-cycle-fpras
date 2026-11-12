# An FPRAS reduction for directed-cycle probability

This is the written mathematical solution. The Lean development checks the
probabilistic correctness of the reduction at constant confidence, with the
exact boundary in [FORMALIZATION.md](FORMALIZATION.md), together with the
resource counts and size bounds behind Section 4. A machine-level running
time is a written argument only.

The external ingredient is the general directed two-terminal reliability FPRAS
of Weiming Feng, Yucheng Fu, and Heng Guo,
[*Approximating two-terminal network reliability*](https://arxiv.org/abs/2608.02523).
The original local proof used v1 (2026-08-03); v2 (2026-11-03) retains that
existence theorem and gives a different, faster algorithm. Neither version's
algorithm is implemented or formalised in this repository.

The union estimator is the standard witness-mixture/inverse-multiplicity
method. The proposed contribution is its application to directed cycles via
edge-return-path witnesses and a reliability-oracle self-reduction. We do not
claim that the general union-estimation technique is new.

## Caveat on the computational model

Read against the PDF of arXiv:2608.02523v2 on 2026-11-12. Its FPRAS
definition takes rational open probabilities in (0,1] on directed graphs with
parallel arcs and self-loops allowed, and success probability 3/4 (Remark 16
raises this by a median). But its running-time bounds, including Theorem 1,
"count unit-cost arithmetic operations and independent draws of uniform
random variables on (0, 1)", with taking the integer part of a number as a
unit-cost operation. The paper states no bit-complexity bound and no bound on
the length of the output for the directed algorithm.

The theorem below is stated for binary input length, and Section 4 assumes
"an oracle with polynomial worst-case bit complexity" returning
polynomial-length numbers. The cited theorem does not supply that as stated.
Until this is settled, the result established here is an FPRAS **in the same
unit-cost model with real uniform draws**. A bit-model FPRAS needs one more
argument: that the oracle can be run with finitely many random bits and
bounded-precision arithmetic while keeping its guarantee. That is plausible,
since its coins are comparisons of a uniform variable with a known bias, but
it is not proved in the paper or here.

The Lean development is unaffected in what it proves, but note that its
oracle model uses a finite seed space per call and its size theorems assume a
bound on the oracle's answers. Both correspond to the discretised oracle, not
to the paper's algorithm as literally stated.

## Theorem

Given a finite directed graph G with m edges, independent rational retention
probabilities p_e in [0,1], and rational parameters 0<epsilon<=1/2 and
0<delta<1/2, there is a randomized algorithm returning Z_hat such that

    Pr[|Z_hat-Z| <= epsilon Z] >= 1-delta,
    Z = Pr[the retained graph contains a directed cycle].

Its worst-case running time is polynomial in the binary input length,
1/epsilon, and log(1/delta). If Z=0 it returns zero exactly. Self-loops and
parallel edges are permitted. No complexity conjecture is assumed.

We prove an approximation-preserving reduction to directed reliability and
then apply the cited theorem. For parameters outside the stated ranges,
replace them by smaller fixed admissible values if necessary.

## 1. A polynomial family of cycle witnesses

Let mu be the product distribution on edge sets. For each edge e=(u,v), set

    A_e = {e is present and v reaches u without using e},
    w_e = Pr(A_e) = p_e Rel_(G-e)(v,u).

A zero-length return path is allowed when u=v. Thus a loop witnesses itself.
Every cycle supplies a witness; every witness supplies a cycle. In particular,

    {X is cyclic} = union_e A_e.

The number of witness events is m, even when the graph has exponentially
many cycles. For a sampled edge set X, define

    t(X) = |{e : X belongs to A_e}|,
    W = sum_e w_e.

All the memberships, and hence t(X), are computable by polynomially many
reachability tests. When Z>0,

    Z <= W <= mZ.

Choose e with probability w_e/W and sample X according to mu conditioned
on A_e. The resulting mixture distribution q satisfies

    q(X) = t(X) mu(X)/W.

Consequently the score Y=1/t(X), which is in [1/m,1], has expectation

    theta = E_q[Y] = Z/W >= 1/m.

Estimating this expectation and multiplying by W avoids sampling an
exponentially rare cyclic graph directly from mu.

## 2. Reliability estimates provide the required conditional sampler

To condition on A_e, fix e present, remove it from the return-path instance,
and expose the other edge bits sequentially, conditioned on v reaching u.
For an unexposed edge f with original retention probability p_f, let R_b
be the residual reliability when its bit is fixed to b. Previous decisions
are represented by deleting edges or setting their probabilities to one.
The next bit has conditional weights

    b_0 = (1-p_f)R_0,    b_1 = p_f R_1.

Reachability in the positive-probability support decides exactly whether
each branch has positive mass. Impossible branches receive weight zero
without calling the approximation oracle. A feasible prefix has at least
one feasible branch. Probabilities zero and one require no random choice.

Suppose every positive reliability estimate is within relative error alpha,
where alpha<=1/2. Normalizing the estimates changes a positive branch
probability by a multiplicative factor between

    (1-alpha)/(1+alpha) and (1+alpha)/(1-alpha).

In particular, its total-variation error is at most 4 alpha. Coupling at
each of at most m exposures gives conditional-sampling error at most
4m alpha. Estimating the initial w_e similarly changes witness selection
by at most 4 alpha. The approximate mixture is therefore within

    eta = 4(m+1)alpha

of q in total variation. For any score in [0,1], its expectation changes
by at most eta. This remains true when individual oracle estimates are
random: average the bound over their random choices, using fresh oracle
randomness for every new sample.

## 3. Accuracy, confidence, and adaptive oracle queries

If the support is acyclic, return zero. Otherwise m>=1 and Z>0. Set

    alpha = epsilon / (100m(m+1)),
    N = ceil(200m^2 epsilon^(-2) ceil(log_2(4/delta))),
    T = m + 2mN.

Estimate all witness weights, let W_hat be their sum, generate N samples
using the approximate mixture, and output

    Z_hat = W_hat * (sum_(j=1)^N 1/t(X_j))/N.

First analyze a fictitious oracle that always gives alpha-accurate answers.
Conditional on the initial weight estimates, sampling runs are independent.
Their common expected score differs from theta by at most
eta=epsilon/(25m). Hoeffding's inequality gives

    Pr[|sample mean - its expectation| > epsilon/(10m)]
      <= 2 exp(-2N epsilon^2/(100m^2)) <= delta/4.

Because theta>=1/m, the combined relative error in the score mean is at
most (1/25+1/10)epsilon < epsilon/4. Also
|W_hat/W-1|<=alpha<=epsilon/200. Multiplying the two estimates gives relative
error at most

    epsilon/4 + epsilon/200 + epsilon^2/800 < epsilon.

There are at most T reliability calls, including adaptive residual instances.
Amplify each call by independent repetition and a median to failure probability
delta/(4T). For analysis only, replace every inaccurate answer by the exact
answer. This defines the fictitious oracle just analyzed. On every history,
the next query is a fixed input to a fresh randomized oracle, so its failure
probability is still at most delta/(4T). Couple real and fictitious runs until
their first differing answer. A union bound makes the probability of such a
difference at most delta/4.

This argument does **not** assume independence after conditioning on all
adaptive oracle calls succeeding. That conditioning would be unjustified.
Independence is used only between fictitious sampling runs conditional on
their shared initial estimates.

## 4. A fixed random-bit budget and polynomial bit complexity

Each discrete choice has rational weights. For k alternatives, draw a
uniform b-bit integer U and place U/2^b in their cumulative probability
intervals. Each interval's assigned mass differs from its exact mass by
at most 2^(-b), giving total-variation error at most k/2^b.

There is one choice among at most m witnesses and at most m binary choices
per sample. Across N samples the sum of these errors is at most
3Nm/2^b. Choose

    b = ceil(log_2(12Nm/delta)).

Sequential coupling then bounds any departure from the exact-discrete-choice
algorithm by delta/4. Together with the preceding two failure budgets, total
failure is at most 3delta/4, which is less than delta.

An oracle with polynomial worst-case bit complexity returns polynomial-length
numbers. The branch weights, their normalizations, and the sum of m witness
weights therefore have polynomial bit length. The score sum also does:
its denominators divide lcm(1,...,m), whose bit length is at most
log_2(m!)=O(m log m). Its numerator adds only O(log N) further bits.
The parameters 1/alpha, N, and T are polynomial in m and 1/epsilon,
times a polynomial in log(1/delta). Median amplification costs only
O(log(T/delta)) repetitions.

Residual reliability instances retain the original probabilities or use
zero and one; their binary descriptions do not grow. Delete zero-probability
edges before invoking the external theorem. Loops can be discarded in a
reachability query, and s=t is handled exactly. If a simple-graph oracle is
required, subdivide each parallel arc through a distinct new vertex, putting
its original probability on one half and probability one on the other.
This preserves independence and reliability with only polynomial growth.

Thus all computation, random bits, and oracle calls have a polynomial
worst-case bound. In particular, no bound depends polynomially on 1/Z.
Applying the reliability theorem proves the stated FPRAS. **QED.**


## Formalisation and executable model

Lean verifies a constant-confidence version of Sections 1 to 3 and the
rounding estimate of Section 4, as one theorem about an explicit oracle
program (`Digraph.cycle_fpras_of_constant_confidence`). Its constants differ
from those above: Chebyshev replaces Hoeffding, with
`N = ceil(2048*m^2/epsilon^2)` samples; the oracle accuracy is
`alpha = epsilon/(128*m*(m+1))`; the rounding error of the `b`-bit choices is
added to the total-variation budget of the sampling law instead of being
charged to a separate failure event; and each query is answered by the median
of `6*ceil(log2(8T))` oracle calls that are individually accurate with
probability 3/4. The coupling with the fictitious oracle is formalised exactly
as described: no conditioning on the success of all calls.

Confidence `1-delta` is obtained in Lean by a median of `O(log(1/delta))`
independent runs (`Digraph.cycle_fpras_confidence`), not by the Hoeffding
argument above. The sampler exposes every edge, including the already fixed
witness edge, which costs nothing in the bound `T`.

For Section 4, Lean proves the counts of oracle calls, random bits and
charged local operations, that every query is a residual instance, and that
the output has numerator and denominator at most `(2*Hp*Ho)^m * N * m!` when
the input probabilities and oracle answers have them at most `Hp` and `Ho`.
There is no machine model: that each charged operation costs polynomial time
is not formalised, and the charges themselves are annotations.

Lean also proves that deleting zero-probability edges preserves reliability,
and states the final theorem for an estimator on multigraphs with
probabilities in `(0,1]` (`Digraph.cycle_fpras_of_estimator`). That is the
input class of the cited Theorem 1 in v2, which allows parallel arcs and
self-loops, so the subdivision step of Section 4 is not needed for it. The
cited running time is in a unit-cost arithmetic model; the bit-complexity
assumption on the oracle at the start of Section 4's last part is an extra
requirement, not something that statement provides.

Not formalised: a machine-level running time and the Hoeffding argument. The
reliability theorem of Feng, Fu, and Guo enters only as a hypothesis on the
oracle. [FORMALIZATION.md](FORMALIZATION.md) maps each step to its Lean
statement.

The executable model is in `scripts/cycle_fpras_reduction.py`. Its tests use
an exponential exact reliability oracle and bounded-error variants. Those
finite tests do not prove the polynomial-time reliability theorem or link the
Python implementation to the Lean definitions.

## Provenance

Extracted from entry a3nm-012 of the local `open-problems` research log.
The written reduction was developed on 2026-10-25; this separate repository
and its Lean development were created on 2026-11-12. Independent correctness
review and novelty assessment remain pending.
