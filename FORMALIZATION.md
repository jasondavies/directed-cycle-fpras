# Formalisation scope

The project uses finite real-valued probability laws, finite sums and products,
and relational reachability. These are mathematical semantics; a finite sum
being executable by exhaustive enumeration does not make it polynomial-time.
All theorems below are checked by Lean. No `sorry`, project axioms, or native
computation oracle is used to obtain them.

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

The entry point `DirectedCycleFPRAS.lean` imports all modules. `AxiomAudit.lean`
prints dependencies of the principal results, including the graph-specific
success theorem and the reliability identity.

## Strongest graph-specific statement

`Digraph.cycle_estimator_success` proves the probability bound described in
[README.md](README.md). Its approximation hypotheses are substantive:
it accepts a fixed weight estimate and a finite sampling law that is close to
the ideal mixture. It proves the estimator's guarantee from those hypotheses,
including concentration, rather than assuming that guarantee.

The graph product law and reliability factorisation are also proved. Thus the
formalisation is more than an abstract union-estimator identity, but less than
an end-to-end proof of an oracle FPRAS.

## Remaining work for the full reduction theorem

1. Implement the conditional edge-exposure sampler in the formal model and
   prove that exact residual reliability ratios reproduce the conditional
   product law. Connect the existing normalisation and sequential-stability
   lemmas to its approximate version, including impossible branches.
2. Model the randomized reliability oracle with fresh randomness on each call.
   Prove the good-oracle coupling for adaptively chosen queries and the outer
   mixture over shared random initial weight estimates. The current statistical
   theorem fixes those estimates; it does not silently condition on all real
   adaptive calls succeeding.
3. Verify the bounded-random-bit implementation, including rounding errors,
   fallback behavior, rational encodings, output lengths, and worst-case work.
   Also connect the support-acyclicity test to the zero-probability branch.
4. Establish a formal algorithmic implication: given an implementation of a
   directed-reliability FPRAS with its stated guarantees, construct a cycle
   FPRAS. The external theorem should be an explicit hypothesis of that result.
   Proving that external theorem itself is outside this repository's contribution.

Confidence amplification to arbitrary delta is in the written solution. The
formal statistical theorem uses Chebyshev and a constant-success budget instead
of formalising the written Hoeffding/logarithmic-confidence argument. This is
sufficient for the usual 3/4-success specification once the missing algorithmic
layers are verified.

## Trust and reproduction

Pinned toolchain: `leanprover/lean4:v4.35.0`.
Pinned mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Run `python3 scripts/check_formalization.py`; the report is written to
`sources/lean-verification.json`. This checks the actual theorem dependencies,
not just a text search. The Python model has a separate finite regression suite;
it has not been proved equivalent to the Lean definitions.
