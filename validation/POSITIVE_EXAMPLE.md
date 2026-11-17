# Positive execution examples

`PositiveExample.lean` evaluates positive instances using rational arithmetic
and explicit bit tapes. Run it from the repository root after `lake build`:

```sh
lake env lean --run validation/PositiveExample.lean oracle
```

The graph is one arc from vertex 0 to vertex 1, retained with probability 1/2.
The sample budget is Theorem 9's `16*n^3*m/alpha^2` with `n=2`, `m=1`, and
`alpha=1/2`, hence `M=512`. The choice width is
`ceil(log2(8*algSChoices 2 1 512)) = 23`. On the all-zero tape this run returns
`1/2` and consumes 35,328 bits. It exercises Algorithm S with a positive
reliability and a parameter-derived sample budget, rather than a zero-support
shortcut. This is one execution check, not a statistical validation of the
error theorem.

The same file offers the full reduction on a fair self-loop, whose cyclicity
probability is 1/2:

```sh
timeout 60s lake env lean --run validation/PositiveExample.lean sample
timeout 60s lake env lean --run validation/PositiveExample.lean count
```

These modes use the actual public parameters: sampling with `d=2`, or counting
with `r=2, d=2`. The vertex reliability budget is `M=131072`; it is not reduced
for the benchmark. Both use a deterministic all-one tape, so the printed
count is not required to meet the probabilistic error guarantee on that tape.

These benchmarks are opt-in because the executable uses repeated cumulative
scans over `M+1` pool alternatives. Polynomial worst-case overhead does not
make these conservative production budgets practical. A 45-second attempt at
the full sampler did not finish in the preparation environment; no successful
full-production run is claimed. The completed `oracle` example uses the larger
accuracy tolerance above and is not a benchmark of the full FPRAS.

The quick regression suite runs the `oracle` example and checks a deterministic
two-edge path
with `M=3` and a high tape. This fills the intermediate pool, selects its last
positive interval, and checks that the output remains one. The manuscript's
appendix and [discretization note](DISCRETISATION.md) distinguish the supplied
selector's costs from the indexed implementation's sharper bound.
