# Palomar submission

The repository uses the conventional root layout: `Challenge.lean`,
`Solution.lean`, `comparator.json`, and `formalization.yaml`. Leave the optional
project, Comparator, and metadata path fields blank.

The submission title is **Directed-cycle probability: verified counting and
conditional sampling**. This names the formal guarantees precisely: polynomial
machine runtime is treated in the paper's written analysis, with separate
bounds for the indexed implementation and the supplied executable. The repository
and manuscript are licensed under Apache-2.0; cited sources and dependencies
retain their own licenses.

## Statements of record

All compared declarations are in `DirectedCycleFPRAS.Publication`.

| Declaration | Claim |
| --- | --- |
| `vertex_reliability` | A vertex lies on a retained cycle exactly when the split terminals are connected. |
| `feedback_cover` | A supplied feedback vertex set covers every cyclic configuration. |
| `count_correct` | Relative error `1/r` with failure at most `2⁻ᵈ` on a uniform finite tape. |
| `count_zero` | Every tape returns zero when the true cyclicity probability is zero. |
| `sample_correct` | Conditional sampling within total variation `2⁻ᵈ` when cyclicity has positive probability. |
| `sample_none_iff` | On every tape, the sampler returns `none` exactly when cyclicity probability is zero. |
| `acyclicity_probability` | The independent-set count equals `2^|V|` times the gadget's acyclicity probability. |

The two definition holes, `count` and `sample`, are filled by the actual rational
implementations in the Solution. Graph notions, independent product probabilities,
and tape lengths are explicit in the Challenge. `sample` returns an `Option`:
`none` reports an undefined conditional law, and `some` carries a configuration.
The accuracy statements constrain
the supplied implementations for every permitted input; no oracle-accuracy premise
is assumed. Algorithm S accuracy is proved in their dependency closure.

Counting and sampling use numbered finite vertices and edges, with a supplied
ordering of the feedback set. The underlying library accepts arbitrary finite
types and explicit enumerations. The sampler's registered claim is its output-law
bound, not a separate guarantee about every failed-oracle execution. Independent-set
inapproximability and machine runtime are written results, not Comparator claims.

## Local checks

Run from the repository root with the pinned Lean toolchain and dependencies:

```sh
lake exe cache get
bash scripts/check.sh
python3 -m venv .lake/submission-venv
.lake/submission-venv/bin/pip install -r validation/requirements.txt
.lake/submission-venv/bin/python scripts/check_palomar.py
bash scripts/verify-comparator.sh
make -C paper
```

The metadata check downloads an immutable revision of the upstream v0.4 schema;
`--schema /path/to/v0.4.schema.json` permits an offline copy. Classification codes
follow Palomar's arXiv and MSC2020 taxonomies. The source scan includes validation
files, rejects Lean symlinks, and enforces module headers and file-size limits.

Comparator runs inside `bubblewrap` and checks the Solution using Lean's kernel,
NanoDa, and con-ron. It needs working unprivileged namespaces and self-contained
Lake dependency directories; symlinks to another workspace's packages are not a
portable checkout. CI installs the sandbox on a disposable Ubuntu runner.
Challenge warnings about deliberate holes are expected; the Solution and its
proof dependencies must have none. `scripts/check.sh` audits the Solution too.

## Final handoff

1. Review the metadata, especially authorship, automation, review status, and scope.
2. Commit all intended files and push the publication snapshot to the public
   repository, `https://github.com/jasondavies/directed-cycle-fpras`.
3. Run `git rev-parse HEAD` and use the full 40-character SHA. Palomar checks that
   immutable commit; local uncommitted or unpushed changes are excluded.
4. Open [the submission form](https://submit.palomar-registry.org/) and declare
   the appropriate author/maintainer authorization relationship. Keep the private
   status-page link. Submission and registration are separate decisions.

For an agent-operated submission, follow the service's
[agent protocol](https://submit.palomar-registry.org/llms.txt), rather than driving
the browser form. This preparation does not push, submit, or register the result.
See the current [submission requirements](https://palomar-registry.org/how-to-submit)
before sending the final snapshot.
