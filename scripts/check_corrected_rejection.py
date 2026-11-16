"""Exact finite checks of the mathematical claims and executable model.

The reliability oracle here enumerates edge configurations exponentially.
These checks are regression evidence, not proofs or a polynomial oracle.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from finite_choices import ceiling
from corrected_rejection import (Draw, Query, budgets, cycle_vertices, estimate,
    initial_weights, prepare, proposal, sample, split_vertex)
from cycle_reliability import (cycle_witnesses, cyclic_independent, product_mass,
    reachable)

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(None)
def exact(n, arcs, ps, source, target):
    return sum((product_mass(ps, mask) for mask in range(1 << len(arcs))
                if reachable(n, arcs, mask, source, target)), Q(0))


def test_oracle(n, arcs, ps, source, target, alpha, delta, rng):
    # Fresh independent signs, with a prefix-dependent asymmetric distribution.
    threshold = 1 if sum(p == 1 for p in ps) % 2 else 2
    factor = 1 - alpha if rng.randrange(3) < threshold else 1 + alpha
    return exact(n, arcs, ps, source, target) * factor


def enumerate_protocol(factory, alpha, bad=False, bits=None):
    """Replay all finite transcripts of the actual generator implementation."""
    distribution, leaves = defaultdict(Q), 0
    stack = [((), Q(1))]
    while stack:
        history, mass = stack.pop()
        gen, answer = factory(), None
        try:
            for answer_next in history:
                gen.send(answer)
                answer = answer_next
            event = gen.send(answer)
        except StopIteration as result:
            distribution[result.value] += mass
            leaves += 1
            continue
        finally:
            gen.close()
        if isinstance(event, Query):
            if bad:
                alternatives = [(Q(-1), Q(1))]
            else:
                r = exact(event.n, event.arcs, event.probabilities, event.source, event.target)
                assert r > 0
                low = Q(1 if sum(p == 1 for p in event.probabilities) % 2 else 2, 3)
                alternatives = [(r * (1 - alpha), low), (r * (1 + alpha), 1 - low)]
        else:
            assert isinstance(event, Draw) and min(event.weights) >= 0 and sum(event.weights) > 0
            if bits is None:
                alternatives = [(i, w / sum(event.weights)) for i, w in enumerate(event.weights) if w]
            else:
                grid, cumulative, alternatives = 1 << bits, Q(0), []
                for i, w in enumerate(event.weights):
                    end = cumulative + w / sum(event.weights)
                    mass_grid = Q(ceiling(grid * end) - ceiling(grid * cumulative), grid)
                    alternatives.append((i, mass_grid))
                    cumulative = end
        stack.extend((history + (answer,), mass * prob) for answer, prob in alternatives if prob)
    assert sum(distribution.values()) == 1
    return distribution, leaves


cases = [
    (1, ((0, 0),), (Q(1, 7),), (0,), "loop"),
    (2, ((0, 1), (1, 0)), (Q(1, 10**30), Q(1, 10**30)), (0,), "rare_cycle_fvs1"),
    (2, ((0, 0), (0, 1), (1, 0)), (Q(1, 5), Q(1, 3), Q(2, 7)), (0, 1), "overlapping_cycles"),
    (2, ((0, 1), (0, 1), (1, 0)), (Q(1, 3), Q(1, 2), Q(2, 3)), (0, 1), "parallel_edges"),
    (3, ((0, 1), (1, 0), (2, 2)), (Q(1), Q(1, 2), Q(0)), (0, 1, 2), "zero_one_unreachable"),
    (2, ((0, 0), (0, 1), (1, 0)), (Q(1), Q(1), Q(1)), (0,), "deterministic"),
]
records = []
for n, arcs, ps, vertices, name in cases:
    prepare(n, arcs, ps, vertices)
    true_weights = []
    for v in vertices:
        size, split, s, t = split_vertex(n, arcs, v)
        truth = Q(0)
        for mask in range(1 << len(arcs)):
            independent_members = {arcs[e][0] for e in cycle_witnesses(n, arcs, mask)}
            assert cycle_vertices(n, arcs, mask) == independent_members
            assert reachable(size, split, mask, s, t) == (v in independent_members)
            truth += product_mass(ps, mask) * (v in independent_members)
        assert truth == exact(size, split, ps, s, t)
        true_weights.append(truth)
    z = sum((product_mass(ps, mask) for mask in range(1 << len(arcs))
             if cyclic_independent(n, arcs, mask)), Q(0))
    assert z <= sum(true_weights) <= len(vertices) * z
    alpha = Q(1, 16 * (len(arcs) + 1))
    # Enumerate initial randomized answers too, checking the identity separately
    # for every resulting weight vector (the theorem conditions on these).
    weights_law, initial_leaves = enumerate_protocol(
        lambda: initial_weights(n, arcs, ps, vertices), alpha)
    leaves = 0
    for weights in weights_law:
        law, count = enumerate_protocol(lambda: proposal(n, arcs, ps, vertices, weights), alpha)
        leaves += count
        accepted = {mask: law.get((mask, True), Q(0)) for mask in range(1 << len(arcs))}
        for mask, mass in accepted.items():
            expected = (product_mass(ps, mask) / (2 * sum(weights))
                        if cyclic_independent(n, arcs, mask) else Q(0))
            assert mass == expected, (name, weights, mask, mass, expected)
        # Enumerate actual fixed-grid choices against the exact-choice reference.
        rounded, _ = enumerate_protocol(lambda: proposal(n, arcs, ps, vertices, weights), alpha, bits=8)
        outcomes = law.keys() | rounded.keys()
        rounding_tv = sum(abs(law.get(x, 0) - rounded.get(x, 0)) for x in outcomes) / 2
        assert rounding_tv <= Q(len(vertices) + 2 * len(arcs) + 2, 2**8)
        q = sum(accepted.values())
        assert q == z / (2 * sum(weights)) and q >= Q(1, 4 * len(vertices))
        assert 2 * sum(weights) * q == z
        for mask, mass in accepted.items():
            expected = product_mass(ps, mask) / z if cyclic_independent(n, arcs, mask) else 0
            assert mass / q == expected
        # A capped first-success sampler has exactly a timeout mixture.
        cap = 3
        timeout = (1 - q)**cap
        support = sum(1 << e for e, p in enumerate(ps) if p)
        capped = {mask: (1 - timeout) * mass / q + timeout * (mask == support)
                  for mask, mass in accepted.items()}
        tv = sum(abs(capped[mask] - accepted[mask] / q) for mask in accepted) / 2
        assert tv <= timeout
    records.append({"case": name, "cycle_probability": str(z),
                    "initial_transcripts": initial_leaves, "weight_vectors": len(weights_law),
                    "proposal_transcripts": leaves})
    print(name, "exact transcript checks passed", flush=True)

# The hardness gadget, on every simple undirected graph with at most four vertices.
hardness_graphs = 0
for n in range(5):
    edges = tuple(combinations(range(n), 2))
    for graph in range(1 << len(edges)):
        selected_edges = [uv for e, uv in enumerate(edges) if graph >> e & 1]
        arcs = tuple((2*v, 2*v+1) for v in range(n)) + tuple(
            arc for u, v in selected_edges for arc in ((2*u+1, 2*v), (2*v+1, 2*u)))
        assert len(arcs) == len(set(arcs)) and all(u != v for u, v in arcs)
        fixed = ((1 << len(arcs)) - 1) ^ ((1 << n) - 1)
        independent_count, acyclic_count = 0, 0
        for chosen in range(1 << n):
            independent = all(not (chosen >> u & 1 and chosen >> v & 1) for u, v in selected_edges)
            acyclic = not cyclic_independent(2*n, arcs, fixed | chosen)
            assert independent == acyclic
            independent_count += independent
            acyclic_count += acyclic
        assert Q(acyclic_count, 2**n) == Q(independent_count, 2**n)
        hardness_graphs += 1

# Fixed-bit public paths, failure totality, validation, and exact-zero detection.
n, arcs, ps, vertices, _ = cases[2]
value, stats = estimate(n, arcs, ps, test_oracle, Q(1, 2), Q(1, 4), vertices, seed=2026)
z = sum(product_mass(ps, mask) for mask in range(1 << len(arcs)) if cyclic_independent(n, arcs, mask))
assert abs(value - z) <= z / 2 and stats['oracle_calls'] <= stats['max_oracle_calls']
mask, sampling = sample(n, arcs, ps, test_oracle, witnesses=vertices, seed=3)
assert cyclic_independent(n, arcs, mask) and product_mass(ps, mask) > 0
bad = lambda *args: Q(-1)
mask, fallback = sample(n, arcs, ps, bad, witnesses=vertices, seed=3)
assert fallback['fallback'] and cyclic_independent(n, arcs, mask) and product_mass(ps, mask) > 0
bad_law, _ = enumerate_protocol(lambda: proposal(n, arcs, ps, vertices, (Q(1), Q(1))), Q(1, 64), bad=True)
assert not any(accepted for (_, accepted), mass in bad_law.items() if mass)
assert estimate(2, ((0, 1),), (Q(1, 2),), bad)[0] == 0
assert sample(2, ((0, 1),), (Q(1, 2),), bad)[0] is None
try:
    prepare(2, ((0, 1), (1, 0)), (Q(1, 2), Q(1, 2)), ())
except ValueError:
    pass
else:
    raise AssertionError('invalid feedback set accepted')
small = budgets(3, 2, 10, Q(1, 16))
large = budgets(3, 2, 10**100, Q(1, 16))
assert small['alpha'] == large['alpha'] == Q(1, 64)
report = {"scope": "Exact finite transcript checks; no polynomial oracle or Lean refinement proof",
          "cases": records, "hardness_gadgets_checked": hardness_graphs,
          "fixed_bit_estimate": str(value), "truth": str(z),
          "fallbacks_and_invalid_feedback_set_checked": True,
          "precision_independent_of_proposal_count": True,
          "exact_fixed_grid_coupling_checked": True}
(ROOT / 'validation/corrected-rejection-results.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: corrected rejection identities; {hardness_graphs} hardness gadgets; finite-bit paths', flush=True)
