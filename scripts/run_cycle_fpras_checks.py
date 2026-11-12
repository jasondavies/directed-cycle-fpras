"""Exercise the executable reduction with exact and bounded-error test oracles.

The finite oracle enumerates subgraphs; it is NOT the external reliability FPRAS.
"""
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path

from cycle_fpras_reduction import estimate, plan
from cycle_reliability import product_mass, reachable, cyclic_independent

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(None)
def exact(n, arcs, ps, source, target):
    return sum(product_mass(ps, mask) for mask in range(1 << len(arcs))
               if reachable(n, arcs, mask, source, target))


def oracle(n, arcs, ps, source, target, alpha, delta, rng):
    assert 0 < alpha < 1 and 0 < delta < 1
    return exact(n, arcs, ps, source, target)


def perturbed(n, arcs, ps, source, target, alpha, delta, rng):
    value = oracle(n, arcs, ps, source, target, alpha, delta, rng)
    return value * (1 + alpha if sum(p == 1 for p in ps) % 2 else 1 - alpha)


records = []
cases = [
    (3, [(0, 1), (1, 2)], [Q(1, 3), Q(1, 4)], oracle, "acyclic"),
    (1, [(0, 0)], [Q(1, 7)], oracle, "self_loop"),
    (2, [(0, 1), (1, 0)], [Q(1, 10**50), Q(1, 10**50)], oracle, "rare_cycle"),
    (2, [(0, 0), (0, 1), (1, 0)], [Q(1, 5), Q(1, 3), Q(2, 7)], oracle, "overlap"),
    (2, [(0, 0), (0, 1), (1, 0)], [Q(1, 5), Q(1, 3), Q(2, 7)], perturbed, "perturbed_overlap"),
]
for n, arcs, ps, supplied, name in cases:
    truth = sum(product_mass(ps, mask) for mask in range(1 << len(arcs))
                if cyclic_independent(n, arcs, mask))
    result, stats = estimate(n, arcs, ps, supplied, epsilon=Q(1, 2), delta=Q(1, 4), seed=120026)
    assert abs(result - truth) <= truth / 2
    if name in ("acyclic", "self_loop", "rare_cycle"):
        assert result == truth
    records.append({"case": name, "truth": str(truth), "estimate": str(result),
                    "relative_error": str(abs(result / truth - 1)) if truth else "0",
                    "stats": {k: str(v) if isinstance(v, Q) else v for k, v in stats.items()}})
    print(name, "passed", flush=True)

# Invalid oracle answers must cause a defined fallback, never division by zero.
bad, stats = estimate(2, [(0, 1), (1, 0)], [Q(1, 2)] * 2,
                      lambda *args: Q(-10), seed=1)
assert bad == 0 and stats["oracle_zero_fallback"]
large = plan(100, Q(1, 2**128), Q(1, 2**80))
assert large["samples"].bit_length() < 300
assert large["random_bits_per_choice"] < 400
out = {"date": "2026-11-12", "oracle": "exponential exact / bounded-error test oracle",
       "external_fpras_implemented": False, "cases": records,
       "bad_oracle_fallback_checked": True, "large_precision_budget_checked": True}
(ROOT / "sources/cycle-fpras-results.json").write_text(json.dumps(out, indent=2) + "\n")
print("PASS: executable reduction checks", flush=True)
