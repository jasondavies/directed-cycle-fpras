"""Original edge-witness estimator, retained as a model of the earlier reduction.

The oracle signature is (n, arcs, probabilities, s, t, alpha, delta, rng).
It must return a rational alpha-relative approximation with failure <= delta,
in time polynomial in the input length, 1/alpha, and log(1/delta).
The bit-model contract uses Algorithm S / Theorem 9 of Feng--Fu--Guo,
arXiv:2608.02523v2, together with research/DISCRETISATION.md; their unit-cost
arithmetic theorem alone does not provide it. This module implements only
the original reduction. corrected_rejection.py implements the revised model;
neither module implements the external reliability oracle.
"""
from fractions import Fraction as Q
import random

from cycle_reliability import cycle_witnesses, cyclic_independent, reachable


def ceiling(x):
    return -(-x.numerator // x.denominator)


def ceil_log2(x):
    assert x >= 1
    k = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    return k + int((1 << k) * x.denominator < x.numerator)


def plan(m, epsilon=Q(1, 4), delta=Q(1, 4)):
    epsilon, delta = Q(epsilon), Q(delta)
    assert m >= 1 and 0 < epsilon <= Q(1, 2) and 0 < delta < Q(1, 2)
    samples = ceiling(200 * m * m * ceil_log2(4 / delta) / epsilon**2)
    max_calls = m + 2 * m * samples
    return {"alpha": epsilon / (100 * m * (m + 1)), "samples": samples,
            "max_oracle_calls": max_calls, "oracle_delta": delta / (4 * max_calls),
            "random_bits_per_choice": ceil_log2(12 * samples * m / delta)}


def choose(weights, rng, bits):
    """Fixed random-bit budget; TV error <= len(weights) / 2**bits."""
    total = sum(weights)
    assert total > 0 and all(w >= 0 for w in weights)
    threshold = Q(rng.getrandbits(bits), 1 << bits) * total
    cumulative = Q(0)
    for i, weight in enumerate(weights):
        cumulative += weight
        if threshold < cumulative:
            return i
    raise AssertionError("unreachable rational sampling endpoint")


def estimate(n, arcs, probabilities, oracle, epsilon=Q(1, 4), delta=Q(1, 4), seed=None):
    arcs, probabilities = tuple(arcs), tuple(map(Q, probabilities))
    assert len(arcs) == len(probabilities) and n >= 0
    assert all(0 <= u < n and 0 <= v < n for u, v in arcs)
    assert all(0 <= p <= 1 for p in probabilities)
    m = len(arcs)
    support = sum(1 << i for i, p in enumerate(probabilities) if p)
    if not cyclic_independent(n, arcs, support):
        return Q(0), {"oracle_calls": 0, "samples": 0, "exact_zero": True}
    budget = plan(m, epsilon, delta)
    rng = random.Random(seed)
    calls = 0

    def reliability(ps, source, target):
        nonlocal calls
        if source == target:
            return Q(1), True
        possible = sum(1 << i for i, p in enumerate(ps) if p)
        if not reachable(n, arcs, possible, source, target):
            return Q(0), False
        calls += 1
        value = Q(oracle(n, arcs, tuple(ps), source, target,
                         budget["alpha"], budget["oracle_delta"], rng))
        # Clipping preserves the accuracy guarantee and handles bad oracle draws.
        return min(Q(1), max(Q(0), value)), True

    weights = []
    for e, (u, v) in enumerate(arcs):
        if not probabilities[e]:
            weights.append(Q(0))
            continue
        ps = list(probabilities)
        ps[e] = Q(0)
        r, _ = reliability(ps, v, u)
        weights.append(probabilities[e] * r)
    total = sum(weights)
    if not total:
        # Reachable only when at least one reliability call failed its guarantee.
        return Q(0), {"oracle_calls": calls, "samples": 0, "oracle_zero_fallback": True}

    score = Q(0)
    for _ in range(budget["samples"]):
        witness = choose(weights, rng, budget["random_bits_per_choice"])
        u, v = arcs[witness]
        mask = 1 << witness
        ps = list(probabilities)
        ps[witness] = Q(0)
        for i, p in enumerate(probabilities):
            if i == witness:
                continue
            if p in (0, 1):
                if p:
                    mask |= 1 << i
                continue
            ps[i] = Q(0)
            r0, feasible0 = reliability(ps, v, u)
            ps[i] = Q(1)
            r1, feasible1 = reliability(ps, v, u)
            branches = [(1 - p) * r0, p * r1]
            if not sum(branches):
                # Preserve feasible conditioning even after an inaccurate oracle draw.
                branches = [(1 - p) * feasible0, p * feasible1]
            bit = choose(branches, rng, budget["random_bits_per_choice"])
            ps[i] = Q(bit)
            if bit:
                mask |= 1 << i
        witnesses = cycle_witnesses(n, arcs, mask)
        assert witness in witnesses
        score += Q(1, len(witnesses))
    assert calls <= budget["max_oracle_calls"]
    return total * score / budget["samples"], {
        **budget, "oracle_calls": calls, "exact_zero": False}
