"""Exact exponential oracle model for the conditional FPRAS reduction.

This does NOT implement the external polynomial-time reliability FPRAS.
It verifies the reduction and its sampling identity on small rational inputs.
"""
from fractions import Fraction
from functools import lru_cache


def reachable(n, arcs, mask, source, target, omit=None):
    reached = {source}
    stack = [source]
    while stack:
        u = stack.pop()
        for i, (a, b) in enumerate(arcs):
            if i != omit and mask >> i & 1 and a == u and b not in reached:
                reached.add(b)
                stack.append(b)
    return target in reached


def cycle_witnesses(n, arcs, mask):
    return [i for i, (u, v) in enumerate(arcs)
            if mask >> i & 1 and reachable(n, arcs, mask, v, u, omit=i)]


def cyclic_independent(n, arcs, mask):
    """Independent Kahn acyclicity test, not the edge-return-path predicate."""
    out = [[] for _ in range(n)]
    indegree = [0] * n
    for i, (u, v) in enumerate(arcs):
        if mask >> i & 1:
            out[u].append(v)
            indegree[v] += 1
    stack = [v for v in range(n) if indegree[v] == 0]
    removed = 0
    while stack:
        u = stack.pop()
        removed += 1
        for v in out[u]:
            indegree[v] -= 1
            if indegree[v] == 0:
                stack.append(v)
    return removed < n


def product_mass(probabilities, mask):
    mass = Fraction(1)
    for i, p in enumerate(probabilities):
        mass *= p if mask >> i & 1 else 1-p
    return mass


def conditional_law(n, arcs, probabilities, witness, relative_perturbation=Fraction(0)):
    """Enumerate the law of sequential conditional sampling using exact/perturbed R.

    A fixed witness edge is forced present. Remaining coordinates are exposed in
    index order. The perturbed oracle has deliberately alternating signed error.
    """
    m = len(arcs)
    u, v = arcs[witness]
    other = [i for i in range(m) if i != witness]

    @lru_cache(None)
    def rel(position, present):
        if position == len(other):
            return Fraction(reachable(n, arcs, present, v, u, omit=witness))
        i = other[position]
        return (1-probabilities[i])*rel(position+1, present) + probabilities[i]*rel(position+1, present | (1 << i))

    weight = probabilities[witness]*rel(0, 0)
    if not weight:
        return weight, {}
    distribution = {}
    def generate(position, present, mass):
        if position == len(other):
            distribution[present | (1 << witness)] = mass
            return
        i = other[position]
        r0, r1 = rel(position+1, present), rel(position+1, present | (1 << i))
        # Opposite signed errors stress the normalization; zeros stay exact.
        sign = 1 if (present.bit_count()+position) % 2 else -1
        b0 = (1-probabilities[i])*r0*(1+sign*relative_perturbation)
        b1 = probabilities[i]*r1*(1-sign*relative_perturbation)
        total = b0+b1
        assert total > 0
        if b0:
            generate(position+1, present, mass*b0/total)
        if b1:
            generate(position+1, present | (1 << i), mass*b1/total)
    generate(0, 0, Fraction(1))
    return weight, distribution


def audit(n, arcs, probabilities, alpha=Fraction(1, 10000)):
    m = len(arcs)
    masses = {mask: product_mass(probabilities, mask) for mask in range(1 << m)}
    witness_sets = {mask: cycle_witnesses(n, arcs, mask) for mask in masses}
    assert all(bool(witness_sets[mask]) == cyclic_independent(n, arcs, mask) for mask in masses)
    target = sum(mass for mask, mass in masses.items() if cyclic_independent(n, arcs, mask))
    weights, laws, perturbed = [], [], []
    maximum_tv = Fraction(0)
    for i in range(m):
        weight, law = conditional_law(n, arcs, probabilities, i)
        direct_weight = sum(mass for mask, mass in masses.items() if i in witness_sets[mask])
        assert weight == direct_weight
        weights.append(weight)
        laws.append(law)
        _, perturbed_law = conditional_law(n, arcs, probabilities, i, alpha)
        perturbed.append(perturbed_law)
        if weight:
            assert sum(law.values()) == 1
            for mask, mass in masses.items():
                assert law.get(mask, 0) == (mass/weight if i in witness_sets[mask] else 0)
            tv = sum(abs(law.get(mask, 0)-perturbed_law.get(mask, 0)) for mask in masses)/2
            assert tv <= 4*m*alpha
            maximum_tv = max(maximum_tv, tv)
    total_weight = sum(weights)
    if not total_weight:
        assert target == 0
        return target, maximum_tv
    mixture = {mask: sum(weights[i]*laws[i].get(mask, 0) for i in range(m))/total_weight for mask in masses}
    estimate_mean = sum(mixture[mask]/len(witness_sets[mask]) for mask in masses if witness_sets[mask])
    assert total_weight*estimate_mean == target
    assert Fraction(1, m) <= estimate_mean <= 1
    # End-to-end expectation with inexact weights and inexact conditional laws.
    approximate_weights = [w*(1+alpha if i % 2 else 1-alpha) for i, w in enumerate(weights)]
    approximate_total = sum(approximate_weights)
    approximate_mean = sum(sum(approximate_weights[i]*perturbed[i].get(mask, 0) for i in range(m))
                           / approximate_total / len(witness_sets[mask])
                           for mask in masses if witness_sets[mask])
    assert abs(approximate_total*approximate_mean/target-1) <= 20*m*m*alpha
    return target, maximum_tv
