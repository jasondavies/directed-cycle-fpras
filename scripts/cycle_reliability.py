"""Graph predicates and exact product weights for finite regression checks."""
from fractions import Fraction


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
