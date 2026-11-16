"""Vertex-witness counting and conditional sampling with a reliability oracle.

The oracle signature is (n, arcs, probabilities, s, t, alpha, delta, rng).
It returns a rational alpha-relative estimate with failure at most delta.
This module models the reduction; it does not implement Algorithm S and has
no Lean refinement proof. The Query/Draw protocol permits exact enumeration
of proposal choices and adaptive oracle transcripts.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import random

from finite_choices import ceiling, ceil_log2, choose
from cycle_reliability import cyclic_independent, product_mass, reachable


@dataclass(frozen=True)
class Query:
    n: int
    arcs: tuple
    probabilities: tuple
    source: int
    target: int


@dataclass(frozen=True)
class Draw:
    weights: tuple


def split_vertex(n, arcs, v):
    """v is the out terminal, n the new in terminal; preserve edge identities."""
    return n + 1, tuple((u, n if w == v else w) for u, w in arcs), v, n


def cycle_vertices(n, arcs, mask):
    """One iterative Kosaraju SCC decomposition, including retained self-loops."""
    out, rev = [[] for _ in range(n)], [[] for _ in range(n)]
    loops = set()
    for e, (u, v) in enumerate(arcs):
        if mask >> e & 1:
            out[u].append(v)
            rev[v].append(u)
            if u == v:
                loops.add(u)
    seen, order = set(), []
    for start in range(n):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(out[start]))]
        while stack:
            u, edges = stack[-1]
            v = next(edges, None)
            if v is None:
                order.append(u)
                stack.pop()
            elif v not in seen:
                seen.add(v)
                stack.append((v, iter(out[v])))
    seen, cyclic = set(), set(loops)
    for start in reversed(order):
        if start in seen:
            continue
        seen.add(start)
        component, stack = [], [start]
        while stack:
            u = stack.pop()
            component.append(u)
            for v in rev[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        if len(component) > 1:
            cyclic.update(component)
    return cyclic


def prepare(n, arcs, probabilities, witnesses=None):
    arcs, ps = tuple(arcs), tuple(map(Q, probabilities))
    if n < 0 or len(arcs) != len(ps) or any(not 0 <= p <= 1 for p in ps):
        raise ValueError("invalid graph probabilities")
    if any(not (0 <= u < n and 0 <= v < n) for u, v in arcs):
        raise ValueError("invalid endpoint")
    vertices = tuple(range(n)) if witnesses is None else tuple(witnesses)
    if len(set(vertices)) != len(vertices) or any(not 0 <= v < n for v in vertices):
        raise ValueError("witness vertices must be distinct graph vertices")
    support = sum(1 << e for e, p in enumerate(ps) if p)
    selected = set(vertices)
    remainder = sum(1 << e for e, (u, v) in enumerate(arcs)
                    if ps[e] and u not in selected and v not in selected)
    if cyclic_independent(n, arcs, remainder):
        raise ValueError("supplied vertices are not a feedback set of the support")
    return arcs, ps, vertices, support


def reliability(n, arcs, ps, source, target):
    if source == target:
        return Q(1)
    support = sum(1 << e for e, p in enumerate(ps) if p)
    if not reachable(n, arcs, support, source, target):
        return Q(0)
    answer = Q((yield Query(n, arcs, tuple(ps), source, target)))
    return min(Q(1), max(Q(0), answer))


def initial_weights(n, arcs, ps, vertices):
    weights = []
    for v in vertices:
        size, split, source, target = split_vertex(n, arcs, v)
        weights.append((yield from reliability(size, split, ps, source, target)))
    return tuple(weights)


def proposal(n, arcs, ps, vertices, weights):
    """Return (configuration, accepted); g always uses nominal probabilities."""
    if not sum(weights):
        return None, False
    i = yield Draw(tuple(weights))
    size, split, source, target = split_vertex(n, arcs, vertices[i])
    residual, mask, g = list(ps), 0, Q(1)
    for e, p in enumerate(ps):
        if p in (0, 1):
            if p:
                mask |= 1 << e
            continue
        branches = []
        for b in (0, 1):
            residual[e] = Q(b)
            r = yield from reliability(size, split, residual, source, target)
            branches.append((p if b else 1 - p) * r)
        total = sum(branches)
        if not total:
            return None, False
        b = yield Draw(tuple(branches))
        g *= branches[b] / total
        residual[e] = Q(b)
        if b:
            mask |= 1 << e
    mass = product_mass(ps, mask)
    members = cycle_vertices(n, arcs, mask).intersection(vertices)
    denominator = 2 * len(members) * weights[i] * g
    if not mass or vertices[i] not in members or not denominator:
        return None, False
    h = min(Q(1), max(Q(0), mass / denominator))
    accepted = yield Draw((1 - h, h))
    return mask, bool(accepted)


class Runner:
    def __init__(self, oracle, alpha, failure, bits, rng):
        self.oracle, self.alpha, self.failure = oracle, alpha, failure
        self.bits, self.rng, self.calls, self.draws = bits, rng, 0, 0

    def run(self, program):
        answer = None
        while True:
            try:
                event = program.send(answer)
            except StopIteration as result:
                return result.value
            if isinstance(event, Query):
                self.calls += 1
                answer = self.oracle(event.n, event.arcs, event.probabilities,
                                     event.source, event.target, self.alpha,
                                     self.failure, self.rng)
            else:
                self.draws += 1
                answer = choose(event.weights, self.rng, self.bits)


def budgets(m, k, proposals, beta):
    calls = k + 2 * m * proposals
    alternatives = proposals * (k + 2 * m + 2)
    return {"alpha": Q(1, 16 * (m + 1)), "max_calls": calls,
            "oracle_delta": Q(beta) / calls,
            "bits": ceil_log2(Q(alternatives) / beta)}


def estimate(n, arcs, probabilities, oracle, epsilon=Q(1, 4), delta=Q(1, 4),
             witnesses=None, seed=None):
    epsilon, delta = Q(epsilon), Q(delta)
    if not (0 < epsilon <= Q(1, 2) and 0 < delta < Q(1, 2)):
        raise ValueError("expected 0 < epsilon <= 1/2 and 0 < delta < 1/2")
    arcs, ps, vertices, support = prepare(n, arcs, probabilities, witnesses)
    if not cyclic_independent(n, arcs, support):
        return Q(0), {"exact_zero": True, "oracle_calls": 0}
    count = ceiling(64 * len(vertices) / epsilon**2)
    runs = 8 * ceil_log2(1 / delta) + 1
    plan = budgets(len(arcs), len(vertices), count, Q(1, 16))
    runner = Runner(oracle, plan["alpha"], plan["oracle_delta"], plan["bits"], random.Random(seed))
    estimates = []
    for _ in range(runs):
        weights = runner.run(initial_weights(n, arcs, ps, vertices))
        accepted = sum(runner.run(proposal(n, arcs, ps, vertices, weights))[1] for _ in range(count))
        estimates.append(2 * sum(weights) * accepted / count)
    return sorted(estimates)[runs // 2], {"runs": runs, "proposals_per_run": count,
        "oracle_calls": runner.calls, "max_oracle_calls": runs * plan["max_calls"],
        "alpha": plan["alpha"], "bits": plan["bits"]}


def sample(n, arcs, probabilities, oracle, eta=Q(1, 100), witnesses=None, seed=None):
    eta = Q(eta)
    if not 0 < eta < Q(1, 2):
        raise ValueError("expected 0 < eta < 1/2")
    arcs, ps, vertices, support = prepare(n, arcs, probabilities, witnesses)
    if not cyclic_independent(n, arcs, support):
        return None, {"undefined": True, "oracle_calls": 0}
    # The full support itself is a fixed cyclic configuration of positive mass.
    fallback = support
    count = 4 * len(vertices) * ceil_log2(3 / eta)
    plan = budgets(len(arcs), len(vertices), count, eta / 3)
    runner = Runner(oracle, plan["alpha"], plan["oracle_delta"], plan["bits"], random.Random(seed))
    weights = runner.run(initial_weights(n, arcs, ps, vertices))
    for _ in range(count):
        mask, accepted = runner.run(proposal(n, arcs, ps, vertices, weights))
        if accepted:
            return mask, {"fallback": False, "oracle_calls": runner.calls, "cap": count}
    return fallback, {"fallback": True, "oracle_calls": runner.calls, "cap": count}
