"""Exact rational utilities and bounded fair-bit choices."""
from fractions import Fraction as Q


def ceiling(x):
    return -(-x.numerator // x.denominator)


def ceil_log2(x):
    assert x >= 1
    k = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    return k + int((1 << k) * x.denominator < x.numerator)


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


