"""Count integer midpoints compatible with every power of selected primes."""

from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True)
class Lane:
    residue: int
    modulus: int

    def first(self, low):
        return low + (self.residue - low) % self.modulus

    def count(self, low, high):
        first = self.first(low)
        return 0 if first > high else 1 + (high - first) // self.modulus


def lift_roots(roots, modulus, prime, digits, target):
    """Lift all known roots from modulus through the requested further digits."""
    for _ in range(digits):
        next_modulus = modulus * prime
        roots = [x for r in roots for x in range(r, next_modulus, modulus)
                 if (x*x - target) % next_modulus == 0]
        modulus = next_modulus
    return roots, modulus


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def midpoint_lanes(n, prime, exponent):
    """Disjoint congruence classes h for which h²−n is a square mod prime^exponent."""
    if not is_prime(prime):
        raise ValueError("the auxiliary modulus must be prime")
    if gcd(n, prime) != 1 or exponent < 1:
        raise ValueError("need a positive exponent and a product coprime to the prime")
    unit_digits = 3 if prime == 2 else 1
    units = [1] if prime == 2 else sorted({i*i % prime for i in range(1, prime)})
    roots, modulus, level = [0], 1, 0
    lanes = []
    while level < exponent and roots:
        digits = min(unit_digits, exponent-level)
        for unit in units:
            branch, period = lift_roots(roots, modulus, prime, digits, n+modulus*unit)
            lanes.extend(Lane(root, period) for root in branch)
        jump = min(2, exponent-level)
        roots, modulus = lift_roots(roots, modulus, prime, jump, n)
        level += jump
    lanes.extend(Lane(root, modulus) for root in roots)
    return lanes


def stable_exponent(prime, max_discriminant):
    """All higher powers have the same decision on this bounded discriminant interval."""
    if prime < 2 or max_discriminant < 0:
        raise ValueError("need a base of at least two and a nonnegative discriminant bound")
    if prime == 2:
        return max(1, max_discriminant.bit_length()+2)
    exponent, power = 1, prime
    while power <= max_discriminant:
        exponent += 1
        power *= prime
    return exponent


def count_intersection(low, high, families):
    """Count a CRT intersection without expanding any local prime-power period."""
    if low > high:
        return 0
    groups = sorted(families, key=len)

    def visit(i, lane):
        first = lane.first(low)
        if first > high:
            return 0
        if i == len(groups):
            return lane.count(low, high)
        if first + lane.modulus > high:
            return int(all(any(first % b.modulus == b.residue for b in group)
                           for group in groups[i:]))
        total = 0
        for b in groups[i]:
            shift = (b.residue-lane.residue) * pow(lane.modulus, -1, b.modulus)
            joint = Lane(lane.residue + lane.modulus*(shift % b.modulus),
                         lane.modulus*b.modulus)
            total += visit(i+1, joint)
        return total

    return visit(0, Lane(0, 1))


def _balanced_families(n, primes):
    low, high = 1+isqrt(n-1), isqrt(9*n//8)
    families = []
    profile = []
    for prime in primes:
        exponent = stable_exponent(prime, max(0, high*high-n))
        group = midpoint_lanes(n, prime, exponent)
        families.append(group)
        profile.append([prime, exponent, len(group)])
    return low, high, families, profile


def search(n, primes):
    """Count the whole interval, locating and checking a midpoint if it is unique."""
    if n <= 1 or n % 2 == 0 or len(set(primes)) != len(primes) or not all(map(is_prime, primes)):
        raise ValueError("need an odd product greater than one and distinct auxiliary primes")
    for p in primes:
        d = gcd(n, p)
        if 1 < d < n:
            return {"factor": d, "outcome": "auxiliary divisor", "range_queries": 0,
                    "square_tests": 0}
    low, high, families, profile = _balanced_families(n, primes)
    survivors = count_intersection(low, high, families)
    result = {"low": low, "high": high, "candidates": max(0, high-low+1),
              "prime_exponent_classes": profile, "survivors": survivors,
              "range_queries": 1, "square_tests": 0, "factor": None,
              "outcome": "multiple midpoints" if survivors else "empty interval"}
    if survivors == 1:
        left, right = low, high
        while left < right:
            mid = (left+right)//2
            result["range_queries"] += 1
            if count_intersection(left, mid, families):
                right = mid
            else:
                left = mid+1
        gap = isqrt(left*left-n)
        result.update(midpoint=left, square_tests=1, outcome="unique midpoint")
        if (left-gap)*(left+gap) == n and 1 < left-gap < n:
            result["factor"] = left-gap
    return result


if __name__ == "__main__":
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("primes", type=int, nargs="+")
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.primes), indent=2))
