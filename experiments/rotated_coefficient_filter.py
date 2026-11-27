"""Certify rotated Fourier grids on small products using exact arithmetic.

Run python3 -m experiments.rotated_coefficient_filter from the repository root.
"""
import json
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import isqrt
from pathlib import Path

from experiments.circular_coefficient_filter import retained


CUTOFF = 3
MAX_CALLS = 64
FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/rotated-coefficient-filter.json"


@dataclass
class DivisorScan:
    last: int
    next_divisor: int = CUTOFF + 1
    total: int = 0


class EarlierCoefficients:
    """Resume each earlier index's trial divisions if its full value is requested."""
    def __init__(self):
        self.scans = {}
        self.trials = 0

    def inspect(self, n, full=False):
        if n not in self.scans:
            self.scans[n] = DivisorScan(isqrt(n))
        scan = self.scans[n]
        while scan.next_divisor <= scan.last and (full or scan.total == 0):
            d = scan.next_divisor
            cofactor, remainder = divmod(n, d)
            self.trials += 1
            scan.next_divisor += 1
            if remainder == 0:
                scan.total += d
                if d != cofactor:
                    scan.total += cofactor
        return scan.total

    def work(self):
        return {"integer_roots": len(self.scans), "divisor_tests": self.trials}


def rotated_grid(n):
    earlier = EarlierCoefficients()
    rules = class_tests = 0
    for m in range(1, MAX_CALLS + 1):
        steps = (n - 1) // m
        for v in range(max(1, steps.bit_length())):
            rules += 1
            for j in range(1, steps + 1):
                class_tests += 1
                if (j & -j) != (1 << v) and earlier.inspect(n - j*m):
                    break
            else:
                return m, v, {**earlier.work(), "rules": rules, "class_tests": class_tests}
    return None


def first_uncorrected_grid(n, limit):
    earlier = EarlierCoefficients()
    for m in range(1, limit + 1):
        if all(earlier.inspect(n - j*m) == 0 for j in range(1, (n-1)//m + 1)):
            return m
    return None


def subtract_earlier(n, m):
    """At radius 1/2 each earlier term is an integer times a power of two."""
    earlier = EarlierCoefficients()
    correction = 0
    additions = 0
    for h in range(m, n, m):
        value = earlier.inspect(n - h, full=True)
        if value:
            correction += value << h
            additions += 1
    return correction, {**earlier.work(), "shifted_additions": additions}


def divide_monic(coefficients, divisor):
    """Integer polynomial long division, coefficients in ascending order."""
    remainder = list(coefficients)
    quotient = [0] * max(1, len(coefficients) - len(divisor) + 1)
    for degree in range(len(coefficients) - 1, len(divisor) - 2, -1):
        leading = remainder[degree]
        if leading:
            start = degree - len(divisor) + 1
            quotient[start] = leading
            for i, coefficient in enumerate(divisor):
                remainder[start+i] -= leading*coefficient
    return quotient, remainder[:len(divisor)-1]


@cache
def cyclotomic(order):
    polynomial = [-1] + [0]*(order-1) + [1]
    for d in range(1, order):
        if order % d == 0:
            polynomial, remainder = divide_monic(polynomial, cyclotomic(d))
            assert not any(remainder)
    return polynomial


def certify_grid(n, coefficients, m, v=None, correction=0):
    """Evaluate every distinct point at radius 1/2 and enclose the infinite readout.

    The arrays represent numerators in Z[zeta] with the common denominator
    2^degree. For an unrotated grid conjugate pairs require a single evaluation.
    """
    if v is None:
        order = m
        nodes = [(j, 1 if j == 0 or 2*j == m else 2) for j in range(m//2 + 1)]
    else:
        stride = 1 << (v + 2)
        order = stride*m
        nodes = [(1 + stride*j, 1) for j in range(m)]
    degree = len(coefficients) - 1
    average = [0]*order
    for exponent, multiplicity in nodes:
        value = [0]*order
        for j, coefficient in enumerate(coefficients):
            value[(exponent*j) % order] += coefficient << (degree-j)
        # Multiply by the conjugate target phase, then add twice the real part.
        for k, entry in enumerate(value):
            if entry:
                shift = (k - exponent*n) % order
                average[shift] += multiplicity*entry
                average[-shift % order] += multiplicity*entry

    _, reduced = divide_monic(average, cyclotomic(order))
    denominator = 2*m*(1 << (degree-n))
    centre = Fraction(reduced[0], denominator) - correction
    radius = Fraction(sum(abs(x) for x in reduced[1:]), denominator)
    # a(j) <= j². Summing (degree+t)²/2^t for t >= 1 gives this tail even
    # before the distinct phases can cancel.
    radius += Fraction(degree**2 + 4*degree + 6, 1 << (degree-n))
    total = round(centre)
    error = abs(centre-total) + radius
    if error >= Fraction(1, 2):
        raise ArithmeticError("the enclosure has not certified rounding")
    gap = isqrt(total**2 - 4*n)
    factors = [(total-gap)//2, (total+gap)//2]
    if factors[0]*factors[1] != n or sum(factors) != total or factors[0] < 2:
        raise ArithmeticError("rounded sum did not give a proper split")
    return {"grid_size": m, "calls": len(nodes), "degree": degree, "sum": total,
            "terms_evaluated": len(nodes)*len(coefficients), "factors": factors,
            "error_bound": str(error)}


def compare(n):
    rule = rotated_grid(n)
    if rule is None:
        return None, first_uncorrected_grid(n, 2*MAX_CALLS)
    m, v, preparation = rule
    # This reference even grants the unrotated 2m grid, which uses m-1 complex
    # points plus two real endpoints. The matched corrected grid uses m calls.
    uncorrected = first_uncorrected_grid(n, 2*m)
    corrected_size = 2*m - 1
    correction, corrected_work = subtract_earlier(n, corrected_size)
    coeffs = [retained(CUTOFF, j) for j in range(n+97)]
    rotated = certify_grid(n, coeffs, m, v=v)
    ordinary = certify_grid(n, coeffs, corrected_size, correction=correction)
    assert rotated["factors"] == ordinary["factors"]
    return {"n": n, "v": v, "rotated": {**preparation, **rotated},
            "ordinary": {**corrected_work, **ordinary},
            "first_uncorrected_grid": uncorrected}, uncorrected


def census():
    totals = {}
    successes = []
    for width in (5, 6, 7):
        primes = [p for p in range(2**(width-1), 2**width)
                  if all(p % d for d in range(2, isqrt(p)+1))]
        products = [p*q for p, q in combinations(primes, 2)]
        hits = raw_wins = both_miss = 0
        for n in products:
            result, uncorrected = compare(n)
            if result is None:
                both_miss += uncorrected is None
            else:
                successes.append(result)
                hits += 1
                raw_wins += uncorrected is None
        totals[width] = dict(products=len(products), rotated_hits=hits,
                             wins_over_uncorrected=raw_wins, neither_raw_grid=both_miss)
    return totals, successes


if __name__ == "__main__":
    summary, rows = census()
    expected = {int(row["n"]): row["factors"] for row in json.loads(FIXTURE.read_text())}
    actual = {row["n"]: list(map(str, row["rotated"]["factors"])) for row in rows}
    assert actual == expected
    print(json.dumps({"widths": summary, "recoveries": rows}, indent=2))
