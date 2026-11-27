"""Enclose the complete error of a signed reading of one Dirichlet coefficient."""
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import isqrt
from pathlib import Path


class Interval:
    """Round each decimal endpoint outward, including the elementary logarithm."""

    def __init__(self, lower, upper=None):
        self.lower = Decimal(lower)
        self.upper = Decimal(upper) if upper is not None else self.lower

    def __neg__(self):
        return Interval(self.upper.copy_negate(), self.lower.copy_negate())

    def __add__(self, other):
        return Interval((self.lower + other.lower).next_minus(),
                        (self.upper + other.upper).next_plus())

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        endpoints = [x*y for x in (self.lower, self.upper) for y in (other.lower, other.upper)]
        return Interval(min(endpoints).next_minus(), max(endpoints).next_plus())

    def __truediv__(self, other):
        if other.lower <= 0 <= other.upper:
            raise ZeroDivisionError('interval contains zero')
        reciprocal = Interval((1/other.upper).next_minus(), (1/other.lower).next_plus())
        return self * reciprocal

    def log(self):
        return Interval(self.lower.ln().next_minus(), self.upper.ln().next_plus())

    def padded(self, radius):
        return self + Interval(radius.copy_negate(), radius)


def arctan_reciprocal(d):
    """Two successive partial sums of the alternating series enclose atan(1/d)."""
    lower = sum(Fraction((-1)**k, (2*k+1)*d**(2*k+1)) for k in range(52))
    upper = lower + Fraction(1, 105*d**105)
    return Interval((Decimal(lower.numerator)/Decimal(lower.denominator)).next_minus(),
                    (Decimal(upper.numerator)/Decimal(upper.denominator)).next_plus())


def sine(angle, half_pi):
    quadrant = int((angle.lower/half_pi.lower).to_integral_value())
    reduced = angle - Interval(quadrant)*half_pi
    if max(abs(reduced.lower), abs(reduced.upper)) >= 1:
        raise ArithmeticError('range reduction failed')
    use_sine = quadrant % 2 == 0
    term = reduced if use_sine else Interval(1)
    total = term
    negative_square = -(reduced*reduced)
    for j in range(1, 13):
        exponent = 2*j + int(use_sine)
        term = term*negative_square/Interval(exponent*(exponent-1))
        total += term
    # Taylor remainder at |x| < 1 is at most 1/25! for either polynomial.
    total = total.padded(Decimal('1e-24'))
    return total if quadrant % 4 < 2 else -total


def residual_numerators(limit, cutoff):
    """At index m, return m times the retained sum of reciprocal squarefree divisors."""
    squarefree = bytearray([1])*(limit+1)
    for k in range(2, isqrt(limit)+1):
        squarefree[k*k::k*k] = bytes(limit//(k*k))
    numerators = [0]*(limit+1)
    for divisor in range(cutoff+1, limit+1):
        if squarefree[divisor]:
            for index in range(divisor, limit+1, divisor):
                numerators[index] += index//divisor
    return numerators


def bias_enclosures(n, cutoff, limit, cancellations):
    with localcontext() as context:
        context.prec = 35
        pi = Interval(16)*arctan_reciprocal(5) - Interval(4)*arctan_reciprocal(239)
        half_pi = pi/Interval(2)
        numerators = residual_numerators(limit, cutoff)
        logs = {m: (Interval(m)/Interval(n)).log() for m in range(1, limit+1) if numerators[m]}
        results = []
        for count in cancellations:
            offsets = [(Interval(n+j)/Interval(n)).log() for j in range(1, count+1)]
            step = pi/(Interval(count+1)*offsets[0])
            denominator = Interval(1)
            for offset in offsets:
                denominator *= sine(step*offset, half_pi)
            if denominator.lower <= 0:
                raise ArithmeticError('normalization denominator must be positive')
            subtotal = Interval(0)
            for m, offset in logs.items():
                kernel = Interval(1)
                for root in offsets:
                    kernel *= sine(step*(root-offset), half_pi)
                subtotal += Interval(n*n*numerators[m])*kernel/(Interval(m**3)*denominator)
            tail = Interval(n*n)/denominator * (
                Interval(2)/Interval(limit*cutoff) + Interval(1)/Interval(limit**2))
            bias = subtotal - Interval(numerators[n])/Interval(n)
            results.append(bias.padded(tail.upper))
        return results


def main():
    path = Path(__file__).resolve().parents[1]/'benchmarks/signed-index-notches.json'
    case = json.loads(path.read_text())
    n = int(case['n'])
    readings = bias_enclosures(n, case['cutoff'], case['limit'], case['cancellations'])
    assert len(readings) == len(case['bias_bounds'])
    for count, result, bounds in zip(case['cancellations'], readings, case['bias_bounds']):
        assert Decimal(bounds[0]) <= result.lower <= result.upper <= Decimal(bounds[1])
        assert result.lower*n > 12 or result.upper*n < -12
        print(f'{count} canceled: bias in [{result.lower}, {result.upper}]')
    p, q = map(int, case['expected_factors'])
    assert p*q == n and residual_numerators(n, case['cutoff'])[n] == p+q+1


if __name__ == '__main__':
    main()
