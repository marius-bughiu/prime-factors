"""Independently check the five finite weighted-subset bounds with rational prices.

A support prime in [2^j,2^(j+1)) spends at least j of the determinant's B
bits. In a segment starting at a, its contribution to the Rankin correction
is at most u = ceil(2^80 a^(-k/64)), in fixed-point units. For any nonnegative
bit price λ and per-octave prices μ_j, every feasible sum of contributions is
at most λB + sum_j μ_j cap_j + sum_segments cap_a max(0, u - jλ - μ_j).
This follows by charging each selected prime and then bounding each remaining
nonnegative term separately. The first omitted octave already costs at least
its largest contribution, and all later contributions decrease.

Run python3 -m experiments.weighted_subset_budget_dual. Every numerical check
uses integers or exact fractions, including the final population comparison.
"""

from bisect import bisect_left
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd, isqrt, prod


X = 2**1023
SCALE = 2**80
SMALL = 2**16
WHEEL_PRIMES = (2, 3, 5, 7, 11, 13)
WHEEL_TERMS = [(prod(subset), (-1)**len(subset)) for i in range(len(WHEEL_PRIMES)+1)
               for subset in combinations(WHEEL_PRIMES, i)]
# K=J, numerator of theta over 64, reference endpoint for λ, anchor bits, saving.
CASES = (
    (16, 36, 294912, 693, 294),
    (64, 43, 4456448, 783, 201),
    (256, 47, 71303168, 842, 139),
    (1024, 50, 1140850688, 884, 94),
    (4096, 52, 18253611008, 915, 60),
)


@lru_cache(None)
def small_primes():
    return [p for p in range(2, SMALL) if all(p % d for d in range(2, isqrt(p)+1))]


@lru_cache(None)
def wheel_prefix(stop):
    """Count positive integers below stop coprime to 30030 by inclusion-exclusion."""
    return sum(sign*((stop-1)//d) for d, sign in WHEEL_TERMS)


def segment_capacity(a, b):
    if b <= SMALL:
        primes = small_primes()
        return bisect_left(primes, b) - bisect_left(primes, a)
    return wheel_prefix(b) - wheel_prefix(a)


def reciprocal(a, k):
    """The smallest integer u with u^64 a^k >= SCALE^64."""
    target, power = SCALE**64, a**k
    lo, hi = 0, SCALE
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**64*power >= target:
            hi = mid
        else:
            lo = mid
    if not (hi-1)**64*power < target <= hi**64*power:
        raise ArithmeticError('invalid reciprocal rounding')
    return hi


def catalogue(k):
    height = 24*k
    h = 1+isqrt(k-1)
    width = max(1, k//h)
    counts = []
    for residue in range(1, 24):
        if gcd(residue, 24) != 1:
            continue
        rows = 0
        for r in range(1, k+1):
            step = gcd(24, 2*(r+residue))
            rows += 2*k+1+isqrt((4*r*width**2)//step**2)
        counts.append(rows)
    anchors = ((X+width-1)//width)*sum(counts)
    deviation = height+2*h*width
    determinant_cap = 2*k*deviation*(8*X*h+deviation)
    bits = (max(counts)-1)*(determinant_cap-1).bit_length()
    excess_cap = height*(8*X*h+height)
    exceptions = X*k*(4*h+height//X)*(2*(excess_cap//X)+1)
    return anchors, bits, excess_cap, exceptions


def dual_bound(bits, k, reference):
    # Use the integer denominator j_last throughout for both λ and μ_j.
    last = reference.bit_length()-1
    price = reciprocal(reference, k)
    objective = price*bits
    for j in range(1, last+1):
        lo = 2**j
        width = max(1, lo//16)
        # Every prime in the larger octave divides binom(2*lo,lo) <= 2^(2*lo).
        room = lo if lo < SMALL else (2*lo)//j
        segments = [(last*reciprocal(a, k)-j*price, segment_capacity(a, a+width))
                    for a in range(lo, 2*lo, width)]
        # Choose μ_j at the last available slot inside the octave cap.
        slots, mu = 0, 0
        for gain, capacity in segments:
            slots += capacity
            if slots >= room:
                mu = max(0, gain)
                break
        objective += mu*room + sum(capacity*max(0, gain-mu) for gain, capacity in segments)
    tail = last+1
    if last*reciprocal(2**tail, k) > price*tail:
        raise ArithmeticError('unpaid prime in the omitted tail')
    return Fraction(objective, last)


def verify(k, theta_numerator, reference, anchor_bits, saving):
    if not 32 <= theta_numerator < 64:
        raise ValueError('Rankin exponent must lie in [1/2,1)')
    anchors, bits, excess_cap, exceptions = catalogue(k)
    scaled_correction = dual_bound(bits, theta_numerator, reference)
    # Four positive terms of ln 2 = 2 atanh(1/3) suffice for log2(e)<1443/1000.
    log_lower = sum(Fraction(2, (2*i+1)*3**(2*i+1)) for i in range(4))
    if log_lower <= Fraction(1000, 1443):
        raise ArithmeticError('insufficient lower bound on ln 2')
    log_bound = (Fraction(theta_numerator*(excess_cap-1).bit_length(), 64)
                 + Fraction(1443, 1000*SCALE)*scaled_correction)
    if log_bound > anchor_bits:
        raise ArithmeticError(f'K={k}: dual exceeds {anchor_bits} anchor bits')
    numerator = 2*anchors*2**anchor_bits + exceptions
    if 21_000_000*2**saving*numerator > X**2:
        raise ArithmeticError(f'K={k}: failed population saving {saving}')
    return bits


if __name__ == '__main__':
    print('K=J   theta   support bits   anchor bits   fraction below')
    for case in CASES:
        k, theta, _, anchor, saving = case
        bits = verify(*case)
        print(f'{k:4}  {theta}/64  {bits:13,}   {anchor:11}   2^-{saving}')
