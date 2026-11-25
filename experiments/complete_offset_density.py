"""Bound the surviving fraction of primitive (offset, multiplier) pairs on both controls."""

import json
from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path

from experiments.complete_offset_search import CONTROL_IDS
from experiments.grouped_offset_rows import local_failures
from scripts.factor import primes_through


def primitive_pair_bounds(n, primes):
    """Rigorous finite bounds for the full coprime schedule, without enumerating it."""
    t = isqrt(n)
    h = n-t*t
    j_limit = isqrt(4*h//3)
    if not h or j_limit < 2:
        raise ValueError('the density estimate requires a nonsquare and at least two offsets')

    scale = 2**120
    low_product = high_product = scale
    sum_upper = obstruction_count = 0
    for p in primes:
        single, higher = local_failures(-h, [p], j_limit)
        if not single and not higher:
            continue
        q = (single or higher)[0]
        denom = (p+1)*q
        low_product = low_product*(denom-p)//denom
        high_product = (high_product*(denom-p)+denom-1)//denom
        sum_upper += (scale*p+denom-1)//denom
        obstruction_count += 1

    order = 18
    subsets = sum(comb(obstruction_count, i) for i in range(order+1))
    c = Fraction(t, h)
    # 1+ln(J) <= 1+bit_length(J), and zeta(2) < 2.
    grid_error = (2*(1+2/c)*(1+j_limit.bit_length())+2)/j_limit
    population_low = c*j_limit**2/4*(1-grid_error)
    if grid_error >= 1:
        raise ValueError('the uniform count error exceeds the primitive population bound')
    bonferroni_tail = Fraction(sum_upper, scale)**order / factorial(order)
    error = (bonferroni_tail+(subsets+1)*grid_error)/(1-grid_error)
    low = max(Fraction(0), Fraction(low_product, scale)-error)
    high = min(Fraction(1), Fraction(high_product, scale)+error)
    # Outward-rounded millionths of one percent.
    unit = 10**8
    minimum = low*population_low
    return dict(obstructions=obstruction_count, minimum_percent_units=int(low*unit),
                maximum_percent_units=-(-high.numerator*unit//high.denominator),
                surviving_pairs_at_least=minimum.numerator//minimum.denominator)


if __name__ == '__main__':
    controls = json.loads((Path(__file__).resolve().parents[1]/'benchmarks/grouped-norm.json').read_text())
    primes = primes_through(10**6)
    for case in controls:
        if case['id'] in CONTROL_IDS:
            print(case['id'], json.dumps(primitive_pair_bounds(int(case['n']), primes)))
