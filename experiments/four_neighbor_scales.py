"""Compare four neighbor products using fixed small prime populations."""

import json
from itertools import combinations
from math import isqrt
from pathlib import Path

from experiments.gap_coverage import fermat, primes_through
from experiments.opposite_square_scales import scales
from experiments.predecessor_square import factor_from_sum


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/four-neighbor-scales.json'


def scan(n, candidates, include_gap, budget=None):
    roots = discs = sites = 0
    for t in candidates:
        if budget is not None and roots+discs >= budget:
            break
        r = isqrt(n//t)
        roots += 1
        even = r+r%2
        nearby = t*even**2
        # At scale one the sum-root guesses are r−1 and r+2. Only the
        # even one could occur in the product of the two even neighbors.
        total_square = ((r-1 if r%2 else r+2)**2 if t == 1 else nearby)
        total = abs(total_square-(n+1))
        sum_possible = 4*n < total**2 and 2*total**2 <= 9*n
        gap = abs(nearby-(n-1))
        gap_possible = include_gap and gap > 0 and 2*gap**2 < n
        assert not (sum_possible and gap_possible), (n,t,total,gap)
        sites += 1 + (t == 1 and include_gap)
        if not sum_possible and not gap_possible:
            continue
        if budget is not None and roots+discs >= budget:
            break
        discs += 1
        if sum_possible:
            sign = '++' if total_square > n+1 else '--'
            factor = factor_from_sum(n, total)
        else:
            sign = '+-' if nearby > n-1 else '-+'
            total = isqrt(gap**2+4*n)
            factor = (total-gap)//2
            if factor < 2 or 2*factor+gap != total or factor*(factor+gap) != n:
                factor = None
        if factor is not None:
            return dict(factor=factor, scale=t, signs=sign, scaled_roots=roots,
                        discriminant_roots=discs, square_values=sites)
    return dict(factor=None, scale=None, signs=None, scaled_roots=roots,
                discriminant_roots=discs, square_values=sites)


def measure(n, candidates, extended):
    run = scan(n, candidates, include_gap=True)
    budget = run['scaled_roots']+run['discriminant_roots']
    assert len(extended) >= budget
    two = scan(n, extended, include_gap=False, budget=budget)
    control = fermat(n, budget-1)
    return dict(four=run, matched_two=two, matched_fermat=control.factor or None)


def census(bits, candidates, extended):
    primes = [p for p in primes_through(2**bits-1) if p.bit_length() == bits]
    counts = dict(pairs=0, four_hits=0, two_hits=0, fermat_hits=0,
                  four_only_vs_two=0, two_only_vs_four=0, four_only_vs_fermat=0,
                  fermat_only_vs_four=0, first_by_sign={s:0 for s in ('--','++','-+','+-')},
                  scaled_roots=0, discriminant_roots=0, square_values=0)
    for p, q in combinations(primes, 2):
        result = measure(p*q, candidates, extended)
        run, two, f = result['four'], result['matched_two']['factor'], result['matched_fermat']
        found = run['factor']
        assert all(answer in (None,p) for answer in (found,two,f))
        counts['pairs'] += 1
        counts['four_hits'] += found is not None
        counts['two_hits'] += two is not None
        counts['fermat_hits'] += f is not None
        counts['four_only_vs_two'] += found is not None and two is None
        counts['two_only_vs_four'] += two is not None and found is None
        counts['four_only_vs_fermat'] += found is not None and f is None
        counts['fermat_only_vs_four'] += f is not None and found is None
        if found:
            counts['first_by_sign'][run['signs']] += 1
        for key in ('scaled_roots','discriminant_roots','square_values'):
            counts[key] += run[key]
    return counts


def main():
    fixture = json.loads(FIXTURE.read_text())
    candidates, extended = scales(fixture['cap']), scales(fixture['matched_cap'])
    for case in fixture['controls']:
        p, q = map(int, case['factors'])
        result = measure(int(case['n']), candidates, extended)
        assert p*q == int(case['n']) and result == case['observed']
        assert all(answer in (None,p) for answer in (result['four']['factor'],
                   result['matched_two']['factor'], result['matched_fermat']))
        print(json.dumps(dict(n=case['n'], **result)))
    for case in fixture['censuses']:
        counts = census(case['bits'], candidates, extended)
        assert counts == case['observed'], counts
        print(json.dumps(dict(bits=case['bits'], **counts)))


if __name__ == '__main__':
    main()
