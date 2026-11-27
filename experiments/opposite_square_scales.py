"""Compare both square-scale signs on bounded balanced prime pairs."""

import json
from itertools import combinations
from math import isqrt
from pathlib import Path

from experiments.gap_coverage import fermat, primes_through
from experiments.predecessor_square import factor_from_sum


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/opposite-square-scales.json'


def scales(cap):
    # All comparisons share the same precomputed squarefree list. The setup
    # uses only the cap. The small census never needs a large factor table.
    return [t for t in range(1, cap+1) if all(t % (k*k) for k in range(2, isqrt(t)+1))]


def scan(n, candidates, both, root_budget=None, check_selection=False):
    roots = discriminants = window_tests = comparisons = 0
    for t in candidates:
        if root_budget is not None and roots+discriminants >= root_budget:
            break
        r = isqrt(n//t)
        roots += 1
        lower = r-1 if t == 1 else r
        sign, total = 'predecessor', n+1-t*lower**2
        if both:
            upper = r+2 if t == 1 else r+1
            other = t*upper**2-n-1
            comparisons += 1
            # At scales 2, 3 and 4 the gap between the scaled roots is at
            # most two. At scale 1 the integer roots differ by three.
            use_larger = 2 <= t <= 4
            if (other > total if use_larger else other < total):
                sign, total, other = 'successor', other, total
            if check_selection:
                # An independent replay of the discarded sign. These checks
                # are outside the operation counts for the tested search.
                assert not (other > 0 and 4*n < other**2 and 2*other**2 <= 9*n), (n,t,other)
        window_tests += 1
        square = total**2
        if total > 0 and 4*n < square and 2*square <= 9*n:
            if root_budget is not None and roots+discriminants >= root_budget:
                break
            discriminants += 1
            factor = factor_from_sum(n, total)
            if factor is not None:
                return dict(scale=t, sign=sign, factor=factor, roots=roots, comparisons=comparisons,
                            discriminants=discriminants, window_tests=window_tests)
    return dict(scale=None, sign=None, factor=None, roots=roots,
                comparisons=comparisons, discriminants=discriminants, window_tests=window_tests)


def measure(n, candidates, extra):
    single = scan(n, candidates, both=False)
    paired = scan(n, candidates, both=True, check_selection=True)
    # Fermat spends one root on its initial midpoint. Count this in its budget.
    budget = paired['roots'] + paired['discriminants']
    assert len(extra) >= budget
    matched = scan(n, extra, both=False, root_budget=budget)
    control = fermat(n, max(0, budget-1))
    return dict(single=single, paired=paired, matched_predecessor_factor=matched['factor'],
                fermat_factor=control.factor or None,
                fermat_roots=1+control.squares)


def census(bits, candidates, extra):
    primes = [p for p in primes_through(2**bits-1) if p.bit_length() == bits]
    counts = dict(pairs=0, predecessor_hits=0, paired_hits=0, successor_first=0,
                  matched_predecessor_hits=0, paired_only_vs_matched_predecessor=0,
                  matched_predecessor_only_vs_paired=0, matched_fermat_hits=0,
                  paired_only_vs_fermat=0, fermat_only_vs_paired=0,
                  predecessor_scale_roots=0, paired_scale_roots=0,
                  predecessor_discriminant_roots=0, paired_discriminant_roots=0)
    for p, q in combinations(primes, 2):
        result = measure(p*q, candidates, extra)
        single, paired = result['single'], result['paired']
        matched = result['matched_predecessor_factor']
        for answer in (single['factor'], paired['factor'], matched, result['fermat_factor']):
            assert answer in (None, p)
        assert single['factor'] is None or paired['factor'] == p
        counts['pairs'] += 1
        counts['predecessor_hits'] += single['factor'] is not None
        counts['paired_hits'] += paired['factor'] is not None
        counts['successor_first'] += paired['sign'] == 'successor'
        counts['matched_predecessor_hits'] += matched is not None
        counts['paired_only_vs_matched_predecessor'] += paired['factor'] is not None and matched is None
        counts['matched_predecessor_only_vs_paired'] += paired['factor'] is None and matched is not None
        counts['matched_fermat_hits'] += result['fermat_factor'] is not None
        counts['paired_only_vs_fermat'] += paired['factor'] is not None and result['fermat_factor'] is None
        counts['fermat_only_vs_paired'] += paired['factor'] is None and result['fermat_factor'] is not None
        counts['predecessor_scale_roots'] += single['roots']
        counts['paired_scale_roots'] += paired['roots']
        counts['predecessor_discriminant_roots'] += single['discriminants']
        counts['paired_discriminant_roots'] += paired['discriminants']
    return counts


def main():
    fixture = json.loads(FIXTURE.read_text())
    candidates = scales(fixture['cap'])
    extra = scales(fixture['matched_predecessor_cap'])
    for case in fixture['controls']:
        n = int(case['n'])
        result = measure(n, candidates, extra)
        p, q = map(int, case['factors'])
        assert p*q == n and result == case['observed'], (n, result)
        for answer in (result['single']['factor'], result['paired']['factor'], result['fermat_factor']):
            assert answer in (None, p)
        print(json.dumps(dict(n=n, **result)))
    for sample in fixture['censuses']:
        observed = census(sample['bits'], candidates, extra)
        assert observed == sample['observed'], (sample['bits'], observed)
        print(json.dumps(dict(bits=sample['bits'], **observed)))


if __name__ == '__main__':
    main()
