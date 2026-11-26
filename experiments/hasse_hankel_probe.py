"""Eight public gcds from the first two Somos-4 consistency minors at four shifts.

The degree-six and degree-ten coefficient lists come from the identities in
PrimeFactors/HasseHankelBilinear.lean, in ascending powers of C²/B³. We
homogenize without division, so the test works even when B or C is a nonunit.
Each comparison arm receives eight gcds. The two-minor common-root diagnostic
is postprocessing and does not count as an independent recovery. The script
uses no factor labels to select a shift, an arm, or an operand.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path
from random import Random

from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
SUMMARY = ROOT / 'research' / 'hasse-hankel-probe.json'
SEED = 20261126
POLYNOMIALS = (
    (-26368, 795712, -5672064, 9444924, 4411422, 6213267, 11691702),
    (7110656, -331866112, 4804732928, -20123449856, -42695682816,
     277267821408, -790326605952, 963638542530, -1652488154568,
     -642558404367, -172014697116),
)


def homogeneous(coefficients, x, y):
    degree = len(coefficients) - 1
    return sum(a*x**j*y**(degree-j) for j, a in enumerate(coefficients))


def operands(c, n=None):
    b, cubic = 3*c*c-1, c**3-c
    if n is not None:
        b, cubic = b % n, cubic % n
    x, y = cubic*cubic, b**3
    if n is not None:
        x, y = x % n, y % n
    u, v = (homogeneous(coefficients, x, y) for coefficients in POLYNOMIALS)
    return (2*b*cubic**4*u, b*cubic**8*v), (u, v), (b, cubic)


FIXED = tuple(operands(c) for c in (2, 3))


def search(n):
    """Compute complete, equal-gcd-budget arms; retain factor gcds and full misses."""
    if n < 3 or n % 2 == 0:
        raise ValueError('an odd integer at least three is required')
    r = isqrt(n)
    shifts = [2, 3, r, r+1]
    rows = []
    for c, values in zip(shifts, (*FIXED, operands(r, n), operands(r+1, n))):
        raw, residual, simple = ([gcd(x, n) for x in pair] for pair in values)
        rows.append(dict(shift=c, raw=raw, residual=residual, simple=simple))
    rng = Random(SEED+n)
    # Secondary elementary comparison: eight positive odd integers nearest the
    # smaller factor's upper endpoint, cycling at one only on tiny inputs.
    last = (r - 1)//2
    trials = [gcd(1 + 2*((last-i) % (last+1)), n) for i in range(8)]
    return dict(rows=rows, random=[gcd(rng.randrange(n), n) for _ in range(8)],
                descending_odd=trials)


def factor_set(values, n):
    return {v for v in values if 1 < v < n}


def outcomes(n, result):
    rows = result['rows']
    output = {arm: any(factor_set(row[arm], n) for row in rows)
              for arm in ('raw', 'residual', 'simple')}
    output['random'] = bool(factor_set(result['random'], n))
    output['descending_odd'] = bool(factor_set(result['descending_odd'], n))
    output['raw_without_descending_odd'] = output['raw'] and not output['descending_odd']
    output['descending_odd_without_raw'] = output['descending_odd'] and not output['raw']
    output['raw_fixed'] = any(factor_set(row['raw'], n) for row in rows[:2])
    output['raw_adaptive'] = any(factor_set(row['raw'], n) for row in rows[2:])
    output['raw_adaptive_only'] = output['raw_adaptive'] and not output['raw_fixed']
    output['raw_without_simple'] = output['raw'] and not output['simple']
    output['raw_without_fixed_or_simple'] = output['raw_adaptive_only'] and not output['simple']
    output['raw_miss'] = not output['raw']
    output['raw_without_random'] = output['raw'] and not output['random']
    output['random_without_raw'] = output['random'] and not output['raw']
    # A common residual prime with B,C both units locally excludes the obvious
    # roots. The simple gcds may still detect a different prime of this n.
    output['common_nondegenerate_prime'] = any(
        (g := gcd(*row['residual'])) > 1 and g // gcd(g, row['simple'][0]*row['simple'][1]) > 1
        for row in rows)
    return output


def panel():
    primes = primes_through(2**10-1)
    total, by_width, examples = Counter(), {}, {}
    for bits in range(4, 11):
        counts = Counter()
        for p, q in combinations((p for p in primes if p.bit_length() == bits), 2):
            n = p*q
            run = search(n)
            if any(v not in (1, p, q, n) for row in run['rows']
                   for arm in ('raw', 'residual', 'simple') for v in row[arm]):
                raise ArithmeticError('gcd disagrees with independently generated pair')
            outcomes_n = outcomes(n, run)
            counts.update({k: int(v) for k, v in outcomes_n.items()})
            counts['products'] += 1
            name = 'raw_without_fixed_or_simple'
            if outcomes_n[name]:
                fermat_tests = (p+q)//2 - isqrt(n)
                for label, include in ((name, True), ('also_missed_by_eight_nearby_trials',
                        not outcomes_n['descending_odd'] and fermat_tests > 8)):
                    if include and label not in examples:
                        examples[label] = dict(n=str(n), run=run, fermat_tests=fermat_tests)
        total.update(counts)
        by_width[str(bits)] = dict(counts)
    controls = {}
    for row in json.loads((ROOT / 'benchmarks/near-smooth-sum.json').read_text()):
        if row['id'] not in ('near-smooth-fresh-2048', 'near-smooth-crossed-2048'):
            continue
        n = int(row['n'])
        run = search(n)
        result = outcomes(n, run)
        controls[row['id']] = dict(outcomes=result, raw=[r['raw'] for r in run['rows']],
                                   remaining=row['n'] if result['raw_miss'] else None)
    if len(controls) != 2:
        raise ValueError('the fresh and crossed controls are both required')
    return dict(shifts=['2', '3', 'isqrt(n)', 'isqrt(n)+1'],
                gcds_per_arm=8, uniform_residue_seed='20261126+n',
                population='Every pair of distinct primes of the same bit width 4 through 10.',
                fixed_raw_bits=[[abs(k).bit_length() for k in values[0]] for values in FIXED],
                fixed_trial_primes_through_1023=[[[p for p in primes if value % p == 0]
                                                   for value in arms[0]] for arms in FIXED],
                totals=dict(total), by_factor_bits=by_width, examples=examples, controls=controls)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    result = panel()
    if args.verify:
        if result != json.loads(SUMMARY.read_text()):
            raise SystemExit('Hankel probe results differ from the stored panel')
        print(json.dumps(result['totals'], sort_keys=True))
    elif args.write:
        SUMMARY.write_text(json.dumps(result, indent=2) + '\n')
    else:
        print(json.dumps(result, indent=2))
