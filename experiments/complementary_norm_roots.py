"""Compare three manufactured norm branches with their corresponding direct quadratic gcd."""

import json
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def compare(n, max_multiple=256, x=2):
    if gcd(n, 2*(x*x+3)) != 1:
        raise ValueError('the fixed seed and both scalings must be units')
    tests = 0
    for multiple in range(1, max_multiple + 1):
        root = isqrt(multiple*n + 3)
        for offset in (-1, 0, 1):
            t = root + offset
            direct = gcd(n, t*t-3)
            for c, k in ((0, 1), (3, 2), (-3, 2)):
                r = k*t-c
                a, b = r*x-3, x+r
                u = x*a+3*b
                v = x*b-a
                forced = gcd(n, (u+c*v)**2-3*(k*v)**2)
                if forced != direct:
                    raise AssertionError((n, t, c, k, direct, forced))
            tests += 1
            if 1 < direct < n:
                return dict(factors=sorted([str(direct), str(n//direct)], key=int), remaining=[],
                            direct_gcds=tests, forced_gcds=3*tests, root_evaluations=multiple, offset=offset)
    return dict(factors=[], remaining=[str(n)], direct_gcds=tests, forced_gcds=3*tests,
                root_evaluations=max_multiple, offset=None)


def fixtures():
    results = []
    cases = json.loads((ROOT / 'benchmarks' / 'complementary-keys.json').read_text())
    for case in cases:
        if case['id'] not in ('complementary-keys-pair', 'complementary-keys-fresh-2048',
                              'complementary-keys-crossed-2048'):
            continue
        run = compare(int(case['n']))
        if (run['factors'],run['remaining']) != (case['factors'],case['remaining']):
            raise AssertionError((case['id'],run))
        results.append(dict(id=case['id'], **run))
    return results


if __name__ == '__main__':
    print(json.dumps(fixtures(), indent=2))
