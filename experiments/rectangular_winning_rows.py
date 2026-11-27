"""Locate the winning rows after revealing the factors of a constructed control."""
import argparse
import json
from math import gcd
from pathlib import Path

from experiments.offset_winner_positions import published_controls
from experiments.rectangular_root_windows import bounds

ROOT = Path(__file__).resolve().parents[1]


def bracket(r, n, limit):
    """Neighbors of r/n among fractions with denominator at most limit."""
    if not 0 < r < n or not 1 <= limit < n or gcd(r, n) != 1:
        raise ValueError('expected a reduced proper fraction with denominator above the cutoff')
    a, b, c, d = 0, 1, 1, 1
    low, high = r, n - r
    steps = 0
    while b + d <= limit:
        if low == high:
            raise ArithmeticError('the target fraction has a denominator within the cutoff')
        if low > high:
            skip = min((low - 1) // high, (limit - b) // d)
            a, b, low = a + skip*c, b + skip*d, low - skip*high
        else:
            skip = min((high - 1) // low, (limit - d) // b)
            c, d, high = c + skip*a, d + skip*b, high - skip*low
        steps += 1
    if c*b - a*d != 1 or not (low == r*b - n*a > 0 and high == n*c - r*d > 0):
        raise ArithmeticError('invalid bracket')
    return ((a, b, low), (c, d, high)), steps


def observation(p, q):
    if not 2 < p < q or p % 2 == 0 or q % 2 == 0 or gcd(p, q) != 1:
        raise ValueError('expected two distinct odd prime factors in ascending order')
    n = p*q
    b, h, last = bounds(n, 1)
    if h >= p or b+h >= n:
        raise ValueError('rectangle exceeds the verified balanced-input bounds')
    # This diagnostic uses both known factors to choose a nontrivial square root of one.
    r = (2*p*pow(p, -1, q) - 1) % n
    sides, steps = bracket(r, n, b)
    rows = []
    for side, (quotient, y, x) in zip(('lower', 'upper'), sides):
        record = dict(side=side, fraction_numerator=str(quotient), y=str(y), x=str(x), inside=x <= h)
        if x <= h:
            k, rem = divmod(y*y-x*x, n)
            factor = gcd(y-x, n)
            if rem or not 1 <= k <= last or gcd(x, y) != 1 or factor not in (p, q):
                raise ArithmeticError('invalid primitive witness')
            record['multiplier'] = str(k)
            record['scales'] = str(min(b//y, h//x))
        rows.append(record)
    wins = [int(row['multiplier']) for row in rows if row['inside']]
    if not wins:
        raise ArithmeticError('balanced rectangle has no solution')
    return dict(n=str(n), root=str(r), denominator_cap=str(b), numerator_cap=str(h),
                last_multiplier=str(last), steps=steps, neighbors=rows, first_multiplier=str(min(wins)))


def report():
    controls = [dict(id=label, **observation(p,q)) for label, _, p, q in published_controls()]
    panel = []
    source = json.loads((ROOT/'research/rectangular-multiplier-products.json').read_text())
    for case in source['panel']:
        p,q = map(int,case['factors'])
        data = observation(p,q)
        first = str(case['methods']['weights']['data']['first']['multiplier'])
        if first != data['first_multiplier']:
            raise ArithmeticError('retrospective first row disagrees with the actual search')
        panel.append(dict(n=case['n'], first_multiplier=first,
                          primitive_rows=sum(row['inside'] for row in data['neighbors'])))
    return dict(method='Retrospective reconstruction using published prime factors.',controls=controls,panel=panel)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    encoded = json.dumps(report(), indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded, end='')
