"""Compare honest first-mark searches on all small balanced prime pairs."""

import json
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.mixed_ratio_heights import jacobi
from scripts.factor import fermat_split, primes_through, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/circle-mark-prefix-skip.json'


def choose_target(n):
    """Take the first negative Jacobi value, retaining any factor seen along the way."""
    for a in range(2, n):
        symbol = jacobi(a, n)
        if symbol == -1:
            return a, None
        if symbol == 0:
            return a, gcd(a, n)
    raise ValueError('expected a product of two distinct odd primes')


def consecutive(n, a, cap):
    for x in range(1, cap + 1):
        divisor = gcd(x * x - a, n)
        if divisor > 1:
            return x, divisor
    raise ArithmeticError('no mark within the factor-width bound')


def band_search(n, a, width):
    """Only the product, target and factor width enter this search."""
    upper = (1 << width) - 1
    lower = n // (1 << width) + 1
    if not 0 < a < lower < upper:
        raise ValueError('the small-target census requires this positive target below the factor band')
    cap = upper // 2
    x = 1 + isqrt(a + lower - 1)
    prefix = x - 1
    gcds = 0
    roots = 1
    bands = 0
    jumps = 0
    k = 1
    while x <= cap:
        bands += 1
        if k * (upper - lower) >= lower - 1:
            end = cap
        else:
            end = min(cap, isqrt(a + k * upper))
            roots += 1
        while x <= end:
            gcds += 1
            divisor = gcd(x * x - a, n)
            if divisor > 1:
                return dict(
                    first_x=x, divisor=divisor, direct_gcds=x, band_gcds=gcds,
                    prefix_skips=prefix, later_skips=x - gcds - prefix,
                    later_jumps=jumps, bands=bands, square_roots=roots,
                )
            x += 1
        if x > cap:
            break
        k += 1
        next_x = 1 + isqrt(a + k * lower - 1)
        roots += 1
        if next_x > x:
            jumps += 1
            x = next_x
    raise ArithmeticError('jumped search missed the factor-width bound')


def measure(n, width):
    if not 7 <= width <= 12 or n.bit_length() != 2 * width:
        raise ValueError('expected a small balanced input of the requested width')
    # The true midpoint of two width-bit factors is strictly below 2**width.
    # This limit uses only the supplied width and contains the entire search.
    fermat_divisor, midpoints = fermat_split(n, 1 << width)
    if fermat_divisor is None:
        raise ArithmeticError('Fermat search exhausted the factor-width bound')
    baseline = dict(fermat_divisor=fermat_divisor, fermat_midpoints=midpoints)
    a, early = choose_target(n)
    if early is not None:
        return dict(target=a, early_factor=early, **baseline)
    result = band_search(n, a, width)
    reference = consecutive(n, a, ((1 << width) - 1) // 2)
    if reference != (result['first_x'], result['divisor']):
        raise ArithmeticError('jumped and consecutive searches give different first marks')
    return dict(target=a, **result, **baseline)


def census(width):
    upper = 1 << width
    primes = [p for p in primes_through(upper - 1) if p >= upper // 2]
    totals = dict(
        products=0, factors_during_target_selection=0, jacobi_tests=0, fermat_midpoints=0,
        direct_gcds=0, band_gcds=0, prefix_skips=0, later_skips=0,
        later_jumps=0, bands=0, square_roots=0, products_with_later_skips=0,
    )
    band_fields = ('direct_gcds', 'band_gcds', 'prefix_skips', 'later_skips', 'later_jumps',
                   'bands', 'square_roots')
    largest_later_saving = None
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * width:
            continue
        row = measure(n, width)
        totals['products'] += 1
        totals['jacobi_tests'] += row['target'] - 1
        totals['fermat_midpoints'] += row['fermat_midpoints']
        divisor = row['early_factor'] if 'early_factor' in row else row['divisor']
        for found in (divisor, row['fermat_divisor']):
            if found <= 1 or n % found or sorted((found, n // found)) != [p, q]:
                raise ArithmeticError('a discovered factorization disagrees with the prime labels')
        if 'early_factor' in row:
            totals['factors_during_target_selection'] += 1
            continue
        for field in band_fields:
            totals[field] += row[field]
        totals['products_with_later_skips'] += row['later_skips'] > 0
        if largest_later_saving is None or row['later_skips'] > largest_later_saving['later_skips']:
            largest_later_saving = dict(
                product=str(n), target=row['target'], first_x=row['first_x'],
                factors=[str(factor) for factor in sorted((divisor, n // divisor))],
                fermat_midpoints=row['fermat_midpoints'],
                **{field: row[field] for field in band_fields},
            )
    if totals['direct_gcds'] != totals['band_gcds'] + totals['prefix_skips'] + totals['later_skips']:
        raise ArithmeticError('inconsistent skip accounting')
    if largest_later_saving is None:
        raise ArithmeticError('the census found no product reaching the coordinate search')
    return dict(factor_bits=width, **totals, largest_later_saving=largest_later_saving)


def study():
    return [census(width) for width in range(7, 13)]


def main():
    rows = study()
    if rows != json.loads(FIXTURE.read_text()):
        raise SystemExit('first-mark census differs from the reviewed fixture')
    with TemporaryDirectory() as tmp:
        for row in rows:
            example = row['largest_later_saving']
            n = int(example['product'])
            proof = Path(tmp) / f'CircleMarkBand{n}.lean'
            proof.write_text(render_certificate(n, list(map(int, example['factors']))))
            verify_file(proof)
    print(json.dumps(rows))


if __name__ == '__main__':
    main()
