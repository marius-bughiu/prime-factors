"""Bounded comparison of factor-sum residues on the same public modulus and interval."""

import argparse
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.reciprocal_anchor import find_anchor, jacobi, oriented, progressions, sum_bounds
from scripts.factor import render_certificate, verify_file


# Existing public inputs chosen to illustrate prime and composite periods. The
# search receives the product, public equal bit width, and continued-fraction budget.
EXAMPLES = ((135137, 9, 32), (137649271, 14, 128), (140188063, 14, 4), (2218279573, 16, 32))
WHEEL = 60


def odd_discriminant_table(n, d):
    """A square-residue lookup for every sum, counting reflected roots exactly once."""
    squares = set()
    roots = 0
    for r in range(d // 2 + 1):
        square = r*r % d
        squares.add(square)
        if square == n % d:
            roots += 1 if r == 0 else 2
    sums = {s for s in range(d) if (s*s - 4*n) % d in squares}
    return sums, dict(root_candidates=d//2+1, distinct_squares=len(squares),
                      roots_of_product=roots, sum_residues_tested=d)


def positive_orbits(n, d):
    """Jacobi is opposite on ±x; swapping x with N/x leaves the sum unchanged."""
    sums = set()
    inversions = 0
    representatives = 0
    for x in range(1, d//2 + 1):
        symbol = jacobi(x, d)
        if symbol == 0:
            continue
        positive = x if symbol == 1 else d-x
        partner = n*pow(positive, -1, d) % d
        inversions += 1
        if positive <= partner:
            representatives += 1
            sums.add((positive+partner) % d)
    return sums, dict(jacobi_calls=d//2, inversions=inversions, representatives=representatives)


def lifted_candidates(n, low, high, wheel_rows, modulus, residues, inverse):
    """CRT merge, then visit only sums inside the common interval, in ascending order."""
    lifted = {w + WHEEL*((s-w)*inverse % modulus) for w in wheel_rows for s in residues}
    rows = progressions(low, high, lifted, WHEEL*modulus)
    candidates = sorted(first+j*WHEEL*modulus for first, length in rows for j in range(length))
    hits = []
    for index, s in enumerate(candidates, 1):
        delta = s*s-4*n
        gap = isqrt(delta)
        if gap*gap == delta and (s-gap) % 2 == 0:
            p, q = (s-gap)//2, (s+gap)//2
            if p > 1 and p*q == n:
                hits.append(dict(rank=index, factors=[str(p), str(q)]))
    return candidates, dict(crt_pairs=len(wheel_rows)*len(residues), square_tests=len(candidates),
                            hits=hits)


def comparison(n, bits, budget):
    if n % 2 == 0 or gcd(n, WHEEL) != 1:
        raise ValueError('the reference wheel requires a product coprime to 60')
    low, _, high = sum_bounds(n, bits)
    anchor = find_anchor(n, budget, WHEEL)
    if anchor and 'setup_factor' in anchor:
        raise ValueError('the common setup already factored this input')
    if not anchor or anchor['period'] > 10000:
        raise ValueError('the example needs an anchor of period at most 10000')
    d, e = anchor['period'], anchor['root']
    if (anchor['minus_root']**2+d) % n or (e*e-n) % d or gcd(d, n*WHEEL) != 1 or d%4 != 3:
        raise ArithmeticError('invalid public anchor')
    baseline, root_work = odd_discriminant_table(n, d)
    positive, orbit_work = positive_orbits(n, d)
    # Independent exhaustive checks, outside the two priced methods.
    units = [x for x in range(d) if gcd(x, d) == 1]
    pairs = {(x+n*pow(x, -1, d)) % d for x in units}
    offset_signs = {s for s in range(d) if jacobi(s-2*e,d) >= 0 and jacobi(s+2*e,d) >= 0}
    if pairs != baseline or not positive <= (baseline & offset_signs):
        raise ArithmeticError('the same-modulus reference sets disagree')
    if len(baseline) != 2*len(positive):
        raise ArithmeticError('the two local signs failed to bisect the ordinary image')
    oriented_classes = {s for s in range(d) if oriented(s, d, e)}
    if (oriented_classes & baseline) != positive or len(oriented_classes)*2 != d-1:
        raise ArithmeticError('the pointwise selector failed its full-period cross-check')
    wheel_units = [x for x in range(WHEEL) if gcd(x,WHEEL) == 1]
    wheel_rows = {(x+n*pow(x,-1,WHEEL)) % WHEEL for x in wheel_units}
    inverse = pow(WHEEL,-1,d)
    ordinary_candidates, ordinary_run = lifted_candidates(n,low,high,wheel_rows,d,baseline,inverse)
    positive_candidates, positive_run = lifted_candidates(n,low,high,wheel_rows,d,positive,inverse)
    cheap = [s for s in ordinary_candidates if s%d in offset_signs]
    if not set(positive_candidates) <= set(cheap):
        raise ArithmeticError('the CRT refinements disagree')
    ordinary_hits = [h['factors'] for h in ordinary_run['hits']]
    positive_hits = [h['factors'] for h in positive_run['hits']]
    if ordinary_hits != positive_hits or len(positive_hits) != 1:
        raise ArithmeticError('the complete bounded searches did not recover the same split')
    return dict(n=str(n), bits=n.bit_length(), interval=[low,high], period=d,
                anchor_scan=budget, anchor_replay=anchor['step'], minus_root=anchor['minus_root'],
                root=e, wheel_residues=len(wheel_rows),
                wheel_candidates=sum(length for _,length in progressions(low,high,wheel_rows,WHEEL)),
                units=len(units), orbit_ceiling=(len(units)+root_work['roots_of_product'])//4,
                ordinary_classes=len(baseline), positive_classes=len(positive),
                oriented_classes=len(oriented_classes), sign_classes=len(offset_signs), ordinary_and_sign_classes=len(baseline & offset_signs),
                ordinary_and_sign_candidates=len(cheap), root_work=root_work, orbit_work=orbit_work,
                ordinary=ordinary_run, positive=positive_run)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='also generate and Lean-check the splits')
    args = parser.parse_args()
    for n,bits,steps in EXAMPLES:
        result = comparison(n,bits,steps)
        if args.verify:
            path = Path('build/reciprocal-anchor-comparison') / f'Factor{n}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            factors = [int(x) for x in result['positive']['hits'][0]['factors']]
            path.write_text(render_certificate(n,factors))
            verify_file(path)
            result['verified'] = True
        print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
