"""Locate two public weighted labels near each chosen stationary point."""

import hashlib
import json
from collections import Counter
from math import gcd, isqrt
from pathlib import Path

from experiments.quotient_strip_levels import chord_levels, schedule
from experiments.quotient_strip_localization import holdout_cohort


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/quotient-strip-stationary.json'
ROOT = FIXTURE.parents[1]


def fibonacci_pair(index):
    a, b = 0, 1
    for _ in range(index):
        a, b = b, a+b
    return a, b


PAIRS = (
    ('1,1', 1, 1),
    ('2,1', 2, 1),
    ('1,2', 1, 2),
    ('F229,F230', *fibonacci_pair(229)),
    ('2^327-1,2^327', 2**327-1, 2**327),
)


def fixture_row(name, input_id):
    rows = json.loads((ROOT/'benchmarks'/name).read_text())
    return next(row for row in rows if row['id'] == input_id)


def residue_classes(n, u, v):
    """Independent enumeration of possible weighted residues of xy=N modulo 24."""
    local = {(u*x+v*y) % 24 for x in range(24) for y in range(24) if (x*y-n) % 24 == 0}
    exact = {z for z in range(24) if gcd(z, 24) == gcd(u+n*v, 24)}
    if gcd(n, 24) != 1 or local != exact:
        raise ArithmeticError('Exact weighted residues disagree with local multiplication')
    return local


def recover(n, a, b, u, v, z, work):
    """Solve the weighted quadratic and verify both pair entries on a square."""
    disc = z*z-4*u*v*n
    if disc <= 0:
        raise ArithmeticError('Expected a strictly positive discriminant')
    work['square_tests'] += 1
    root = isqrt(disc)
    if not root*root <= disc < (root+1)**2:
        raise ArithmeticError('Incorrect integer square root')
    if root*root != disc:
        work['positive_nonsquares'] += 1
        return []
    pairs = []
    for numerator in {z-root, z+root}:
        x, remainder = divmod(numerator, 2*u)
        if remainder or not a <= x <= b:
            continue
        y, remainder = divmod(n, x)
        if not remainder and x*y == n and u*x+v*y == z:
            pairs.append((x, y))
    return sorted(pairs)


def locate(n, origin, stop, width, u, v, z, work):
    """Try the block containing the floored left root, then its immediate neighbors."""
    disc = z*z-4*u*v*n
    if disc <= 0:
        raise ArithmeticError('Chosen weighted line must intersect the real hyperbola')
    work['location_square_roots'] += 1
    root_column = (z-(isqrt(disc-1)+1))//(2*u)
    # These inequalities independently characterize floor((z-sqrt(disc))/(2u)).
    left = z-2*u*root_column
    following = left-2*u
    if left < 0 or left*left < disc or (following >= 0 and following*following >= disc):
        raise ArithmeticError('Computed column does not bracket the left real root')
    index = (root_column-origin)//width
    for shift in (0, -1, 1):
        j = index+shift
        a = origin+j*width
        b = a+width-1
        if j < 0 or b > stop:
            continue
        work['blocks_examined'] += 1
        actual_u, actual_v, low, high = chord_levels(n, a, b, False, work)
        if (actual_u, actual_v) != (u, v) or not low <= z <= high:
            continue
        if z % 24 not in residue_classes(n, u, v):
            raise ArithmeticError('Chosen label should have a compatible residue')
        pairs = recover(n, a, b, u, v, z, work)
        return (j, a, b, z, low, high, disc, pairs, shift)
    raise ArithmeticError('The chosen label was absent around its public real root')


def full_control(input_id, n, clipped):
    origin, stop, width = schedule(n)
    if clipped:
        origin = max(origin, 2**1023, (n-1)//(2**1024-1)+1)
    if n.bit_length() != 2048 or 400*origin**2 > 289*n:
        raise ArithmeticError('Input does not meet the selected schedule origin bound')
    r = width//2
    work = Counter()
    examples, selected = [], []
    digest = hashlib.sha256()
    for name, i, j in PAIRS:
        u, v = 4*i+5*j, 3*i+4*j
        if gcd(i, j) != 1 or gcd(u, v) != 1 or not 7 <= v <= r//2048:
            raise ArithmeticError('Direction outside the proved family')
        work['stationary_label_square_roots'] += 1
        radicand = 4*u*v*n
        floor_minimum = isqrt(radicand)
        first = floor_minimum+1 if floor_minimum**2 == radicand else floor_minimum+2
        first += (u+v*n-first) % 24
        rows = [locate(n, origin, stop, width, u, v, z, work) for z in (first, first+24)]
        if rows[0][0] == rows[1][0]:
            raise ArithmeticError('Distinct weighted labels should belong to different strips')
        for row in rows:
            index, a, b, z, low, high, disc, pairs, shift = row
            digest.update(f'{i} {j} {index} {a} {b} {z} {low} {high} {disc}\n'.encode('ascii'))
            selected.append((a, b, u, v, z, pairs))
        examples.append(dict(pair=name, label_mod24=first % 24,
                             offsets_above_floor_minimum=[first-floor_minimum, first+24-floor_minimum],
                             raw_label_counts=[row[5]-row[4]+1 for row in rows],
                             neighboring_block_offsets=[row[8] for row in rows]))
    if len({(a,b) for a,b,_,_,_,_ in selected}) != len(selected):
        raise ArithmeticError('Two different designated directions were assigned to one strip')
    result = dict(input_id=input_id, schedule='1024-bit clipped' if clipped else 'balanced',
                  width_bits=width.bit_length(), public_rows_sha256=digest.hexdigest(),
                  distinct_blocks=len(selected), examples=examples, work=dict(work))
    return result, selected


def duplicate_control():
    n = 346597
    origin, _, width = schedule(n)
    work = Counter()
    examples, selected = [], []
    for j in (3, 4):
        a = origin+j*width
        b = a+width-1
        u, v, low, high = chord_levels(n, a, b, False, work)
        residues = residue_classes(n, u, v)
        labels = [z for z in range(low, high+1) if z % 24 in residues]
        if (u,v) != (3,2) or labels != [2885]:
            raise ArithmeticError('Unexpected toy direction or residue screening')
        z = labels[0]
        disc = z*z-4*u*v*n
        pairs = recover(n, a, b, u, v, z, work)
        examples.append(dict(index=j, bounds=[a,b], raw_labels=[low,high], label=z,
                             discriminant=disc, discriminant_floor_root=isqrt(disc)))
        selected.append((a,b,u,v,z,pairs))
    return dict(product=str(n), source='quotient-strip holdout index 57',
                direction=[3,2], compatible_residues=sorted(residues), examples=examples), selected


def check_selected(n, rows, factors):
    p,q = sorted(factors)
    if p*q != n or 4*q > 5*p:
        raise ArithmeticError('Factor labels disagree with input or before-hit ratio')
    for a,b,u,v,z,got in rows:
        expected = sorted((x,y) for x,y in ((p,q),(q,p)) if a <= x <= b and u*x+v*y == z)
        if got != expected or b >= p:
            raise ArithmeticError('Publicly chosen block disagrees with the certificate')


def study():
    fresh_id = 'endpoint-offset-fresh-2048'
    gap_id = 'gap-stride-2048'
    fresh_n = int(fixture_row('endpoint-offset-product.json',fresh_id)['n'])
    gap_n = int(fixture_row('gap-stride.json',gap_id)['n'])
    fresh, fresh_rows = full_control(fresh_id, fresh_n, False)
    gap, gap_rows = full_control(gap_id, gap_n, True)
    toy, toy_rows = duplicate_control()

    # Consult the expected primes after selecting every example and solving its label.
    chains = json.loads((ROOT/'research/certified-control.json').read_text())['chains']
    fresh_factors = [int(chain[-1]['prime']) for chain in chains.values()]
    gap_factors = [int(p) for p in fixture_row('gap-stride.json',gap_id)['factors']]
    check_selected(fresh_n, fresh_rows, fresh_factors)
    check_selected(gap_n, gap_rows, gap_factors)
    check_selected(int(toy['product']), toy_rows, holdout_cohort()[57])
    return dict(selection='Five fixed primitive pairs. For each choose the first label in class u+Nv modulo 24 at or above ceil(sqrt(4uvN))+1 and the label 24 higher. Locate each left real root directly and replay the actual chord selector. The small duplicate illustrates the same discriminant in two scheduled blocks.',
                scope='Only the displayed blocks were visited. Selection, direction, residue and discriminant checks use the input alone. Known primes check the answers and stopping positions after selection.',
                digest_format='SHA-256 of one ASCII line per selected row in pair/label order: i j block_index a b z low high discriminant, separated by spaces and terminated by LF.',
                controls=[fresh,gap], duplicate=toy)


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Stationary label results differ from the reviewed fixture')
    print('Verified 20 full-size stationary labels and the repeated toy discriminant.')
