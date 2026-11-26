"""A bounded product-only search for cubic square relations.

Replay `python3 -m experiments.cubic_trace_search --check --verify` to verify
all recorded public computations and a Lean prime-factor certificate per split.
"""

import argparse
from collections import Counter
from itertools import product
import json
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory
from time import process_time_ns

from .affine_radix_holdout import draw_prime
from .cubic_trace_roots import readout
from .gap_coverage import primes_through
from .offset_tangent_cover import cube_root
from .pell_relations import insert_parity
from .polynomial_relations import search as quadratic_search


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'research/cubic-trace-panel.json'
SEED = b'cubic-trace-panel-v1'
BOUND = 127
PRIMES = tuple(primes_through(BOUND))
CHAR_PRIMES = tuple(p for p in primes_through(1021) if p > BOUND)
def primitive_rows(a_limit, b_limit):
    return tuple((a, b) for b, a in product(range(1, b_limit+1), range(-a_limit, a_limit+1)) if gcd(a, b) == 1)


POINTS = primitive_rows(40, 8)
OFFSETS = (0, 1, -1, 2, -2, 3, -3, 4, -4)
TRACE_CAP = 32


def evaluate(f, x):
    c, b, a = f
    return ((x+a)*x+b)*x+c


def select_polynomial(n, work):
    base = cube_root(n)
    for offset in OFFSETS:
        m = base + offset
        if m < 2:
            continue
        remaining = n - m**3
        digits = []
        for _ in range(2):
            digit = (remaining + m//2) % m - m//2
            digits.append(digit)
            remaining = (remaining-digit)//m
        f = (*digits, remaining)
        if evaluate(f, m) != n:
            raise ArithmeticError('balanced-base polynomial identity failed')
        work['polynomials_tried'] += 1
        for p in PRIMES:
            if p > 97:
                break
            for t in range(p):
                work['irreducibility_residues'] += 1
                if evaluate(f, t) % p == 0:
                    break
            else:
                return m, f, p
    return None


def multiply_by_alpha(f, x):
    c, b, a = f
    i, j, k = x
    return (-c*k, i-b*k, j-a*k)


def characteristic(f, element):
    u = element
    v = multiply_by_alpha(f, u)
    w = multiply_by_alpha(f, v)
    trace = u[0] + v[1] + w[2]
    middle = u[0]*v[1] + u[0]*w[2] + v[1]*w[2] - u[1]*v[0] - u[2]*w[0] - v[2]*w[1]
    norm = (u[0]*(v[1]*w[2]-v[2]*w[1]) - v[0]*(u[1]*w[2]-u[2]*w[1])
            + w[0]*(u[1]*v[2]-u[2]*v[1]))
    return trace, middle, norm


def smooth_parity(x, work):
    if x == 0:
        return None
    mask, x = int(x < 0), abs(x)
    for i, p in enumerate(PRIMES, 1):
        if x == 1:
            break
        work['trial_prime_visits'] += 1
        while x % p == 0:
            x //= p
            mask ^= 1 << i
            work['exact_prime_divisions'] += 1
    return mask if x == 1 else None


def collect(m, f, points, work):
    rows = []
    c0, c1, c2 = f
    for a, b in points:
        rational = a+b*m
        norm = a**3-c2*a*a*b+c1*a*b*b-c0*b**3
        rm = smooth_parity(rational, work)
        nm = smooth_parity(norm, work)
        work['rational_smooth'] += int(rm is not None)
        work['norm_smooth'] += int(nm is not None)
        if rm is not None and nm is not None:
            rows.append((a, b, rational, norm, rm | (nm << (len(PRIMES)+1))))
    return rows


def character_places(f, work):
    c, b, a = f
    discriminant = a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c
    places = []
    for p in CHAR_PRIMES:
        work['character_primes_tried'] += 1
        if discriminant % p == 0:
            continue
        for x in range(p):
            work['character_root_residues'] += 1
            if evaluate(f, x) % p == 0:
                places.append((p, x))
                break
        if len(places) == 8:
            break
    return places


def character_word(row, places, work):
    a, b = row[:2]
    word = 0
    for j, (p, x) in enumerate(places):
        value = (a+b*x) % p
        if value == 0:
            raise ArithmeticError('a prime larger than the smoothness bound divides a retained norm')
        work['euler_criterion_powers'] += 1
        word |= int(pow(value, (p-1)//2, p) != 1) << j
    return word


def kernels(rows, words, bits):
    pivots, basis = {}, []
    for i, (row, word) in enumerate(zip(rows, words)):
        extension = (word & ((1 << bits)-1)) << (2*(1+len(PRIMES)))
        dep = insert_parity(pivots, row[4] | extension, 1 << i)
        if dep is not None:
            basis.append(dep)
    return basis


def check_subset(n, m, f, rows, mask):
    chosen = [row for i, row in enumerate(rows) if mask >> i & 1]
    rational = prod(row[2] for row in chosen)
    norm = prod(row[3] for row in chosen)
    z = isqrt(rational)
    if z*z != rational or isqrt(norm)**2 != norm:
        raise ArithmeticError('dependency parity did not give the two asserted squares')
    beta = (1, 0, 0)
    for a, b, *_ in chosen:
        alpha_beta = multiply_by_alpha(f, beta)
        beta = tuple(a*i+b*j for i, j in zip(beta, alpha_beta))
    a, b, c = characteristic(f, beta)
    if c != norm or (beta[0]+m*beta[1]+m*m*beta[2]-rational) % n:
        raise ArithmeticError('cubic norm or specialization identity failed')
    result = readout(n, z, a, b, c)
    return result, {'rows': [list(row[:2]) for row in chosen], 'beta': list(map(str, beta)),
                    'abc': list(map(str, (a, b, c))), 'rational_root': str(z)}


def compare_arm(n, m, f, rows, basis, bits, cap):
    total = (1 << len(basis))-1
    tested = min(cap, total)
    work = Counter({key: 0 for key in ('true_squares', 'false_squares', 'scalar_squares',
                   'rootless_mod5', 'isolation_nodes', 'gcd_tests', 'proper_hits', 'row_multiplications')})
    mask, first = 0, None
    for index in range(1, tested+1):
        mask ^= basis[(index & -index).bit_length()-1]
        result, witness = check_subset(n, m, f, rows, mask)
        square = bool(result['witnesses'])
        work['true_squares' if square else 'false_squares'] += 1
        work['scalar_squares'] += int(result['status'] == 'scalar_square')
        work['rootless_mod5'] += int(result['work']['mod5_root_mask'] == 0)
        work['isolation_nodes'] += result['work']['integer_root_nodes']
        work['gcd_tests'] += 2*len(result['probes'])
        work['row_multiplications'] += bin(mask).count('1')
        if result['proper_divisors']:
            work['proper_hits'] += 1
            if first is None:
                divisor = result['proper_divisors'][0]
                first = dict(witness, check=index, divisors=list(map(str, sorted((divisor, n//divisor)))),
                             traces=result['roots'], probes=result['probes'], field_roots=result['witnesses'])
    return {'bits': bits, 'kernel_dimension': len(basis), 'matrix_rank': len(rows)-len(basis),
            'tested': tested, 'remaining_dependencies': str(total-tested), **work, 'first_hit': first}


def search(n, *, trace_cap=TRACE_CAP, a_limit=40, b_limit=8, timing=None):
    if n <= 1 or trace_cap < 0 or a_limit < 1 or b_limit < 1:
        raise ValueError('expected n>1, a nonnegative trace cap and positive row limits')
    started = process_time_ns()
    work = Counter({key: 0 for key in ('polynomials_tried', 'irreducibility_residues', 'rational_smooth',
                   'norm_smooth', 'trial_prime_visits', 'exact_prime_divisions', 'character_primes_tried',
                   'character_root_residues', 'euler_criterion_powers')})
    selected = select_polynomial(n, work)
    if selected is None:
        return {'status': 'no_irreducibility_certificate', 'remaining_cofactor': str(n),
                'work': dict(work), 'arms': []}
    m, f, prime = selected
    points = primitive_rows(a_limit, b_limit)
    rows = collect(m, f, points, work)
    base_kernel = kernels(rows, [0]*len(rows), 0)
    # Additional parity constraints cannot create a new dependency. Skip their
    # setup entirely when the existing signed norm/rational kernel is empty.
    places = character_places(f, work) if base_kernel else []
    words = [character_word(row, places, work) for row in rows]
    if timing is not None:
        timing['cubic_setup_ns'] = process_time_ns()-started
        timing['cubic_arms_ns'] = {}
    arms = []
    for bits in (0, 4, 8):
        if base_kernel and len(places) < bits:
            continue
        before = process_time_ns()
        basis = kernels(rows, words, bits) if bits and base_kernel else base_kernel
        arms.append(compare_arm(n, m, f, rows, basis, bits, trace_cap))
        if timing is not None:
            timing['cubic_arms_ns'][str(bits)] = process_time_ns()-before
    split = next((a['first_hit']['divisors'] for a in arms if a['first_hit']), None)
    status = 'split' if split else ('no_proper_split' if base_kernel else 'no_norm_dependency')
    return {'status': status, 'remaining_cofactor': '1' if split else str(n),
            'm': str(m), 'f_ascending_monic': [str(c) for c in (*f, 1)],
            'irreducibility_prime': prime, 'candidate_rows': len(points), 'smooth_rows': len(rows),
            'available_character_places': [list(place) for place in places], 'work': dict(work), 'arms': arms}


def baseline(n, positions):
    # Centered single-polynomial entry point accepts an odd number of sites.
    result = quadratic_search(n, 'centered', bound=BOUND, radius=(positions-1)//2, blocks=1)
    factor = result['factor']
    policy = result['policies'].get('base', {})
    return {'positions_budget': 2*((positions-1)//2)+1, 'positions': result['positions'],
            'smooth_rows': result['smooth_rows'], 'sieve_marks': result['sieve_marks'],
            'prime_divisions': result['prime_divisions'], 'kernel_dimension': policy.get('dependencies', 0),
            'gcd_tests': policy.get('gcd_tests', 0), 'remaining_cofactor': '1' if factor else str(n),
            'outcome': result['outcome'], 'divisors': sorted((str(factor), str(n//factor)), key=int) if factor else []}


def cohort(bits, count, seed=SEED):
    samples, idx = [], 0
    while len(samples) < count:
        p, q = sorted(draw_prime(side, idx, bits=(bits+1)//2, seed=seed) for side in (b'p', b'q'))
        if p != q and (p*q).bit_length() == bits:
            samples.append((idx, p, q))
        idx += 1
    return samples


def run_case(name, n, index=None, *, a_limit=40, b_limit=8, timings=None):
    timing = {} if timings is not None else None
    before = process_time_ns()
    details = search(n, a_limit=a_limit, b_limit=b_limit, timing=timing)
    after = process_time_ns()
    quadratic = baseline(n, len(primitive_rows(a_limit, b_limit)))
    if timings is not None:
        timing.update(cubic_total_ns=after-before, quadratic_total_ns=process_time_ns()-after)
        timings[name] = timing
    return {'id': name, 'draw_index': index, 'n': str(n), 'cubic': details, 'quadratic': quadratic}


def found(row):
    hits = {tuple(map(int, a['first_hit']['divisors'])) for a in row['cubic']['arms'] if a['first_hit']}
    if row['quadratic']['divisors']:
        hits.add(tuple(map(int, row['quadratic']['divisors'])))
    return hits


def panel(*, timed=False):
    rows = []
    timings = {} if timed else None
    for bits, size in ((31, 4), (39, 4), (79, 1)):
        for i, (idx, p, q) in enumerate(cohort(bits, size)):
            row = run_case(f'holdout-{bits}-{i+1}', p*q, idx, timings=timings)
            if any(h != (p, q) for h in found(row)):
                raise ArithmeticError('discovered split differs from independent sample labels')
            rows.append(row)
    controls = json.loads((ROOT/'benchmarks/arbitrary-divisor-window.json').read_text())
    ids = {'arbitrary-divisor-window-fresh-2048', 'arbitrary-divisor-window-crossed-2048'}
    for case in controls:
        if case['id'] in ids:
            rows.append(run_case(case['id'], int(case['n']), timings=timings))
    rows.append(run_case('public-base-989', 989, timings=timings))
    expanded_seed = b'cubic-trace-panel-expanded-v1'
    expanded = []
    for group, seed in (('original', SEED), ('fresh', expanded_seed)):
        for i, (idx, p, q) in enumerate(cohort(31, 4, seed=seed)):
            row = run_case(f'expanded-{group}-31-{i+1}', p*q, idx, a_limit=80, b_limit=16, timings=timings)
            if any(h != (p, q) for h in found(row)):
                raise ArithmeticError('expanded product split differs from sample')
            expanded.append(row)
    sensitivity = []
    for bits in (31, 39):
        (idx, p, q), = cohort(bits, 1)
        row = run_case(f'sensitivity-{bits}-1', p*q, idx, a_limit=160, b_limit=32, timings=timings)
        if any(h != (p, q) for h in found(row)):
            raise ArithmeticError('sensitivity product split differs from sample')
        sensitivity.append(row)
    return {'seed': SEED.decode(), 'cohorts': {'31': 4, '39': 4, '79': 1}, 'first_base_offsets': list(OFFSETS),
            'prime_bound': BOUND, 'character_arms': [0, 4, 8], 'trace_budget_per_arm': TRACE_CAP,
            'candidate_rectangle': {'a': [-40,40], 'b': [1,8], 'primitive_rows': len(POINTS)},
            'rows': rows, 'expanded': {'fresh_seed': expanded_seed.decode(), 'a_limit': 80, 'b_limit': 16, 'rows': expanded},
            'sensitivity': {'a_limit': 160, 'b_limit': 32, 'rows': sensitivity}, 'timing_cpu_ns': timings,
            'supplied_989_examples': {
                'm': 10, 'f': [-11, 0, 0, 1], 'true_rows': [[-2,1],[-2,3],[4,1]],
                'false_rows': [[2,1],[-5,2],[-10,3]],
                'true': readout(989, 56, *characteristic((-11,0,0), (49,-28,4))),
                'false': readout(989, 60, *characteristic((-11,0,0), (166,-20,-23)))}}


def verify_splits(report):
    from scripts.factor import render_certificate, verify_file
    facts = {(int(row['n']), h) for row in report['rows'] + report['expanded']['rows'] + report['sensitivity']['rows'] for h in found(row)}
    facts.add((989, tuple(report['supplied_989_examples']['true']['proper_divisors'])))
    with TemporaryDirectory() as temp:
        path = Path(temp)/'CubicPanelFactor.lean'
        for n, pair in sorted(facts):
            path.write_text(render_certificate(n, list(pair)))
            verify_file(path)
    return len(facts)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--verify', action='store_true', help='kernel check primality and the product for every claimed split')
    args = parser.parse_args()
    result = panel(timed=not args.check)
    if args.check:
        archived = json.loads(OUTPUT.read_text())
        archived['timing_cpu_ns'] = None
        if archived != result:
            raise SystemExit('cubic trace panel differs from the frozen output')
        print('Checked initial, expanded and sensitivity panels and both supplied 989 row triples.')
    if args.verify:
        print(f'Verified {verify_splits(result)} distinct factorization certificates.')
    if not args.check and not args.verify:
        print(json.dumps(result, indent=2))
