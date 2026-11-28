"""One resultant gcd for a rational rectangle, with product-only controls.

The input promise is N=pq with distinct odd primes of equal bit length. A
Jacobi-negative a is a square at one prime and a nonsquare at the other. If
I,J are smaller than both primes, every nonunit i²-a*j² therefore picks out
exactly the same prime. For a split prime r with root z, map the (I+1)(J+1)
pairs in [0,I]×[0,J] to i+z*j modulo r. If there are more than r pairs, two
collide. Their two coordinate differences are nonzero and their absolute
values give a mark in the positive rectangle. This is a sufficient condition.

The square case is already implemented in universal_norm_batch.separating_search
and formalized in NormBatchGCD.grid_gcd. Here each denominator chunk gets its
own monic subproduct/remainder tree and reuses the numerator polynomial. The
backend in wide_modulus uses carry-free packed integer multiplication and
Newton division by reversed monic polynomials over Z/N; evaluation needs no
inverse of a difference of nodes. No polynomial coefficient table is supplied.
With polynomial multiplication cost M(s), a roughly square s-by-s batch uses
O(M(s) log(2s)) ring work under the usual fast multiplication assumptions.
For J>=I, chunking costs O(ceil(J/I) M(I) log(2I)) with O(I log(2I)) stored
coefficients. The direct rectangle has up to IJ gcds. At guaranteed balanced
scale s=Theta(N**(1/4)) the classical linear interval batch also has fourth-
root scale. The deterministic target search incurs additional Jacobi tests.
"""

import argparse
import json
import platform
import sys
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from time import process_time

from experiments import wide_modulus
from experiments.circle_mark_prefix_skip import choose_target
from experiments.factorial_progressions import search as folded_interval
from experiments.short_pascal_blocks import search as tree_interval
from experiments.short_pascal_row import interval
from experiments.universal_norm_batch import modular_product, separating_search
from scripts.factor import fermat_split, primes_through, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/circle-mark-rational-grid.json'
EXAMPLE_PRODUCTS = (3127, 134271337)
FIXED_DEGREE = 8
WIDTHS = range(6, 11)


def rectangle_sizes(n):
    width = (n.bit_length() + 1) // 2
    lower, _ = interval(n)
    upper = min((1 << width) - 1, n // lower)
    side = isqrt(upper)
    # At this I, floor(U/(I+1)) is the least guaranteed denominator bound.
    fixed_denominators = max(FIXED_DEGREE, upper // (FIXED_DEGREE + 1))
    rectangles = dict(square8=(FIXED_DEGREE, FIXED_DEGREE),
                      streamed8=(FIXED_DEGREE, fixed_denominators),
                      balanced=(side, upper // (side + 1)))
    if max(max(pair) for pair in rectangles.values()) >= lower:
        raise ValueError('chosen public rectangle exceeds the small balanced-input domain')
    return rectangles


def resultant(n, a, numerators, denominators):
    """Res(F,Q) modulo N for F=prod(X-i²), Q=prod(X-a*j²)."""
    roots = [i * i % n for i in range(1, numerators + 1)]
    poly = wide_modulus.product_tree(roots, n)[-1][0]
    # P(a*j²) carries one minus sign per numerator root.
    residue = -1 if (numerators * denominators) % 2 else 1
    for first in range(1, denominators + 1, numerators):
        stop = min(first + numerators, denominators + 1)
        nodes = [a * (j * j) % n for j in range(first, stop)]
        values = wide_modulus.values_on_tree(poly, wide_modulus.product_tree(nodes, n), n)
        for value in values:
            residue = residue * value % n
    return gcd(residue, n), residue


def nested_gcds(n, a, numerators, denominators):
    squares = [i * i for i in range(1, numerators + 1)]
    for j in range(1, denominators + 1):
        node = a * j * j
        for i, square in enumerate(squares, 1):
            divisor = gcd(square - node, n)
            if divisor != 1:
                return divisor, (j - 1) * numerators + i, (i, j)
    return 1, numerators * denominators, None


@lru_cache(maxsize=None)
def polynomial_work(numerators, denominators):
    """Trace the real backend once per shape. Length control flow is data independent.

    Only array lengths are counted. The bit width and timing of the packed
    integers vary with N and are not implied by the coefficient counts.
    """
    work = Counter()
    multiply = wide_modulus.multiply.__code__
    remainder = wide_modulus.monic_remainder.__code__
    tree = wide_modulus.product_tree.__code__
    evaluate = wide_modulus.values_on_tree.__code__
    phase = 'root_tree'
    tree_count = 0

    def calls(frame, event, arg):
        nonlocal phase, tree_count
        if event != 'call':
            return
        fn = frame.f_code
        if fn is tree:
            phase = 'point_trees' if tree_count else 'root_tree'
            tree_count += 1
        elif fn is evaluate:
            phase = 'evaluation'
        elif fn is multiply:
            f, g = frame.f_locals['f'], frame.f_locals['g']
            work[phase + '_packed_multiplies'] += 1
            work['packed_input_coefficients'] += len(f) + len(g)
        elif fn is remainder:
            f, g = frame.f_locals['f'], frame.f_locals['g']
            work['remainder_calls'] += 1
            if len(f) >= len(g) == 2:
                work['horner_steps'] += len(f)

    previous = sys.getprofile()
    try:
        sys.setprofile(calls)
        resultant(3127, 3, numerators, denominators)
    finally:
        sys.setprofile(previous)
    return dict(work)


def rectangle_run(n, a, shape):
    i, j = shape
    divisor, residue = resultant(n, a, i, j)
    direct, tests, witness = nested_gcds(n, a, i, j)
    # Independent full product checks sign, every leaf and all chunk boundaries.
    literal = modular_product((u*u - a*v*v for v in range(1, j+1) for u in range(1, i+1)), n)
    if direct != divisor or divisor == n or residue != literal:
        raise ArithmeticError('resultant residue or separating gcd disagrees with direct leaves')
    batches = (j + i - 1) // i
    work = dict(numerator_squares=i, scaled_denominator_squares=j, covered_leaves=i*j,
                point_trees=batches, scalar_modular_products=j, resultant_gcds=1,
                direct_numerator_squares=i, direct_denominator_terms=(tests+i-1)//i,
                direct_gcds=tests, **polynomial_work(i, j))
    return dict(numerators=i, denominators=j, gcd=str(divisor), residue=str(residue),
                first_pair=list(witness) if witness else None, work=work)


def controls(n):
    width = (n.bit_length() + 1) // 2
    ordinary = tree_interval(n, 2, n)
    folded = folded_interval(n, None, wheel=30, folded=True, equal_width=True)
    fermat, steps = fermat_split(n, 1 << width)
    if (ordinary['remaining_candidates'] != '0' or not folded['interval_complete'] or
            any(d is None or not 1 < d < n or n % d for d in (ordinary['factor'], folded['factor'], fermat))):
        raise ArithmeticError('linear interval or midpoint control failed')
    return dict(linear_tree=dict(factor=str(ordinary['factor']), work=ordinary['work']),
                linear_folded=dict(factor=str(folded['factor']), work=folded['work']),
                fermat=dict(factor=str(fermat), work=dict(midpoints=steps, integer_square_roots=steps+1)))


def measure(n):
    shapes = rectangle_sizes(n)
    target, early = choose_target(n)
    row = dict(product=str(n), target=target, jacobi_tests=target-1,
               selector_gcds=int(early is not None), selector_factor=str(early) if early else None,
               rectangles={}, controls=controls(n))
    if early is None:
        for name, shape in shapes.items():
            row['rectangles'][name] = rectangle_run(n, target, shape)
            if name != 'square8' and row['rectangles'][name]['gcd'] == '1':
                raise ArithmeticError('public complete rectangle missed its split prime')
    return row


def products(width):
    primes = [p for p in primes_through((1 << width) - 1) if p.bit_length() == width]
    for p, q in combinations(primes, 2):
        if (p*q).bit_length() == 2*width:
            yield p*q, (p, q)


def factors_of(n, divisor):
    d = int(divisor)
    if not 1 < d < n or n % d:
        raise ValueError('invalid factor')
    return tuple(sorted((d, n//d)))


def census(width):
    selectors = Counter()
    counts = {name: Counter() for name in ('square8', 'streamed8', 'balanced')}
    reference = {name: Counter() for name in ('linear_tree', 'linear_folded', 'fermat')}
    rescued = None
    for n, labels in products(width):
        row = measure(n)
        selectors['products'] += 1
        selectors['jacobi_tests'] += row['jacobi_tests']
        selectors['selector_gcds'] += row['selector_gcds']
        for name, control in row['controls'].items():
            if factors_of(n, control['factor']) != labels:
                raise ArithmeticError('control factorization disagrees with independent labels')
            reference[name].update(control['work'])
        if row['selector_factor'] is not None:
            if factors_of(n, row['selector_factor']) != labels:
                raise ArithmeticError('selector factorization disagrees with independent labels')
            continue
        for name, result in row['rectangles'].items():
            counts[name].update(result['work'])
            if result['gcd'] == '1':
                counts[name]['misses'] += 1
            elif factors_of(n, result['gcd']) != labels:
                raise ArithmeticError('rectangle factorization disagrees with independent labels')
            else:
                counts[name]['hits'] += 1
        if row['rectangles']['square8']['gcd'] == '1' and (rescued is None or n < rescued):
            rescued = n
    return dict(factor_bits=width, selector=dict(selectors),
                rectangles={name: dict(work) for name, work in counts.items()},
                controls={name: dict(work) for name, work in reference.items()}), rescued


def certified_example(n):
    row = measure(n)
    actual = row['controls']['fermat']['factor']
    factors = factors_of(n, actual)
    if factors[0] == factors[1] or factors[0].bit_length() != factors[1].bit_length():
        raise ArithmeticError('example is outside the distinct equal-width promise')
    reported = [c['factor'] for c in row['controls'].values()]
    reported.extend(r['gcd'] for r in row['rectangles'].values() if r['gcd'] != '1')
    if row['selector_factor']:
        reported.append(row['selector_factor'])
    if any(factors_of(n, d) != factors for d in reported):
        raise ArithmeticError('product-only example methods disagree on factorization')
    if row['selector_factor'] is None:
        prior = separating_search(n, FIXED_DEGREE, row['target'])
        square = row['rectangles']['square8']
        if int(prior['side']) != FIXED_DEGREE or (prior['factor'] or 1) != int(square['gcd']):
            raise ArithmeticError('square disagrees with the repository separating-norm search')
        row['previous_square_gcd'] = square['gcd']
    row['factors'] = list(map(str, factors))
    return row


def study():
    cohorts = []
    rescues = []
    for width in WIDTHS:
        counts, first = census(width)
        cohorts.append(counts)
        if first is not None:
            rescues.append(first)
    return dict(
        population='Every distinct pair of odd w-bit primes with a 2w-bit product, for w=6..10.',
        inputs='Only N and the equal-width promise reach the searches. Each rectangle uses the first negative Jacobi target unless selection finds a divisor.',
        work='Each rectangle runs independently, with its own tree construction. Packed input coefficients count both polynomial operands; each packed multiply acts on longer integers as N and the degrees grow. Formula checks, profiling, cohort generation and certificates are outside search work.',
        controls='The odd-candidate linear tree and folded decimal wheel-30 interval both use the complete equal-width factor interval. Their native work fields are summed per cohort. Fermat counts each successive midpoint.',
        cohorts=cohorts, first_square8_miss_resolved_by_streaming=certified_example(min(rescues)),
        product_only_examples=[certified_example(n) for n in EXAMPLE_PRODUCTS])


def timed_search(n, method):
    if method == 'linear_tree':
        return tree_interval(n, 2, n)['factor']
    if method == 'linear_folded':
        return folded_interval(n, None, wheel=30, folded=True, equal_width=True)['factor']
    if method == 'fermat':
        return fermat_split(n, 1 << ((n.bit_length()+1)//2))[0]
    a, factor = choose_target(n)
    if factor is not None:
        return factor
    algorithm, name = method.split(':')
    shape = rectangle_sizes(n)[name]
    if algorithm == 'resultant':
        return resultant(n, a, *shape)[0]
    return nested_gcds(n, a, *shape)[0]


def timing(trials):
    if trials < 1:
        raise ValueError('expected a positive trial count')
    cases = list(products(max(WIDTHS)))
    names = ('resultant:balanced', 'nested_gcds:balanced', 'linear_tree', 'linear_folded',
             'fermat', 'resultant:streamed8', 'nested_gcds:streamed8')
    result = []
    for trial in range(trials):
        order = names[trial % len(names):] + names[:trial % len(names)]
        times = {}
        for name in order:
            start = process_time()
            found = [timed_search(n, name) for n, _ in cases]
            times[name] = round(process_time()-start, 6)
            if any(factors_of(n, d) != labels for (n, labels), d in zip(cases, found)):
                raise ArithmeticError('timed search gave an incorrect factor')
        result.append(times)
    return dict(factor_bits=max(WIDTHS), products=len(cases), python=platform.python_version(),
                machine=platform.machine(), system=platform.system(), cpu_seconds=result,
                scope='Search and public setup per product. Excludes input generation, validation and profiling.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timing', action='store_true', help='time the complete 10-bit cohort')
    parser.add_argument('--trials', type=int, default=3)
    args = parser.parse_args()
    if args.timing:
        print(json.dumps(timing(args.trials), indent=2))
        return
    data = study()
    if data != json.loads(FIXTURE.read_text()):
        raise SystemExit('rational-grid measurements differ from the fixture')
    examples = [data['first_square8_miss_resolved_by_streaming'], *data['product_only_examples']]
    with TemporaryDirectory() as temp:
        for row in examples:
            n = int(row['product'])
            path = Path(temp) / f'RationalGrid{n}.lean'
            path.write_text(render_certificate(n, list(map(int, row['factors']))))
            verify_file(path)
    print(f"Checked {sum(row['selector']['products'] for row in data['cohorts'])} products and {len(examples)} Lean certificates.")


if __name__ == '__main__':
    main()
