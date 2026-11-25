"""Search primitive offset positions with separately chosen dyadic charts."""

import argparse
from itertools import product
import json
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from experiments.offset_crt_reconstruction import search as search_odd_wheel
from experiments.offset_crt_wheel import cheapest_subset, choose_wheel
from experiments.offset_prime_power_slopes import local_directions, reconstruct
from scripts.factor import certificate_witness, render_certificate, verify_file


def forward_count(n, exponent):
    """Size of the odd-unit sumset modulo 2**exponent, independent of its shift.

    Bower, Evans, Luo and Miller, Theorem 3.3, https://arxiv.org/abs/1212.2930.
    """
    if n % 2 == 0 or exponent < 1:
        raise ValueError('expected odd product and positive dyadic exponent')
    if exponent < 3:
        return 1
    if exponent == 3:
        return 2 if n % 4 == 1 else 1
    if exponent == 4:
        return 2
    modulus = 2**exponent
    if n % 8 in (3, 7):
        return modulus // 8
    if n % 8 == 5:
        return modulus // 16
    correction = 1 if exponent % 2 else -1
    return (modulus // 16 + correction) // 3 + 3


def select_charts(n, j_limit, k_limit, max_exponent):
    """Minimize the forward and reverse reconstruction costs in the same odd menu."""
    base = choose_wheel(n, j_limit, k_limit)
    if base['factor'] is not None:
        return dict(factor=base['factor'], work=base['work'])
    fixed, free = base['fixed'], base['free']
    costs = {p: (p + (3 if pow(n, (p-1)//2, p) == 1 else 1)) // 2 for p in (*fixed, *free)}
    fixed_cost, fixed_modulus = prod(costs[p] for p in fixed), prod(fixed)
    best = {}
    work = dict(base['work'])
    work['euler_tests'] += len(costs)
    work['selection_tables'] = 1
    work['half_subsets'] = work['left_subsets'] + work['right_subsets']
    for exponent in range(1, max_exponent + 1):
        dyadic = 2**exponent
        extra, cost, modulus, selection = cheapest_subset(
            free, costs, base['threshold'] // (dyadic * fixed_modulus))
        work['selection_tables'] += 1
        for counter in ('left_subsets', 'right_subsets', 'threshold_queries', 'feasible_queries'):
            work[counter] += selection[counter]
        work['half_subsets'] = work['left_subsets'] + work['right_subsets']
        total_modulus = modulus * fixed_modulus * dyadic
        if total_modulus <= base['threshold']:
            raise ArithmeticError('dyadic wheel did not reach the reconstruction threshold')
        for chart, directions in [('forward', forward_count(n, exponent)), ('reverse', dyadic//2)]:
            total = directions * fixed_cost * cost
            if chart not in best or total < best[chart]['total_tuples']:
                best[chart] = dict(exponent=exponent, dyadic_labels=directions,
                                   primes=sorted((*fixed, *extra)), modulus=total_modulus,
                                   total_tuples=total)
    return dict(factor=None, odd_only_tuples=base['total_tuples'], charts=best, work=work)


def chart_directions(n, t, chart, exponent):
    """Normalized projective entries in the selected dyadic chart."""
    modulus = 2**exponent
    if chart == 'forward':
        residues = sorted({(x + n*pow(x, -1, modulus) - 2*t) % modulus
                           for x in range(1, modulus, 2)})
        return [(r, 1) for r in residues]
    if chart == 'reverse':
        return [(1, b) for b in range(0, modulus, 2)]
    raise ValueError('unknown dyadic chart')


def scan_chart(n, t, h, j_limit, k_limit, chart, plan, odd_masks, budget):
    """Enumerate chart labels in increasing order, then odd-prime labels in prime order."""
    modulus = 2**plan['exponent']
    dyadic = chart_directions(n,t,chart,plan['exponent'])
    masks = [dyadic, *(odd_masks[p] for p in plan['primes'])]
    if len(dyadic) != plan['dyadic_labels'] or prod(map(len, masks)) != plan['total_tuples']:
        raise ArithmeticError('enumerated masks disagree with the selected tuple count')
    moduli = [modulus, *plan['primes']]
    visits = reconstructed = square_tests = 0
    hits = []
    # The integer budget may be larger than Py_ssize_t on a full-size fixture.
    for directions in product(*masks):
        if visits >= budget:
            break
        visits += 1
        pair = reconstruct(moduli, directions, j_limit, k_limit)
        if pair is None:
            continue
        j, k = pair
        if k > t*j//h + 1:
            continue
        reconstructed += 1
        delta = j*j + 4*k*(t*j-h*k)
        if delta < 0:
            continue
        square_tests += 1
        root = isqrt(delta)
        if root*root == delta:
            factor = gcd(n, (j+2*t*k-root)//2)
            if 1 < factor < n:
                hits.append(dict(j=j, k=k, factor=factor))
    return dict(**plan, visited_tuples=visits, unchecked_tuples=plan['total_tuples']-visits,
                reconstructed=reconstructed, square_tests=square_tests, hits=hits)


def search(n, max_per_chart, *, max_exponent=20):
    """Spend up to max_per_chart tuples on each chart, continuing after a hit."""
    if not 4 <= n < 2**2048 or max_per_chart < 0 or not 1 <= max_exponent <= 20:
        raise ValueError('expected 4 <= N < 2^2048, nonnegative budget, and 1..20 exponent')
    t = isqrt(n)
    h = n-t*t
    result = dict(status='partial', factor=None, remaining=n, odd_only_tuples=0, total_tuples=0,
                  visited_tuples=0, unchecked_tuples=0, reconstructed=0, square_tests=0,
                  proper_hits=0, charts={}, setup_work={})
    if h == 0 or n % 2 == 0:
        factor = t if h == 0 else 2
        result.update(status='square' if h == 0 else 'trial-split', factor=factor, remaining=n//factor)
        return result
    j_limit = isqrt(4*h//3)
    k_limit = t*j_limit//h + 1
    selection = select_charts(n, j_limit, k_limit, max_exponent)
    result['setup_work'] = selection['work']
    if selection['factor'] is not None:
        factor = selection['factor']
        result.update(status='trial-split', factor=factor, remaining=n//factor)
        return result
    result['odd_only_tuples'] = selection['odd_only_tuples']
    primes = sorted({p for plan in selection['charts'].values() for p in plan['primes']})
    odd_masks = {p: local_directions(n, t, p, 1) for p in primes}
    result['setup_work'].update(odd_mask_inversions=sum(p-1 for p in primes),
                                dyadic_mask_inversions=2**(selection['charts']['forward']['exponent']-1))
    for chart, plan in selection['charts'].items():
        run = scan_chart(n, t, h, j_limit, k_limit, chart, plan, odd_masks, max_per_chart)
        result['charts'][chart] = run
        for name in ('total_tuples', 'visited_tuples', 'unchecked_tuples', 'reconstructed', 'square_tests'):
            result[name] += run[name]
        result['proper_hits'] += len(run['hits'])
        if run['hits'] and result['factor'] is None:
            result['factor'] = run['hits'][0]['factor']
            result['remaining'] = n//result['factor']
    if result['factor'] is not None:
        result['status'] = 'split'
    elif result['unchecked_tuples'] == 0:
        result['status'] = 'exhausted'
    return result


def verify_split(n, factor, cofactor, directory):
    """Certify the discovered split and distinguish any remaining unproved cofactors."""
    if factor is None:
        return dict(primes_kernel_checked=False, product_kernel_checked=False,
                    verified_prime_factors=[], uncertified_cofactors=[str(n)])
    if min(factor, cofactor) < 2 or factor*cofactor != n:
        raise ValueError('a proper split must multiply to the input')
    primes, unresolved = [], []
    for value in sorted((factor, cofactor)):
        (primes if certificate_witness(value) is not None else unresolved).append(value)
    part = prod(primes)
    source = render_certificate(part, primes)
    theorem = 'PrimeFactors.Generated.factorization'
    if unresolved:
        theorem = 'PrimeFactors.Generated.partialSplit'
        source += f"""
theorem {theorem} : PrimeFactors.ExactFactorization {part} {primes} ∧
    {part} * {prod(unresolved)} = {n} ∧ {factor} * {cofactor} = {n} := by
  exact ⟨PrimeFactors.Generated.factorization, by decide +kernel, by decide +kernel⟩

#print axioms {theorem}
"""
    certificate = directory / 'DyadicOffsetFactorization.lean'
    certificate.write_text(source)
    verify_file(certificate, theorem_name=theorem)
    return dict(primes_kernel_checked=not unresolved, product_kernel_checked=True,
                verified_prime_factors=list(map(str, primes)), uncertified_cofactors=list(map(str, unresolved)))


def compare_holdout(verify=False):
    """Replay both complete searches using only the eight published products as inputs."""
    path = Path(__file__).resolve().parents[1] / 'research' / 'quartic-lane-holdout.json'
    samples = json.loads(path.read_text())
    keys = ('total_tuples', 'visited_tuples', 'unchecked_tuples', 'reconstructed', 'square_tests', 'proper_hits')
    totals = {method: dict.fromkeys((*keys, 'seconds'), 0) for method in ('odd', 'dyadic')}
    rows = []
    with TemporaryDirectory() as temporary:
        for i, item in enumerate(samples['rows']):
            n = int(item['n'])
            row = dict(sample=item['sample'], n=str(n))
            splits = []
            for method in (('odd', 'dyadic') if i % 2 else ('dyadic', 'odd')):
                start = perf_counter()
                if method == 'dyadic':
                    result = search(n, 1 << 18)
                else:
                    result = search_odd_wheel(n, 1 << 18, exhaust=True, optimize_wheel=True)
                elapsed = perf_counter()-start
                if result['status'] != 'split' or result['unchecked_tuples'] != 0:
                    raise ArithmeticError(f'{method} did not exhaust the holdout and return a split')
                splits.append(sorted((result['factor'], result['remaining'])))
                row[method] = {key: result[key] for key in keys}
                row[method]['seconds'] = elapsed
                for key, value in row[method].items():
                    totals[method][key] += value
            if splits[0] != splits[1] or prod(splits[0]) != n:
                raise ArithmeticError('the two methods gave inconsistent factorizations')
            if row['odd']['proper_hits'] != row['dyadic']['proper_hits']:
                raise ArithmeticError('the two methods gave inconsistent winning counts')
            row['factors'] = list(map(str, splits[0]))
            if verify:
                row.update(verify_split(n, *splits[0], Path(temporary)))
                if not row['primes_kernel_checked']:
                    raise ArithmeticError('the holdout needs an exact prime factorization certificate')
            rows.append(row)
    return dict(seed=samples['seed'], samples=len(rows), tuple_cap=1 << 18, max_exponent=20,
                totals=totals, rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--holdout', action='store_true', help='replay the eight frozen inputs with both methods')
    parser.add_argument('--max-per-chart', type=int, help='tuple budget in each chart for one input (default 32)')
    parser.add_argument('--max-exponent', type=int, help='last dyadic exponent for one input (default 20)')
    parser.add_argument('--verify', action='store_true', help='kernel-check each split and identify certified primes')
    args = parser.parse_args()
    if args.holdout:
        if args.n is not None or args.max_per_chart is not None or args.max_exponent is not None:
            parser.error('--holdout uses its fixed inputs, tuple caps and exponent range')
        answer = compare_holdout(args.verify)
    else:
        if args.n is None:
            parser.error('supply a product or select --holdout')
        answer = search(args.n, 32 if args.max_per_chart is None else args.max_per_chart,
                        max_exponent=20 if args.max_exponent is None else args.max_exponent)
        if args.verify:
            with TemporaryDirectory() as temp:
                answer.update(verify_split(args.n, answer['factor'], answer['remaining'], Path(temp)))
    print(json.dumps(answer, indent=2))
