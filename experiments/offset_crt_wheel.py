"""Select an exact minimum-cost CRT wheel within a bounded public prime menu."""

import argparse
from bisect import bisect_right
import json
from math import isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from scripts.factor import primes_through


# Eight primes after 743 suffice for the lookahead at every supported input size.
ODD_PRIMES = tuple(p for p in primes_through(853) if p >= 3)
LOOKAHEAD = 8


def subset_products(primes, costs):
    """Each entry describes one subset by modulus, tuple count and membership mask."""
    entries = [(1, 1, 0)]
    for index, prime in enumerate(primes):
        entries.extend([(modulus * prime, count * costs[prime], mask | (1 << index))
                        for modulus, count, mask in entries])
    return entries


def cheapest_subset(free, costs, threshold):
    """Minimum tuple count among free subsets with modulus strictly above threshold."""
    split = len(free) // 2
    left = subset_products(free[:split], costs)
    right = sorted(subset_products(free[split:], costs))
    moduli = [modulus for modulus, _, _ in right]
    suffix = [None] * len(right)
    best = None
    for i in range(len(right) - 1, -1, -1):
        modulus, count, mask = right[i]
        best = min(best, (count, modulus, mask)) if best is not None else (count, modulus, mask)
        suffix[i] = best

    winner = None
    feasible = 0
    for modulus, count, mask in left:
        start = bisect_right(moduli, threshold // modulus)
        if start == len(right):
            continue
        feasible += 1
        other_count, other_modulus, other_mask = suffix[start]
        choice = (count * other_count, modulus * other_modulus, mask | (other_mask << split))
        if winner is None or choice < winner:
            winner = choice
    if winner is None:
        raise ValueError('prime menu cannot reach the specified modulus threshold')
    count, modulus, mask = winner
    chosen = tuple(p for i, p in enumerate(free) if mask & (1 << i))
    return chosen, count, modulus, dict(left_subsets=len(left), right_subsets=len(right),
                                        threshold_queries=len(left), feasible_queries=feasible)


def global_lower_bound(menu, costs, threshold, incumbent, small_count=16):
    """Lower bound for every wheel of distinct eligible odd primes, even beyond the menu.

    The menu contains all eligible odd primes through its endpoint. For each
    exact subset of the first small_count primes, bound the remaining factor
    of the tuple count at every cardinality r. The cardinality bounds cross
    monotonically, so only adjacent indices can attain their minimum. For
    small-part modulus m and cost c the resulting lower bound is
    c*max(cheapest[r], 1 + floor(threshold / (m*2**r))). For r=0
    the small subset already has to exceed the entire threshold.
    """
    small, large = menu[:small_count], menu[small_count:]
    cheapest = [1]
    for p in large:
        cheapest.append(cheapest[-1] * costs[p])
    # g_p is nondecreasing with p. Every prime above the menu endpoint
    # costs at least the last known g_p, even for its favorable square class.
    while cheapest[-1] <= incumbent:
        cheapest.append(cheapest[-1] * costs[menu[-1]])
    crossing_values = [cost << r for r, cost in enumerate(cheapest)]
    lower = incumbent
    cases = subset_products(small, costs)
    checked = 0
    for modulus, cost, _ in cases:
        if cost > incumbent:
            continue
        if modulus > threshold:
            lower = min(lower, cost)
            continue
        remaining = threshold // modulus
        crossing = bisect_right(crossing_values, remaining)
        for r in (crossing - 1, crossing):
            if 1 <= r < len(cheapest):
                # The remaining prime product is strictly greater than
                # threshold/modulus, and each g_p exceeds p/2.
                cost_bound = max(cheapest[r], (remaining >> r) + 1)
                lower = min(lower, cost * cost_bound)
                checked += 1
    return dict(lower=lower, globally_optimal=(lower == incumbent),
                exact_small_subsets=len(cases), cardinality_checks=checked)


def choose_wheel(n, j_limit, k_limit, *, prove_bound=False):
    """Use only N and its enclosing box. Check small prime divisors before selection.

    Reproduce the 5..743 ascending baseline, then allow 3, eight following
    primes, and up to sixteen baseline primes to vary. The others stay fixed.
    """
    if n < 4 or min(j_limit, k_limit) < 1:
        raise ValueError('expected N >= 4 and positive box sides')
    threshold = 2 * j_limit * k_limit
    baseline = []
    baseline_modulus = 1
    for prime in ODD_PRIMES:
        if prime > 743:
            raise ValueError('the ascending baseline cannot cover the public box')
        if prime == 3 or prime == n:
            continue
        baseline.append(prime)
        baseline_modulus *= prime
        if baseline_modulus > threshold:
            break

    end = ODD_PRIMES.index(baseline[-1]) + 1 + LOOKAHEAD
    menu = tuple(p for p in ODD_PRIMES[:end] if p != n)
    work = dict(trial_divisions=0, euler_tests=0, eligible_primes=len(menu))
    residues = {}
    for p in menu:
        residue = n % p
        work['trial_divisions'] += 1
        if not residue:
            return dict(factor=p, primes=(), total_tuples=None, modulus=None,
                        threshold=threshold, work=work)
        residues[p] = residue
    costs = {}
    for p, residue in residues.items():
        square = pow(residue, (p - 1) // 2, p) == 1
        costs[p] = (p + (3 if square else 1)) // 2
        work['euler_tests'] += 1

    if len(baseline) <= 16:
        flexible = set(baseline)
    else:
        middle = baseline[8:-4]
        flexible = set(baseline[:8] + baseline[-4:])
        flexible.update(middle[i * (len(middle) - 1) // 3] for i in range(4))
    fixed = tuple(p for p in baseline if p not in flexible)
    fixed_set = set(fixed)
    free = tuple(p for p in menu if p not in fixed_set)
    fixed_modulus = prod(fixed)
    selected, cost, modulus, selection_work = cheapest_subset(free, costs, threshold // fixed_modulus)
    primes = tuple(sorted(fixed + selected))
    total_tuples = prod(costs[p] for p in fixed) * cost
    baseline_tuples = prod(costs[p] for p in baseline)
    assert prod(primes) == fixed_modulus * modulus > threshold
    assert prod(costs[p] for p in primes) == total_tuples <= baseline_tuples
    plan = dict(factor=None, primes=primes, total_tuples=total_tuples, modulus=prod(primes),
                threshold=threshold, baseline=baseline, baseline_tuples=baseline_tuples,
                baseline_modulus=baseline_modulus, fixed=fixed, free=free,
                work={**work, **selection_work})
    if prove_bound:
        plan['global_bound'] = global_lower_bound(menu, costs, threshold, total_tuples)
    return plan


def compare_holdout(verify=False):
    """Exhaust both modes on the eight published products. Expected factors are never read."""
    from experiments.offset_crt_reconstruction import search
    from scripts.factor import render_certificate, verify_file

    path = Path(__file__).resolve().parents[1]/'research'/'quartic-lane-holdout.json'
    inputs = json.loads(path.read_text())['rows']
    results = []
    with TemporaryDirectory() as temporary:
        for i, row in enumerate(inputs):
            n = int(row['n'])
            record = dict(id=row['sample'], n=str(n))
            splits = []
            for optimized in ((False, True) if i % 2 == 0 else (True, False)):
                start = perf_counter()
                report = search(n, 1 << 18, exhaust=True, optimize_wheel=optimized)
                elapsed = perf_counter() - start
                if report['status'] != 'split' or report['unchecked_tuples']:
                    raise ArithmeticError('expected an exhaustive CRT split within the public tuple cap')
                splits.append(sorted((report['factor'], report['remaining'])))
                keys = ('visited_tuples', 'reconstructed', 'square_tests', 'proper_hits')
                sample = {key: report[key] for key in keys}
                sample['seconds'] = elapsed
                if optimized:
                    sample['wheel_work'] = report['wheel_work']
                record['selected' if optimized else 'ascending'] = sample
            if splits[0] != splits[1] or splits[0][0]*splits[0][1] != n:
                raise ArithmeticError('the complete schedules gave inconsistent factorizations')
            if record['ascending']['proper_hits'] != record['selected']['proper_hits']:
                raise ArithmeticError('the complete schedules gave inconsistent hit counts')
            record['factors'] = list(map(str, splits[0]))
            if verify:
                cert = Path(temporary)/f'Holdout{i}.lean'
                cert.write_text(render_certificate(n, splits[0]))
                verify_file(cert)
                record['primes_kernel_checked'] = True
            results.append(record)
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--holdout', action='store_true', help='run both complete wheels on eight fixed products')
    parser.add_argument('--verify', action='store_true', help='replay Lean certificates on the holdout')
    parser.add_argument('--prove-bound', action='store_true',
                        help='bound every eligible odd-prime wheel, including primes beyond this menu')
    args = parser.parse_args()
    if args.holdout:
        if args.n is not None or args.prove_bound:
            parser.error('--holdout takes the published public inputs')
        print(json.dumps(compare_holdout(args.verify), indent=2))
    else:
        if args.n is None or args.n < 4 or args.verify:
            parser.error('supply N >= 4, or select --holdout [--verify]')
        t = isqrt(args.n)
        h = args.n - t*t
        if not h:
            parser.error('square input has no nonsquare offset box')
        j = isqrt(4*h // 3)
        k = t*j // h + 1
        print(json.dumps(choose_wheel(args.n, j, k, prove_bound=args.prove_bound), indent=2))
