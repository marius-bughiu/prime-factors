"""Search square-modulus norm relations by joining two lists of signed CRT sums."""

from argparse import ArgumentParser
from bisect import bisect_left
from heapq import merge
from itertools import combinations, count
from json import dumps
from math import comb, gcd, isqrt, prod

if __package__:
    from .exceptional_weights import root_table
    from .pell_relations import check_rows
else:
    from exceptional_weights import root_table
    from pell_relations import check_rows


def _local_roots(n, prime_count, work):
    """Select the first eligible odd primes; lift one unit root to each prime square."""
    roots = []
    primes = []
    for p in count(3, 2):
        if len(roots) == prime_count:
            break
        if any(p % d == 0 for d in primes if d*d <= p):
            continue
        primes.append(p)
        work['primes_tested'] += 1
        if n % p == 0:
            if p < n:
                return roots, p
            continue
        if pow(n, (p-1)//2, p) != 1:
            continue
        x = root_table(p)[n % p][0]
        shift = ((n-x*x)//p)*pow(2*x, -1, p) % p
        roots.append((p, x + p*shift))
    return roots, None


def _shift_sorted(values, shift, modulus):
    """Translating a sorted list around the residue circle wraps its tail to the front."""
    cut = bisect_left(values, modulus - shift)
    return ([x + shift - modulus for x in values[cut:]]
            + [x + shift for x in values[:cut]])


def _signed_sums(weights, modulus):
    residues = [0]
    for weight in weights:
        negative = _shift_sorted(residues, -weight % modulus, modulus)
        positive = _shift_sorted(residues, weight % modulus, modulus)
        residues = list(merge(negative, positive))
    return residues


def _split_roots(roots):
    d = prod(p for p, _ in roots)
    modulus = d*d
    weights = []
    for p, root in roots:
        square = p*p
        rest = modulus//square
        weights.append(root*rest*pow(rest, -1, square) % modulus)
    half = len(weights)//2
    return d, _signed_sums(weights[:half], modulus), _signed_sums(weights[half:], modulus)


def _rank(t, left, rights, modulus):
    """Index of the first root >= t in one doubly infinite periodic row."""
    period, offset = divmod(t-left, modulus)
    return period*len(rights) + bisect_left(rights, offset)


def _value(index, left, rights, modulus):
    period, offset = divmod(index, len(rights))
    return left + period*modulus + rights[offset]


def _window_ranks(target, lefts, rights, modulus):
    """Scan first indices at or above target. Over sorted lefts each index retreats at most one period in total."""
    rank = _rank(target, lefts[0], rights, modulus)
    previous = _value(rank-1, 0, rights, modulus)
    for left in lefts:
        while left + previous >= target:
            rank -= 1
            previous = _value(rank-1, 0, rights, modulus)
        yield rank


def _window(n, modulus, bound):
    low_square = max(0, n-modulus*bound)
    low = 0 if not low_square else 1+isqrt(low_square-1)
    return low, isqrt(n+modulus*bound)


def _nearby(n, d, lefts, rights, bound, hit_cap):
    """Find a global minimum, count the full window, retain at most hit_cap hits."""
    modulus = d*d
    split = isqrt(n)+1
    low, high = _window(n, modulus, bound)
    nearest = None
    hits = []
    total = 0
    ranks = _window_ranks(split, lefts, rights, modulus)
    starts = _window_ranks(low, lefts, rights, modulus)
    stops = _window_ranks(high+1, lefts, rights, modulus)
    for left, rank, first, stop in zip(lefts, ranks, starts, stops):
        for index in (rank-1, rank):
            t = _value(index, left, rights, modulus)
            if t >= 0:
                candidate = (abs(t*t-n), t)
                if nearest is None or candidate < nearest:
                    nearest = candidate
        total += stop-first
        for index in range(first, min(stop, first+hit_cap-len(hits))):
            hits.append(_value(index, left, rights, modulus))
    return nearest[0]//modulus, nearest[1], total, hits


def search(n, prime_count, threshold_bits, hit_cap, subset_size=None):
    """Join all roots in one window, or rotate through lexicographic prime subsets.

    With a subset size, screen positive squares as they arrive. The hit cap
    applies across all windows. Exact interval counts and minima cover every
    window actually opened, including the last window even if the search stops.
    """
    if n <= 1 or min(prime_count, hit_cap) < 0:
        raise ValueError('expected n > 1 and nonnegative prime count and hit cap')
    width = prime_count if subset_size is None else subset_size
    if not 0 <= width <= prime_count:
        raise ValueError('subset size must be between zero and the prime count')
    s = isqrt(n)
    work = dict(factor=None, outcome='no_split', primes_tested=0, primes=[], modulus_bits=0,
                left_size=0, right_size=0, min_abs_norm=None, nearest_t=None, nearest_d=None,
                windows=0, total_windows=comb(prime_count, width), interval_hits=0,
                materialized_hits=0, visited_hits=0, hit_cap_reached=False, square_tests=0,
                rows=0, private_pruned=0, pruning_rounds=0, min_private_bits=None,
                dependencies=0, tested=0, selected_steps=[])
    if s*s == n:
        return dict(work, factor=s, outcome='perfect_square')
    if n % 2 == 0:
        return dict(work, factor=2, outcome='even') if n > 2 else work
    roots, factor = _local_roots(n, prime_count, work)
    work['primes'] = [p for p, _ in roots]
    if factor is not None:
        return dict(work, factor=factor, outcome='prime_divisor')

    bound = s >> threshold_bits if threshold_bits >= 0 else isqrt(n << (-2*threshold_bits))
    best = None
    rows = []
    for chosen in combinations(roots, width):
        d, lefts, rights = _split_roots(chosen)
        remaining = hit_cap-work['visited_hits']
        minimum, t_min, total, hits = _nearby(n, d, lefts, rights, bound, remaining)
        candidate = (minimum, t_min, d)
        if best is None or candidate < best:
            best = candidate
            work.update(min_abs_norm=str(minimum), nearest_t=str(t_min), nearest_d=str(d))
        work['windows'] += 1
        work['left_size'] += len(lefts)
        work['right_size'] += len(rights)
        work['modulus_bits'] = max(work['modulus_bits'], (d*d).bit_length())
        work['interval_hits'] += total
        work['materialized_hits'] += len(hits)
        work['hit_cap_reached'] = len(hits) < total
        inverse = pow(d, -1, n)
        for t in hits:
            work['visited_hits'] += 1
            norm = (t*t-n)//(d*d)
            label = str(t) if subset_size is None else [str(d), str(t)]
            divisor = gcd(t, n)
            if 1 < divisor < n:
                return dict(work, factor=divisor, outcome='root_gcd', selected_steps=[label])
            if divisor == 1:
                residue = t*inverse % n
                work['rows'] += 1
                if subset_size is not None and norm > 0:
                    work['square_tests'] += 1
                    root = isqrt(norm)
                    if root*root == norm:
                        divisor = gcd(n, residue-root)
                        if 1 < divisor < n:
                            return dict(work, factor=divisor, outcome='square_norm',
                                        selected_steps=[label])
                rows.append((label, norm, residue))
        if work['visited_hits'] == hit_cap:
            if work['windows'] < work['total_windows']:
                work['hit_cap_reached'] = True
            break
    return check_rows(n, rows, work)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--prime-count', type=int, default=8)
    parser.add_argument('--threshold-bits', type=int, default=3)
    parser.add_argument('--hit-cap', type=int, default=128)
    parser.add_argument('--subset-size', type=int)
    args = parser.parse_args()
    print(dumps(search(args.n, args.prime_count, args.threshold_bits, args.hit_cap, args.subset_size)))
