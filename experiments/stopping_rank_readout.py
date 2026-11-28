"""Exhaust the first scalar gcd ranks of five small, fixed semiprimes.

For each residue a with Jacobi(a, N) = -1, scan the positive integers x in
order until gcd(x² - a, N) > 1. Each residue has equal weight. The product
alone enters the measurement. An independent capped scan assigns each residue a
score of +1 (hit), −1 (eligible miss), or zero (ineligible). Reference primes
check the two CRT layers and both midpoint readouts.
"""

import json
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, groupby
from math import gcd, isqrt
from pathlib import Path

from experiments.circle_mark_prefix_skip import choose_target, consecutive
from experiments.mixed_ratio_heights import jacobi
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/stopping-rank-readout.json'
REFERENCE = {187: (11, 17), 2183: (37, 59), 2501: (41, 61), 2537: (43, 59), 2701: (37, 73)}


def measure(n):
    """Count actual (divisor, rank) results before examining the reference factors."""
    by_divisor = defaultdict(Counter)
    first = None
    for a in range(n):
        if jacobi(a, n) == -1:
            rank, divisor = consecutive(n, a, n // 2)
            by_divisor[divisor][rank] += 1
            if first is None:
                first = dict(target=a, divisor=str(divisor), rank=rank)
    target, selector_divisor = choose_target(n)
    if first is None or selector_divisor is not None or target != first['target']:
        raise ArithmeticError(f'First negative target mismatch at {n}')
    return by_divisor, first


def rank_runs(histogram):
    """Adjacent ranks with equal counts share a single row in the fixture."""
    result = []
    for count, ranks in groupby(range(1, max(histogram) + 1), key=histogram.__getitem__):
        block = list(ranks)
        result.append(dict(first=block[0], last=block[-1], targets_per_rank=count))
    return result


def summarize(n, layers, fixed, p, q):
    primes = primes_through(q)
    if p not in primes or q not in primes or not p < q or p*q != n or set(layers) != {p, q}:
        raise ArithmeticError(f'Recovered factors disagree with prime references at {n}')
    u, v = (p - 1) // 2, (q - 1) // 2
    for r, length, multiplicity in ((p, u, v), (q, v, u)):
        expected = {k: multiplicity for k in range(1, length + 1)}
        if layers[r] != expected:
            raise ArithmeticError(f'Incorrect first-rank counts at {n}, divisor {r}')

    histogram = layers[p] + layers[q]
    total = sum(histogram.values())
    gcds = sum(k * c for k, c in histogram.items())
    mean = Fraction(gcds, total)
    second = Fraction(sum(k*k*c for k, c in histogram.items()), total)
    variance = second - mean**2
    if (total != 2*u*v or mean != Fraction(p+q+2, 8)
            or variance != Fraction(5*(p+q)**2 - 16*n - 4*(p+q) - 12, 192)):
        raise ArithmeticError(f'Moment identities failed at {n}')

    first_mass = Fraction(histogram[1], total)
    sum_from_mass = (first_mass * (n+1) + 2) / (first_mass + 1)
    if sum_from_mass != p+q or 2*histogram[1]+2 != p+q:
        raise ArithmeticError(f'Exact first-bucket readout failed at {n}')

    return dict(product=str(n), prime_factors=[str(p), str(q)], negative_targets=total,
                gcd_tests_over_all_targets=gcds, histogram=rank_runs(histogram),
                layers={str(r): rank_runs(layers[r]) for r in (p, q)}, first_target=fixed,
                mean=str(mean), second_moment=str(second), population_variance=str(variance),
                factor_sum_from_mean=str(8*mean-2), first_rank_probability=str(first_mass),
                factor_sum_from_product_and_first_rank_probability=str(sum_from_mass))


def midpoint_score(n, a, cutoff):
    if jacobi(a, n) != -1:
        return 0, 0
    for position in range(1, cutoff+1):
        if gcd(position*position-a, n) > 1:
            return 1, position
    return -1, cutoff


def midcut(n):
    """Directly score all residues using the public cutoff, without factor labels."""
    cutoff = isqrt(n) // 2
    counts = Counter()
    gcds = 0
    for a in range(n):
        score, used = midpoint_score(n, a, cutoff)
        counts[score] += 1
        gcds += used

    hits, misses = counts[1], counts[-1]
    population = hits + misses
    signed = hits - misses
    rate = Fraction(hits, population)
    larger = 1 + cutoff / (rate - Fraction(1, 2))
    smaller = 1 + Fraction(signed, cutoff)
    # The unbiased one-draw estimate uses all N residue classes with equal weight.
    values = {s: 1 + Fraction(n*s, cutoff) for s in counts}
    mean = sum(c * values[s] for s, c in counts.items()) / n
    variance = sum(c * (values[s] - mean)**2 for s, c in counts.items()) / n
    if mean != smaller or variance != Fraction(n*population, cutoff**2) - (smaller-1)**2:
        raise ArithmeticError(f'Signed score moments disagree with direct counts at {n}')
    return dict(cutoff=cutoff, eligible_hits=hits, eligible_misses=misses, ineligible=counts[0],
                direct_gcd_tests=gcds, hits_minus_misses=signed, normalized_hit_rate=str(rate),
                larger_from_hit_rate=str(larger), smaller_from_signed_count=str(smaller),
                one_draw_mean=str(mean), one_draw_variance=str(variance),
                variance_over_product=str(variance/n))


def rounding_control(n, midpoint):
    """Round the same signed count at two scales, then test the nearest odd candidate."""
    rows = []
    for step in (10, 100):
        rounded = step * round(Fraction(midpoint['hits_minus_misses'], step))
        estimate = 1 + Fraction(rounded, midpoint['cutoff'])
        if estimate.denominator == 1 and estimate.numerator % 2 == 0:
            raise ArithmeticError('Control requires a unique nearest odd integer')
        candidate = 2*(estimate // 2) + 1
        rows.append(dict(step=step, rounded_count=rounded, smaller_estimate=str(estimate),
                         nearest_odd=candidate, divides_product=1 < candidate < n and n % candidate == 0))
    return dict(product=str(n), cutoff=midpoint['cutoff'], exact_count=midpoint['hits_minus_misses'],
                rounded=rows)


def censored(n, histogram, cutoff):
    total = sum(histogram.values())
    hits = [histogram[k] for k in range(1, cutoff+1)]
    if any(c != hits[0] for c in hits):
        raise ArithmeticError(f'Expected a constant rank mass through {cutoff} at {n}')
    misses = total - sum(hits)
    tests = sum(k*c for k, c in enumerate(hits, 1)) + cutoff*misses
    return dict(product=str(n), early_hits=sum(hits), misses=misses,
                probability_at_each_observed_rank=str(Fraction(hits[0], total)),
                probability_of_miss=str(Fraction(misses, total)),
                mean_gcd_tests_when_capped=str(Fraction(tests, total)))


def distinct_sample_control():
    """Enumerate all subsets at the two sample sizes bracketing RMS error one."""
    n = 15
    cutoff = isqrt(n) // 2
    scores = [midpoint_score(n, a, cutoff)[0] for a in range(n)]
    rows = []
    for size in (12, 13):
        subsets, total_squared_error = 0, Fraction()
        for sample in combinations(scores, size):
            estimate = 1 + Fraction(n*sum(sample), cutoff*size)
            total_squared_error += (estimate-3)**2
            subsets += 1
        rows.append(dict(size=size, subsets=subsets, mean_squared_error=str(total_squared_error/subsets)))
    return dict(product=str(n), prime_factors=['3', '5'], rows=rows)


def study():
    rows = []
    controls = []
    rounding = None
    cutoff = 18
    for n, (p, q) in REFERENCE.items():
        layers, first = measure(n)
        row = summarize(n, layers, first, p, q)
        midpoint = midcut(n)
        k = midpoint['cutoff']
        histogram = layers[p] + layers[q]
        early = sum(c for rank, c in histogram.items() if rank <= k)
        spent = sum(min(rank, k)*c for rank, c in histogram.items())
        if (midpoint['larger_from_hit_rate'] != str(q) or midpoint['smaller_from_signed_count'] != str(p)
                or midpoint['eligible_hits'] != early or midpoint['direct_gcd_tests'] != spent
                or midpoint['eligible_misses'] != row['negative_targets'] - early
                or midpoint['ineligible'] != n - row['negative_targets']
                or Fraction(midpoint['variance_over_product']) <= 1):
            raise ArithmeticError(f'Midpoint score disagrees with reference at {n}')
        row['midcut'] = midpoint
        rows.append(row)
        if n == 2183:
            rounding = rounding_control(n, midpoint)
        if n in (2501, 2701):
            controls.append(censored(n, histogram, cutoff))
    left, right = controls
    for key in ('probability_at_each_observed_rank', 'probability_of_miss', 'mean_gcd_tests_when_capped'):
        if left[key] != right[key]:
            raise ArithmeticError(f'Censored normalized distributions differ at {key}')
    return dict(cases=rows, censoring_control=dict(cutoff=cutoff, products=controls),
                signed_rounding_control=rounding, distinct_sample_control=distinct_sample_control())


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Stopping-rank census differs from the reviewed fixture')
    total = sum(row['negative_targets'] for row in result['cases'])
    residues = sum(int(row['product']) for row in result['cases'])
    print(f"Checked {total} first hits and {residues} midpoint scores across {len(result['cases'])} products.")
