"""Compare odd-part cofactor bands with raw band jumps, a consecutive scan and Fermat."""

import argparse
import hashlib
import json
import platform
from collections import Counter
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter_ns

from experiments.circle_mark_prefix_skip import band_search, choose_target, consecutive, measure
from scripts.factor import fermat_split, primes_through, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/circle-mark-reduced.json'


def reduced_search(n, target, width, *, record_controls=True):
    """Visit every coordinate beyond the public prefix and classify its odd remainder."""
    lower = n // (1 << width) + 1
    upper = (1 << width) - 1
    if n % 2 == 0 or not 0 < target < lower <= upper:
        raise ValueError('expected an odd modulus and a positive target below its factor band')
    prefix = isqrt(target + lower - 1)
    gcds = 0
    histogram = Counter()
    first_extra = None
    comparison_divisions = 0
    half_comparisons = 0
    beyond_one_shift = 0
    for x in range(prefix + 1, upper // 2 + 1):
        difference = x * x - target
        if difference & 1:
            valuation = 0
            odd_part = difference
        else:
            valuation = (difference & -difference).bit_length() - 1
            odd_part = difference >> valuation
        histogram[valuation] += 1
        # A positive value z lies in a band precisely when floor(z/lower)*upper >= z.
        if (odd_part // lower) * upper < odd_part:
            if record_controls and valuation > 1:
                # An admitted half-remainder implies its double is admitted in the raw bands.
                half = difference >> 1
                half_comparisons += 1
                beyond_one_shift += (half // lower) * upper >= half
            if record_controls and valuation and first_extra is None:
                # This comparison records a control and plays no part in the search decision.
                comparison_divisions += 1
                if (difference // lower) * upper >= difference:
                    first_extra = dict(x=x, difference=difference, valuation=valuation,
                                       odd_part=odd_part, lower=lower, upper=upper)
            continue
        gcds += 1
        divisor = gcd(odd_part, n)
        if divisor > 1:
            return dict(first_x=x, divisor=divisor, prefix=prefix, gcds=gcds,
                        histogram=histogram, first_extra=first_extra,
                        comparison_divisions=comparison_divisions, half_comparisons=half_comparisons,
                        beyond_one_shift=beyond_one_shift)
    raise ArithmeticError('the reduced search exhausted the factor-width bound')


def parity_shifts(target):
    """Return v2(x²-a) at an even and an odd coordinate when both are constant."""
    if target == 2:
        return 1, 0
    if target % 8 in (3, 7):
        return 0, 1
    if target % 8 == 5:
        return 0, 2
    return None


def lane_coordinates(target, parity, shift, lower, upper, cutoff, work):
    """Yield in order all in-band coordinates of one parity, through the factor-width cap."""
    scale = 1 << shift
    finish = upper // 2
    k = 1
    while True:
        start = 1 + isqrt(target + scale * k * lower - 1)
        work['lower_roots'] += 1
        start += (start - parity) & 1
        if start > finish:
            return
        work['bands'] += 1
        if k == cutoff:
            # At and beyond k, every integer reduced remainder belongs to a band.
            work['continuous_lanes'] += 1
            yield from range(start, finish + 1, 2)
            return
        end = isqrt(target + scale * k * upper)
        work['upper_roots'] += 1
        yield from range(start, min(end, finish) + 1, 2)
        if end >= finish:
            return
        k += 1


def hybrid_search(n, target, width, *, record_controls=False):
    """Run the two-lane search when the valuation is fixed, or classify the odd part."""
    shifts = parity_shifts(target)
    if shifts is None:
        return 'fallback', reduced_search(n, target, width, record_controls=record_controls)
    lower = (n >> width) + 1
    upper = (1 << width) - 1
    if n % 2 == 0 or not 0 < target < lower < upper:
        raise ValueError('expected an odd modulus and a target below the positive-width factor band')
    cutoff = 1 + (lower - 2) // (upper - lower)
    work = dict(lower_roots=0, upper_roots=0, bands=0, continuous_lanes=0)
    streams = [lane_coordinates(target, parity, shift, lower, upper, cutoff, work)
               for parity, shift in enumerate(shifts)]
    current = [next(stream, None) for stream in streams]
    gcds = comparisons = fixed_shifts = adjacency_checks = 0
    while current[0] is not None or current[1] is not None:
        if current[0] is None:
            parity = 1
        elif current[1] is None:
            parity = 0
        else:
            comparisons += 1
            parity = int(current[1] < current[0])
            if work['continuous_lanes'] == 2:
                adjacency_checks += 1
                start = current[parity]
                if current[1 - parity] == start + 1:
                    # Both pending heads and every following coordinate are admitted.
                    # At odd n the unreduced difference has exactly the same gcd.
                    for x in range(start, upper // 2 + 1):
                        divisor = gcd(x * x - target, n)
                        if divisor > 1:
                            tail = x - start + 1
                            unused = int(tail == 1)
                            return 'lanes', dict(
                                first_x=x, divisor=divisor, gcds=gcds + tail, cutoff=cutoff,
                                fixed_shifts=fixed_shifts, merge_comparisons=comparisons,
                                tail_adjacency_checks=adjacency_checks, tail_gcds=tail,
                                stream_candidates_generated=gcds + 2,
                                candidates_generated=gcds + tail + unused,
                                unused_lookahead=unused, **work,
                            )
                    raise ArithmeticError('continuous tail exhausted the factor-width bound')
        x = current[parity]
        odd_part = x * x - target
        if shifts[parity]:
            odd_part >>= shifts[parity]
            fixed_shifts += 1
        gcds += 1
        divisor = gcd(odd_part, n)
        if divisor > 1:
            prefetched = int(current[1 - parity] is not None)
            return 'lanes', dict(
                first_x=x, divisor=divisor, gcds=gcds, cutoff=cutoff, fixed_shifts=fixed_shifts,
                merge_comparisons=comparisons, tail_adjacency_checks=adjacency_checks, tail_gcds=0,
                stream_candidates_generated=gcds + prefetched, candidates_generated=gcds + prefetched,
                unused_lookahead=prefetched, **work,
            )
        current[parity] = next(streams[parity], None)
    raise ArithmeticError('both parity streams exhausted the factor-width bound')


def check_lanes():
    """Check complete streams, including empty bands and tails, against direct classification."""
    for width, lower in ((7, 65), (7, 99), (8, 248), (8, 254)):
        upper = (1 << width) - 1
        cutoff = 1 + (lower - 2) // (upper - lower)
        if not (cutoff - 1) * (upper - lower) < lower - 1 <= cutoff * (upper - lower):
            raise ArithmeticError('incorrect first continuous band')
        for target in (2, 3, 5, 7, 11, 13):
            for parity, shift in enumerate(parity_shifts(target)):
                expected = []
                for x in range(1, upper // 2 + 1):
                    y = x * x - target
                    if x % 2 != parity or y <= 0:
                        continue
                    if y & -y != 1 << shift:
                        raise ArithmeticError('incorrect valuation for this parity')
                    z = y >> shift
                    if z <= (z // lower) * upper:
                        expected.append(x)
                work = Counter()
                actual = list(lane_coordinates(target, parity, shift, lower, upper, cutoff, work))
                if actual != expected:
                    raise ArithmeticError('a lane missed or duplicated coordinates')


def census(width):
    upper = 1 << width
    primes = [p for p in primes_through(upper - 1) if p >= upper // 2]
    totals = dict(
        factor_bits=width, products=0, jacobi_tests=0, factors_during_target_selection=0,
        fermat_midpoints=0, consecutive_gcds=0, raw_band_gcds=0, raw_band_square_roots=0,
        reduced_gcds=0, reduced_prefix_square_roots=0, reduced_prefix_skips=0,
        reduced_classified_coordinates=0, reduced_odd_part_shifts=0, extra_skips=0,
        products_with_extra_skips=0, extra_skips_beyond_one_halving=0,
        comparison_only_half_band_divisions=0, example_only_raw_band_divisions=0,
    )
    lanes = dict(products=0, gcds=0, fixed_shifts=0, merge_comparisons=0, candidates_generated=0,
                 unused_lookahead=0, bands=0, continuous_lanes=0, lower_roots=0, upper_roots=0,
                 cutoff_divisions=0, tail_adjacency_checks=0, products_reaching_tail=0,
                 tail_gcds=0, stream_candidates_generated=0)
    fallback = dict(products=0, gcds=0, classified_coordinates=0, odd_part_shifts=0, prefix_square_roots=0)
    targets = Counter()
    histogram = Counter()
    earliest = None
    largest = None
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * width:
            continue
        # measure runs the consecutive scan, jumping raw-band search and ordinary Fermat.
        raw = measure(n, width)
        totals['products'] += 1
        totals['jacobi_tests'] += raw['target'] - 1
        totals['fermat_midpoints'] += raw['fermat_midpoints']
        if sorted((raw['fermat_divisor'], n // raw['fermat_divisor'])) != [p, q]:
            raise ArithmeticError('Fermat factorization disagrees with the independent prime labels')
        if 'early_factor' in raw:
            if raw['early_factor'] not in (p, q):
                raise ArithmeticError('target selection reported an invalid factor')
            totals['factors_during_target_selection'] += 1
            continue
        target = raw['target']
        targets[target] += 1
        method, hybrid = hybrid_search(n, target, width, record_controls=True)
        if method == 'lanes':
            reduced = reduced_search(n, target, width)
            lower = (n >> width) + 1
            gap = (1 << width) - 1 - lower
            if not (hybrid['cutoff'] - 1) * gap < lower - 1 <= hybrid['cutoff'] * gap:
                raise ArithmeticError('invalid cutoff for the continuous tail')
            if (hybrid['first_x'], hybrid['divisor'], hybrid['gcds']) != (
                    reduced['first_x'], reduced['divisor'], reduced['gcds']):
                raise ArithmeticError('parity lanes disagree with the independently classified scan')
            lanes['products'] += 1
            lanes['cutoff_divisions'] += 1
            lanes['products_reaching_tail'] += hybrid['tail_gcds'] > 0
            for field in ('gcds', 'fixed_shifts', 'merge_comparisons', 'candidates_generated',
                          'unused_lookahead', 'bands', 'continuous_lanes', 'lower_roots', 'upper_roots',
                          'tail_adjacency_checks', 'tail_gcds', 'stream_candidates_generated'):
                lanes[field] += hybrid[field]
        else:
            reduced = hybrid
            fallback['products'] += 1
            fallback['gcds'] += reduced['gcds']
            fallback['prefix_square_roots'] += 1
            inspected = sum(reduced['histogram'].values())
            fallback['classified_coordinates'] += inspected
            fallback['odd_part_shifts'] += inspected - reduced['histogram'][0]
        if (reduced['first_x'], reduced['divisor']) != (raw['first_x'], raw['divisor']):
            raise ArithmeticError('the reduced search changed the first marked coordinate or divisor')
        divisor = reduced['divisor']
        factors = sorted((divisor, n // divisor))
        if n % divisor or factors != [p, q]:
            raise ArithmeticError('a recovered factorization disagrees with the independent prime labels')
        classified = sum(reduced['histogram'].values())
        extra = raw['band_gcds'] - reduced['gcds']
        if (reduced['prefix'] + classified != raw['first_x'] or extra < 0
                or reduced['beyond_one_shift'] > extra
                or (extra > 0) != (reduced['first_extra'] is not None)):
            raise ArithmeticError('inconsistent reduced-coordinate accounting')
        histogram.update(reduced['histogram'])
        totals['consecutive_gcds'] += raw['direct_gcds']
        totals['raw_band_gcds'] += raw['band_gcds']
        totals['raw_band_square_roots'] += raw['square_roots']
        totals['reduced_gcds'] += reduced['gcds']
        totals['reduced_prefix_square_roots'] += 1
        totals['reduced_prefix_skips'] += reduced['prefix']
        totals['reduced_classified_coordinates'] += classified
        totals['reduced_odd_part_shifts'] += classified - reduced['histogram'][0]
        totals['extra_skips_beyond_one_halving'] += reduced['beyond_one_shift']
        totals['comparison_only_half_band_divisions'] += reduced['half_comparisons']
        totals['extra_skips'] += extra
        totals['products_with_extra_skips'] += extra > 0
        totals['example_only_raw_band_divisions'] += reduced['comparison_divisions']
        if not extra:
            continue
        first_x = reduced['first_extra']['x']
        keep_earliest = earliest is None or (first_x, n) < (
            earliest['first_extra_skip']['x'], int(earliest['product']),
        )
        keep_largest = largest is None or (extra, -n) > (largest['extra_skips'], -int(largest['product']))
        if keep_earliest or keep_largest:
            example = dict(
                product=str(n), target=raw['target'], factors=[str(f) for f in factors],
                first_extra_skip=reduced['first_extra'], first_mark=raw['first_x'],
                first_divisor=str(divisor), consecutive_gcds=raw['direct_gcds'],
                raw_band_gcds=raw['band_gcds'], raw_band_square_roots=raw['square_roots'],
                reduced_gcds=reduced['gcds'], reduced_classified_coordinates=classified,
                reduced_odd_part_shifts=classified - reduced['histogram'][0],
                extra_skips=extra, extra_skips_beyond_one_halving=reduced['beyond_one_shift'],
                fermat_midpoints=raw['fermat_midpoints'], hybrid_method=method,
            )
            if method == 'lanes':
                example['lane_cost'] = {field: count for field, count in hybrid.items()
                                        if field not in ('first_x', 'divisor')}
            if keep_earliest:
                earliest = example
            if keep_largest:
                largest = example
    if earliest is None:
        raise ArithmeticError('the cohort did not exercise an additional skip')
    totals['classified_by_two_adic_valuation'] = {str(v): histogram[v] for v in sorted(histogram)}
    if totals['reduced_gcds'] != lanes['gcds'] + fallback['gcds']:
        raise ArithmeticError('inconsistent hybrid gcd accounting')
    totals['hybrid'] = dict(
        target_frequencies={str(a): targets[a] for a in sorted(targets)},
        parity_lanes=lanes, full_stripping_fallback=fallback,
    )
    return totals, earliest, largest


def study():
    check_lanes()
    cohorts, earliest, largest = zip(*(census(width) for width in range(7, 13)))
    return dict(
        cost_convention=(
            'The reduced search takes one prefix square root per negative target. Each classified '
            'coordinate requires a squared difference, a parity test, one floor division by the '
            'public factor floor, and one band endpoint comparison with a multiplication. An even '
            'difference additionally needs a trailing-zero count and a right shift. A passing odd '
            'part receives one gcd. The raw band method jumps intervals. Extra divisions used to '
            'compare removing only one factor of two or to identify example skips are recorded '
            'separately from the search. The hybrid uses one division to find the first '
            'continuous band per qualifying product. It counts each lane endpoint root and each '
            'comparison of two available stream heads. Once both lanes are continuous and their '
            'heads are adjacent, it tests consecutive unreduced differences. Its unused lookahead is generated before '
            'the first hit and incurs no gcd. For other targets it uses the per-coordinate '
            'classifier. Fermat counts tested midpoints, including the successful one.'
        ),
        cohorts=list(cohorts),
        earliest_extra_skip=min(earliest, key=lambda e: (e['first_extra_skip']['x'], int(e['product']))),
        largest_extra_saving_by_width=list(largest),
    )


def verify_examples(observed):
    with TemporaryDirectory() as tmp:
        examples = [observed['earliest_extra_skip'], *observed['largest_extra_saving_by_width']]
        certificates = {example['product']: example['factors'] for example in examples}
        for product, factors in certificates.items():
            path = Path(tmp) / f'CircleReduced{product}.lean'
            path.write_text(render_certificate(int(product), [int(factor) for factor in factors]))
            verify_file(path)


def first_mark_checksum(cases, answers):
    digest = hashlib.sha256()
    for (n, target, _, _), (x, factor) in zip(cases, answers):
        digest.update(f'{n},{target},{x},{factor}\n'.encode('ascii'))
    return digest.hexdigest()


def time_controls(cases, width, trials, expected, expected_digest):
    """Run separate controls after all raw/hybrid pairs and validate outside the clock."""
    limit = 1 << width
    cap = (limit - 1) // 2
    results = []
    fermat_digest = None
    for trial in range(trials):
        order = ['consecutive', 'fermat'] if trial % 2 == 0 else ['fermat', 'consecutive']
        times = {}
        for name in order:
            answers = []
            if name == 'consecutive':
                start = perf_counter_ns()
                for n, target, _, _ in cases:
                    answers.append(consecutive(n, target, cap))
                times[name] = (perf_counter_ns() - start) / 1_000_000_000
                consecutive_digest = first_mark_checksum(cases, answers)
                if answers != expected or consecutive_digest != expected_digest:
                    raise ArithmeticError('consecutive first marks or checksum differ from the paired searches')
            else:
                start = perf_counter_ns()
                for n, _, _, _ in cases:
                    answers.append(fermat_split(n, limit))
                times[name] = (perf_counter_ns() - start) / 1_000_000_000
                digest = hashlib.sha256()
                midpoints = 0
                for (n, _, p, q), (divisor, steps) in zip(cases, answers):
                    if divisor is None or divisor <= 1 or n % divisor:
                        raise ArithmeticError('Fermat failed to split a timed input')
                    factors = sorted((divisor, n // divisor))
                    if factors != [p, q]:
                        raise ArithmeticError('timed Fermat factors disagree with the sieve labels')
                    midpoints += steps
                    digest.update(f'{n},{factors[0]},{factors[1]},{steps}\n'.encode('ascii'))
                if fermat_digest is not None and fermat_digest != digest.hexdigest():
                    raise ArithmeticError('timed Fermat trials disagree on factors or midpoint counts')
                fermat_digest = digest.hexdigest()
        results.append(dict(trial=trial + 1, order=order, seconds=times))
    return dict(
        convention='Run after the raw/hybrid pairs. Consecutive times the existing direct gcd '
                   'loop and collects (first coordinate, divisor). Fermat receives the product and '
                   'a width-derived limit, times the existing midpoint loop and collects (divisor, '
                   'midpoints). Both use their normal instrumentation. Factor validation, sorting, '
                   'checksums and summation of operation counts are outside the clock.',
        consecutive_gcds=sum(x for x, _ in expected), consecutive_answer_sha256=consecutive_digest,
        fermat_midpoints=midpoints, fermat_factors_and_steps_sha256=fermat_digest, trials=results,
    )


def time_twelve_bits(trials):
    """Compare paired searches on a fixed public target for every qualifying 12-bit product."""
    if trials < 1:
        raise ValueError('expected at least one paired timing trial')
    width = 12
    upper = 1 << width
    primes = [p for p in primes_through(upper - 1) if p >= upper // 2]
    cases = []
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() == 2 * width:
            target, early = choose_target(n)
            if early is not None:
                raise ArithmeticError('an input was already split during target selection')
            cases.append((n, target, p, q))

    def raw(n, target):
        return band_search(n, target, width)

    def hybrid(n, target):
        return hybrid_search(n, target, width)[1]

    expected = None
    results = []
    for trial in range(trials):
        order = [('raw', raw), ('hybrid', hybrid)]
        if trial % 2:
            order.reverse()
        times = {}
        for name, search in order:
            answers = []
            start = perf_counter_ns()
            for n, target, _, _ in cases:
                hit = search(n, target)
                answers.append((hit['first_x'], hit['divisor']))
            times[name] = (perf_counter_ns() - start) / 1_000_000_000
            if expected is None:
                for (_, factor), (_, _, p, q) in zip(answers, cases):
                    if factor not in (p, q):
                        raise ArithmeticError('the timed search returned an incorrect factor')
                expected = answers
            elif answers != expected:
                raise ArithmeticError('timed methods disagreed on first marks or factors')
        results.append(dict(trial=trial + 1, order=[name for name, _ in order], seconds=times))
    answer_digest = first_mark_checksum(cases, expected)
    controls = time_controls(cases, width, trials, expected, answer_digest)
    return dict(
        products=len(cases), answer_sha256=answer_digest,
        runtime=dict(implementation=platform.python_implementation(), python=platform.python_version(),
                     system=platform.system(), release=platform.release(), architecture=platform.machine()),
        clock='perf_counter_ns; seconds per full cohort',
        convention='Identical product and target order in every run. The timed section includes '
                   'each search, its normal counters, and collecting (first coordinate, factor). '
                   'Target selection, independent labels, cross-method checks, checksums, certificates '
                   'and the diagnostic divisions for example skips are outside the timed searches.',
        paired_trials=results, controls=controls,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timing', action='store_true', help='time the complete 12-bit cohort')
    parser.add_argument('--trials', type=int, default=3, help='paired trials for timing mode')
    args = parser.parse_args()
    if args.timing:
        print(json.dumps(time_twelve_bits(args.trials), indent=2))
        return
    observed = study()
    if observed != json.loads(FIXTURE.read_text()):
        raise SystemExit('reduced cofactor-band census differs from the reviewed fixture')
    verify_examples(observed)
    print(json.dumps(observed))


if __name__ == '__main__':
    main()
