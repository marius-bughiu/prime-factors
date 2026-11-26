"""Visit one CRT half in either direction and stop once a sum or a gap yields factors."""

from bisect import bisect_left, bisect_right
from collections import defaultdict
from math import gcd, isqrt

from . import trace_folded_right
from .collision_gap_readout import factor_from_gap
from .sum_menu_partition import partition, prefix_sizes
from .sum_signature_join import _contributions, _fermat_preflight, _plan_crt


def _digits(groups, period, n, base, inverse_period, subtract, work, prefix=None, reverse=False):
    """Each digit has one multiplier for its ordinary sum and one for a wrap."""
    layers = []
    ordered = sorted(_contributions(groups, period, work), key=len)
    sizes = [len(digits) for digits in ordered]
    needed = sizes if prefix is None else prefix_sizes(sizes, prefix)
    for digits, count in zip(ordered, needed):
        if prefix is not None:
            work['left_digit_choices_skipped'] += len(digits)-count
            digits = digits[-count:] if reverse else digits[:count]
        if digits == [0]:
            continue
        options = []
        for digit in digits:
            if digit == 0:
                options.append((0, 1, 1))
                continue
            exp = period-digit if subtract else digit
            power = pow(base, exp, n)
            work['digit_powers'] += 1
            work['setup_powers'] += 1
            adjusted = power * inverse_period % n
            work['signature_multiplications'] += 1
            plain, wrapped = (adjusted, power) if subtract else (power, adjusted)
            options.append((digit, plain, wrapped))
        layers.append(options)
    return layers


def _rows(groups, period, n, start, work, reverse=False):
    """Depth-first CRT folds keep one path. Reversing every layer reverses the leaf sequence."""
    if not groups:
        yield 0, start
        return
    choices = reversed if reverse else iter
    stack = [(0, start, choices(groups[0]))]
    while stack:
        previous, key, options = stack[-1]
        choice = next(options, None)
        if choice is None:
            stack.pop()
            continue
        digit, plain, wrapped = choice
        value = previous + digit
        if digit:
            if value >= period:
                value -= period
                multiplier = wrapped
            else:
                multiplier = plain
            key = key * multiplier % n
            work['signature_multiplications'] += 1
        if len(stack) == len(groups):
            yield value, key
        else:
            stack.append((value, key, choices(groups[len(stack)])))


def _matching_sums(rows, buckets, lower, width, period, n, wrap_power, max_visited, work):
    """Yield in-range matches without opening later rows or copying a bucket slice."""
    for a, target in rows:
        work['left_visited'] += 1
        work['left_unvisited'] -= 1
        for wrap in (0, 1):
            lo = max(0, wrap*period-a)
            hi = min(period-1, wrap*period+width-a)
            if lo > hi:
                continue
            key = target
            if wrap:
                key = target * wrap_power % n
                work['signature_multiplications'] += 1
            work['lookups'] += 1
            bucket = buckets.get(key)
            if bucket is None:
                continue
            work['matched_range_queries'] += 1
            first = bisect_left(bucket, lo)
            stop = bisect_right(bucket, hi)
            for idx in range(first, stop):
                yield lower + a + bucket[idx] - wrap*period
        if work['left_visited'] == max_visited:
            break


def _ordinary_events(n, base, lower, width, period, left, right, max_visited, reverse, work):
    wrap_power = pow(base, period, n)
    inverse_period = pow(wrap_power, -1, n)
    start = pow(base, n+1-lower, n)
    work.update(setup_powers=2, signature_inversions=1)
    right_digits = _digits(right, period, n, base, inverse_period, False, work)
    prefix = max_visited if 'partition' in work else None
    left_digits = _digits(left, period, n, base, inverse_period, True, work, prefix, reverse)

    buckets = defaultdict(list)
    for b, key in _rows(right_digits, period, n, 1, work):
        buckets[key].append(b)
        work['right_built'] += 1
    for bucket in buckets.values():
        bucket.sort()
    work['right_buckets'] = len(buckets)

    rows = _rows(left_digits, period, n, start, work, reverse)
    for total in _matching_sums(rows, buckets, lower, width, period, n, wrap_power, max_visited, work):
        yield total, None


def search(n, *, candidates=(2,), max_right=65536, max_visited=65536, reverse=False,
           gap_trial_cap=None, folded=False, memory_partition=False, partition_budget=100000,
           sum_interval=None):
    """Factor a balanced odd semiprime using a publicly screened base.

    candidates is a finite sequence of integer bases. max_right caps stored residues and
    max_visited caps streamed left leaves. If supplied, gap_trial_cap caps total tested
    trial divisors across all gap attempts. After a bounded gap miss the scan still tests
    every new match it visits, retrying the auxiliary factorization only on a shorter gcd.
    With folded=True the storage cap counts centered sign orbits in the right table.
    With memory_partition=True the planner places whole moduli on the right to
    minimize the complete left scan under max_right; partition_budget limits DP transitions.
    sum_interval optionally restricts the search to inclusive integer sum bounds.
    """
    if n < 9 or n % 2 == 0 or min(max_right, max_visited) < 0:
        raise ValueError('expected an odd input at least 9 and nonnegative table and row caps')
    if gap_trial_cap is not None and gap_trial_cap < 0:
        raise ValueError('expected a nonnegative trial cap')
    if memory_partition and partition_budget < 0:
        raise ValueError('expected a nonnegative partition transition budget')
    lower = isqrt(4*n-1) + 1
    upper = isqrt(9*n//2)
    if sum_interval is not None:
        first, last = sum_interval
        if not isinstance(first, int) or not isinstance(last, int):
            raise ValueError('expected integer sum endpoints')
        lower, upper = max(lower, first), min(upper, last)
    width = max(0, upper-lower)
    work = dict(width=width, period=1, candidate_bases=len(candidates), preflight_gcds=0,
                preflight_powers=0, local_sites=0, local_inverses=0, local_moduli=0,
                left_potential=None, right_potential=None, left_visited=0, left_unvisited=None,
                right_built=0, left_entries_stored=0, right_buckets=0, reverse=reverse,
                max_right=max_right, max_visited=max_visited, gap_trial_cap=gap_trial_cap,
                setup_powers=0, digit_powers=0, signature_multiplications=0,
                signature_inversions=0, crt_inverses=0, lookups=0, matched_range_queries=0,
                matching_sums_seen=0, square_tests=0, first_two_sums=[], gap_attempts=0,
                gap_budget_stops=0, gap_gcds=0, trial_divisions=0, factor_divisions=0,
                order_powers=0, projection_gcds=0, gap_square_tests=0, last_gap=None)
    if folded:
        work.update(folded=True, ordinary_right_potential=None, right_fixed_points=None,
                    fixed_residue_probes=0, right_orbits_visited=0, trace_center=None,
                    trace_matches=0, orientation_powers=0, trace_gcds=0, trace_split=None)
    bases = []
    if sum_interval is not None:
        work.update(lower=lower, upper=upper)

    def result(outcome, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError('invalid divisor')
        factors = [] if factor is None else list(map(str, sorted((factor, n//factor))))
        return dict(outcome=outcome, factors=factors, bases=bases, probes=probes, work=work)

    if lower > upper:
        probes = []
        return result('empty_interval')
    probes, base, factor = _fermat_preflight(n, candidates)
    work['preflight_powers'] = sum(probe['fermat'] is not None for probe in probes)
    work['preflight_gcds'] = len(probes) + work['preflight_powers']
    if factor is not None:
        return result('preflight_gcd', factor)
    if base is None:
        return result('no_witness_within_cap')
    bases.append(str(base))

    factor, period, halves, sizes = _plan_crt(n, lower, width, work)
    if factor is not None:
        return result('local_gcd', factor)
    if memory_partition:
        left, right, plan = partition(halves, lower, max_right, folded, partition_budget)
        work.update(partition=plan, left_digit_choices_skipped=0)
        sizes = [plan['left_rows'], plan['right_choices']]
    else:
        if sizes[0] < sizes[1]:
            halves.reverse()
            sizes.reverse()
        left, right = halves
    work.update(left_potential=sizes[0], right_potential=sizes[1], left_unvisited=sizes[0])
    if folded:
        orbits, fixed = trace_folded_right.orbit_count(right, lower, sizes[1])
        probes_checked = len(right) + sum(m % 2 == 0 for m, _ in right)
        work.update(ordinary_right_potential=sizes[1], right_potential=orbits,
                    right_fixed_points=fixed, fixed_residue_probes=probes_checked)
    if not max_visited:
        return result('left_limit')
    if work['right_potential'] > max_right:
        return result('right_limit')

    anchor = None
    second = None
    gap = 0
    generate = trace_folded_right.events if folded else _ordinary_events
    for s, split in generate(n, base, lower, width, period, left, right, max_visited, reverse, work):
        if split is not None:
            return result('trace_mixed_gcd', split)
        work['matching_sums_seen'] += 1
        if len(work['first_two_sums']) < 2:
            work['first_two_sums'].append(str(s))
        delta = s*s-4*n
        root = isqrt(delta)
        work['square_tests'] += 1
        if root*root == delta and (s-root) % 2 == 0:
            return result('sum_square', (s-root)//2)
        if anchor is None:
            anchor = s
            continue
        if second is None:
            second = s
        work['gap_gcds'] += 1
        new_gap = gcd(gap, abs(s-anchor))
        if new_gap == gap:
            continue
        gap = new_gap
        # One trial per possible integer divisor is an overestimate
        # sufficient for the unbounded policy on this particular gap.
        remaining = (isqrt(gap) if gap_trial_cap is None
                     else gap_trial_cap-work['trial_divisions'])
        status, factor, report = factor_from_gap(
            n, base, lower, upper, anchor, second, remaining, common_multiple=gap)
        work['gap_attempts'] += 1
        for counter in ('trial_divisions', 'factor_divisions', 'order_powers', 'projection_gcds'):
            work[counter] += report[counter]
        work['gap_square_tests'] += report['square_tests']
        work['last_gap'] = dict(report, outcome=status)
        if factor is not None:
            return result(status, factor)
        if status == 'gap_budget':
            work['gap_budget_stops'] += 1
    return result('left_limit' if work['left_unvisited'] else 'exhausted')
