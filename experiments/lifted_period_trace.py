"""Compare three evaluators of the same lifted factor-sum join.

Run python3 -m experiments.lifted_period_trace --verify to compare the deterministic
fields with research/lifted-period-traces.json and kernel-check the recovered factors.
"""

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import chain
import json
from math import gcd, isqrt
from pathlib import Path
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter_ns

from . import lifted_period_join as join
from .factor_sum_quantile import sum_bounds
from .sum_signature_join import _fermat_preflight
from .trace_folded_right import _layers, _walk

ROOT = Path(__file__).resolve().parents[1]
FRESH_N = 3744658748524638520465885991
SEED = b'short-wheel-deferred-prime-postdesign-v1'
MODES = ('stock', 'direct', 'recurrence')
CAPS = dict(max_right=20_000, max_visited=32_256, max_lookups=100_000,
            power_limit=10_000, drop_limit=3, budget=2_000_000)


class TraceSeries:
    """Keys v*h^k + v⁻¹*h⁻ᵏ in a closed integer interval of exponents."""

    def __init__(self, n, h, back, work, mode):
        if mode not in ('direct', 'recurrence'):
            raise ValueError('unknown trace evaluator')
        self.n = n
        self.step = (h + back) % n
        self.powers = {-1: (back, h), 0: (1, 1), 1: (h, back)}
        self.work = work
        self.mode = mode

    def powers_at(self, k):
        if k not in self.powers:
            forward, back = self.powers[1 if k > 0 else -1]
            self.powers[k] = pow(forward, abs(k), self.n), pow(back, abs(k), self.n)
            self.work['setup_powers'] += 2
        return self.powers[k]

    def keys(self, v, inv, first, last):
        if first > last:
            return []
        n = self.n
        size = last - first + 1
        contains_zero = first <= 0 <= last

        def direct(k):
            if k == 0:
                return (v + inv) % n
            forward, back = self.powers_at(k)
            return (v * forward + inv * back) % n

        if size == 1:
            self.work['signature_multiplications'] += 2 * int(first != 0)
            return (direct(first),)

        # In a row starting at -1 or 0 the first two keys cost two products together.
        if first in (-1, 0):
            middle = (v + inv) % n
            forward, back = self.powers[1 if first == 0 else -1]
            adjacent = (v * forward + inv * back) % n
            prev, cur = (middle, adjacent) if first == 0 else (adjacent, middle)
            keys = [prev, cur]
            if self.mode == 'recurrence':
                for _ in range(size - 2):
                    prev, cur = cur, (self.step * cur - prev) % n
                    keys.append(cur)
                self.work['signature_multiplications'] += size
            else:
                keys.extend(direct(k) for k in range(first + 2, last + 1))
                self.work['signature_multiplications'] += 2 * (size - 1)
            return keys

        if self.mode == 'direct':
            self.work['signature_multiplications'] += 2 * (size - int(contains_zero))
            return [direct(k) for k in range(first, last + 1)]

        keys = [0] * size
        if contains_zero:
            # Start at zero and work out in both directions, preserving output order.
            zero = -first
            keys[zero] = (v + inv) % n
            if last > 0:
                keys[zero + 1] = direct(1)
                keys[zero - 1] = (self.step * keys[zero] - keys[zero + 1]) % n
            else:
                keys[zero - 1] = direct(-1)
            for i in range(zero + 2, size):
                keys[i] = (self.step * keys[i - 1] - keys[i - 2]) % n
            for i in range(zero - 2, -1, -1):
                keys[i] = (self.step * keys[i + 1] - keys[i + 2]) % n
            self.work['signature_multiplications'] += size
        else:
            keys[:2] = direct(first), direct(first + 1)
            for i in range(2, size):
                keys[i] = (self.step * keys[i - 1] - keys[i - 2]) % n
            self.work['signature_multiplications'] += size + 2
        return keys


def centered_table(layers, n, period, lift, power, back, work, mode):
    table = defaultdict(list)
    series = TraceSeries(n, power, back, work, mode)
    lifted = period * lift
    entries = orbits = 0
    for r, u, inv in _walk(layers, period, n, 1, 1, True, False, work):
        orbits += 1
        if lift == 1:
            if 2 * r > period:
                trace = (power * inv + back * u) % n
                work['signature_multiplications'] += 2
                r = period - r
            else:
                trace = (u + inv) % n
            table[trace].append(r)
            entries += 1
            continue
        # Take signed points in (-lifted/2, lifted/2]. A self-inverse CRT residue
        # already represents both signs, so in that case take only nonnegative points.
        fixed = r == 0 or 2 * r == period
        first = 0 if fixed else -(((lifted - 1) // 2 + r) // period)
        last = (lifted // 2 - r) // period
        keys = series.keys(u, inv, first, last)
        entries += len(keys)
        # Match stock copy order even if several positions share a key.
        if fixed:
            order = range(first, last + 1)
        elif 2 * r < period:
            order = chain(range(0, last + 1), range(first, 0))
        else:
            order = chain(range(-1, first - 1, -1), range(last, -1, -1))
        for k in order:
            table[keys[k - first]].append(abs(r + k * period))
    work['right_built'] += entries
    work['base_orbits'] += orbits
    return table


def prepare(n, lower, menus, plan, work, mode):
    if mode == 'stock':
        return join._prepare(n, 2, lower, menus, plan, work)
    period = plan['period']
    power = pow(2, period, n)
    back = pow(power, -1, n)

    def layers(moduli, right):
        shifted = [(m, {(s - lower) % m for s in menus[m]}) for m in moduli]
        return _layers(shifted, period, n, 2, power, back, lower, right, work)

    center, right = layers(plan['right_moduli'], True)
    _, left = layers(plan['left_moduli'], False)
    table = centered_table(right, n, period, plan['lift'], power, back, work, mode)
    if work['right_built'] != plan['right_entries']:
        raise ArithmeticError('centered table size disagrees with plan')
    work['right_buckets'] = len(table)
    lifted = pow(power, plan['lift'], n)
    exponent = n + 1 - lower - center
    start = pow(2, exponent, n)
    work['setup_powers'] += 3
    work['signature_inversions'] += 3 + int(exponent < 0)
    return left, center, table, start, pow(start, -1, n), lifted, pow(lifted, -1, n)


def sweep(n, lower, width, plan, prepared, work, mode):
    if mode == 'stock':
        return join._sweep(n, 2, lower, 0, width, plan, prepared, True, work)
    left, center, table, start, inverse, h, back = prepared
    period, lifted = plan['period'], plan['lifted_period']
    series = TraceSeries(n, h, back, work, mode)
    for a, v, inv in _walk(left, period, n, start, inverse, False, True, work):
        work['left_visited'] += 1
        first = -((width + lifted // 2 - a - center) // lifted)
        last = (a + center + lifted // 2) // lifted
        keys = series.keys(v, inv, first, last)
        work['left_keys_prepared'] += len(keys)
        for k, trace in enumerate(keys, first):
            work['lookups'] += 1
            bucket = table.get(trace)
            if not bucket:
                continue
            offset = a + center - k * lifted
            # Recover the oriented point only when a bucket was found.
            y, y_inv = v, inv
            if k:
                forward, backward = series.powers_at(k)
                y, y_inv = v * forward % n, inv * backward % n
                work['signature_multiplications'] += 2
            for t in bucket:
                work['bucket_entries_seen'] += 1
                plus = 0 <= offset + t <= width
                minus = 0 < 2 * t < lifted and 0 <= offset - t <= width
                if not plus and not minus:
                    continue
                u = pow(2, t, n)
                work['orientation_powers'] += 1
                if u != y and u != y_inv:
                    factor = gcd(u - y, n)
                    work['trace_gcds'] += 1
                    if not 1 < factor < n:
                        raise ArithmeticError('invalid mixed trace gcd')
                    return 'trace_mixed_gcd', factor
                for accepted, signed in ((plus and u == y, t), (minus and u == y_inv, -t)):
                    if accepted:
                        total = lower + offset + signed
                        disc = total * total - 4 * n
                        root = isqrt(disc)
                        work['square_tests'] += 1
                        if root * root == disc and (total - root) % 2 == 0:
                            factor = (total - root) // 2
                            if 1 < factor < n:
                                return 'sum_square', factor
    return 'exhausted', None


def cases():
    yield 'fresh-92', FRESH_N, 46
    published = {row['id']: int(row['n']) for row in
                 json.loads((ROOT / 'benchmarks/lifted-period-join.json').read_text())}
    labels = ['lifted-period-holdout-92'] + [f'lifted-period-postdesign-96-{i}' for i in (2, 3, 5, 6)]
    for label in labels:
        n = published[label]
        yield label, n, n.bit_length() // 2


def compare(n, bits, rounds=9, caps=None):
    """Select one product-only layout, then rotate all three evaluations of that layout."""
    if rounds < 1:
        raise ValueError('positive number of rotations required')
    planning_start = perf_counter_ns()
    lower, _, upper = sum_bounds(n, bits)
    probes, base, factor = _fermat_preflight(n, (2,))
    if base is None:
        raise ValueError(f'panel requires base 2 to pass preflight, factor={factor}')
    planning_work = Counter()
    factor, menus, _, plan = join._plan(n, upper - lower, work=planning_work,
                                        **(CAPS if caps is None else caps))
    if factor or plan is None:
        raise ValueError('panel input has no complete plan fitting the published budgets')
    planning_ms = (perf_counter_ns() - planning_start) / 1e6
    times = {mode: [] for mode in MODES}
    methods = {}
    reference = None
    for turn in range(rounds):
        shift = turn % len(MODES)
        for mode in MODES[shift:] + MODES[:shift]:
            work = Counter()
            start = perf_counter_ns()
            prepared = prepare(n, lower, menus, plan, work, mode)
            mid = perf_counter_ns()
            outcome, factor = sweep(n, lower, upper - lower, plan, prepared, work, mode)
            end = perf_counter_ns()
            times[mode].append(((mid - start) / 1e6, (end - mid) / 1e6, (end - start) / 1e6))
            if work['left_visited'] > plan['left_rows'] or work['lookups'] > plan['lookup_bound']:
                raise ArithmeticError('selected bounds exceeded')
            if factor is not None and (not 1 < factor < n or n % factor):
                raise ArithmeticError('invalid split')
            # The comparison also checks decoding order within repeated-key buckets.
            # It happens outside the measured search.
            common = (prepared[2], outcome, factor, work['left_visited'], work['lookups'],
                      work['square_tests'], work['bucket_entries_seen'])
            if reference is None:
                reference = common
            if common != reference:
                raise ArithmeticError('table or recovery differs between evaluators')
            keys = ('right_built', 'right_buckets', 'base_orbits', 'left_visited', 'lookups',
                    'signature_multiplications', 'setup_powers', 'signature_inversions', 'digit_powers',
                    'crt_inverses', 'bucket_entries_seen', 'square_tests', 'orientation_powers', 'trace_gcds')
            methods[mode] = {key: work[key] for key in keys}
            methods[mode]['left_keys_prepared'] = (work['lookups'] if mode == 'stock'
                                                   else work['left_keys_prepared'])
    table, outcome, factor, *_ = reference
    digest = sha256(json.dumps(sorted(table.items()), separators=(',', ':')).encode()).hexdigest()
    factors = list(map(str, sorted((factor, n // factor)))) if factor is not None else []
    return dict(n=str(n), bits=bits, lower=str(lower), upper=str(upper), probes=probes,
                lift=plan['lift'], period=str(plan['period']), setup_local_sites=planning_work['local_sites'],
                lift_candidates=planning_work['lift_candidates'], left_bound=plan['left_rows'],
                lookup_bound=plan['lookup_bound'], table_sha256=digest, outcome=outcome, factors=factors,
                methods=methods, timing_ms=dict(
                    rounds=rounds, common_planning=round(planning_ms, 3),
                    columns=['table_setup', 'sweep', 'setup_and_sweep'],
                    medians={mode: [round(median(row[i] for row in times[mode]), 3) for i in range(3)]
                             for mode in MODES}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    rows = [dict(id=label, **compare(n, b)) for label, n, b in cases()]
    report = dict(seed=SEED.decode(), generator='experiments.affine_radix_holdout.draw_prime',
                  sample_rule='First distinct 46-bit prime pair producing a 92-bit product, indices '
                              'starting at zero, sides p and q. Accepted index 0.',
                  caps=CAPS, timing='Nine rotated rounds, one common measured product-only plan per '
                                   'input. Comparison and primality certification outside timings.',
                  rows=rows)
    if args.verify:
        from scripts.factor import render_certificate, verify_file
        expected = json.loads((ROOT / 'research/lifted-period-traces.json').read_text())
        with TemporaryDirectory() as directory:
            proof = Path(directory) / 'Factorization.lean'
            for row in rows:
                primes = list(map(int, row['factors']))
                if primes:
                    proof.write_text(render_certificate(int(row['n']), primes, certificate_trial_limit=2_000_000))
                    verify_file(proof)
        for row in expected['rows']:
            del row['timing_ms']
        deterministic = dict(report, rows=[{k: v for k, v in row.items() if k != 'timing_ms'} for row in rows])
        if deterministic != expected:
            raise ArithmeticError('deterministic evidence changed')
    if args.out:
        args.out.write_text(json.dumps(report, indent=2) + '\n')
    elif not args.verify:
        print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
