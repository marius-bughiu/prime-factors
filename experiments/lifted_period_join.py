"""Join on a short sum wheel, lifting its right residues to an integer multiple of the period."""

from collections import Counter, defaultdict
from math import gcd, isqrt, prod

from .sum_signature_join import _fermat_preflight, _moduli
from .trace_folded_right import _layers, _walk


def _greedy(moduli, menus):
    halves = [[], []]
    sizes = [1, 1]
    for m in sorted(moduli, key=lambda m: -len(menus[m])):
        side = int(sizes[1] < sizes[0])
        halves[side].append(m)
        sizes[side] *= len(menus[m])
    return halves, sizes


def _wheel_options(prefix, power_limit, drop_limit):
    for drop in range(min(drop_limit, len(prefix)) + 1):
        selected = prefix[:len(prefix) - drop]
        yield drop, selected, None
        for i, m in enumerate(selected[:4]):
            prime = 2 if m == 4 else m
            power = m * prime
            while power <= power_limit:
                yield drop, selected[:i] + [power] + selected[i + 1:], [m, power]
                power *= prime


def _plan(n, width, max_right, max_visited, max_lookups, power_limit, drop_limit, budget, work,
          full_period_only=False):
    menus = {}
    prefix = []
    period = 1
    for m in _moduli():
        if period > width:
            break
        work['wheel_gcds'] += 1
        common = gcd(n, m)
        if 1 < common < n:
            return common, menus, None, None
        prefix.append(m)
        period *= m

    best = None
    feasible = None
    for drop, moduli, upgrade in _wheel_options(prefix, power_limit, drop_limit):
        period = prod(moduli)
        if full_period_only and period <= width:
            continue
        if work['lift_candidates'] >= budget:
            work['plan_budget_hit'] = 1
            break
        for m in moduli:
            if m not in menus:
                values = set()
                for x in range(1, m):
                    work['local_sites'] += 1
                    if gcd(x, m) == 1:
                        work['local_inverses'] += 1
                        values.add((x + n * pow(x, -1, m)) % m)
                menus[m] = values
        work['wheel_layouts'] += 1
        quotient = width // period
        halves, sizes = _greedy(moduli, menus)
        for side in (0, 1):
            left, right = halves[side], halves[1 - side]
            rows, raw = sizes[side], sizes[1 - side]
            zero = int(all(0 in menus[m] for m in right))
            midpoint = period // 2
            half = int(
                period % 2 == 0
                and all(midpoint % m in menus[m] for m in right)
                and all(midpoint % m == 0 for m in left)
            )
            lift = 1
            while True:
                if work['lift_candidates'] >= budget:
                    work['plan_budget_hit'] = 1
                    return None, menus, best, feasible
                work['lift_candidates'] += 1
                fixed = zero + (zero if lift % 2 == 0 else half)
                stored = (lift * raw + fixed) // 2
                wraps = quotient // lift + 2
                query_bound = rows * wraps
                score = stored + query_bound
                eligible = stored <= max_right and rows <= max_visited and query_bound <= max_lookups
                if lift == 1:
                    keys = ['unlifted_reference']
                    if period > width:
                        keys.append('full_period_reference')
                    if eligible:
                        keys.extend([f"feasible_{key}" for key in keys])
                    for key in keys:
                        if key not in work or score < work[key]['score']:
                            work[key] = dict(score=score, right_entries=stored, left_rows=rows,
                                             lookup_bound=query_bound, drop=drop, upgrade=upgrade)
                improves_best = best is None or score < best['score']
                improves_feasible = eligible and (feasible is None or score < feasible['score'])
                if improves_best or improves_feasible:
                    plan = dict(moduli=moduli, period=period, drop=drop, upgrade=upgrade, lift=lift,
                                lifted_period=period * lift, left_moduli=left, right_moduli=right,
                                left_rows=rows, raw_right=raw, zero=zero, half=half, fixed=fixed,
                                right_entries=stored, wraps_per_row=wraps, lookup_bound=query_bound,
                                score=score)
                    if improves_best:
                        best = plan
                    if improves_feasible:
                        feasible = plan
                # Inside a constant-quotient block the right table size is nondecreasing.
                q = quotient // lift
                if q == 0:
                    break
                lift = quotient // q + 1
    return None, menus, best, feasible


def _lifted_table(layers, n, period, lift, power, back, lifted_power, lifted_back, work):
    table = defaultdict(list)
    Q = period * lift
    for r, u, inv in _walk(layers, period, n, 1, 1, True, False, work):
        work['base_orbits'] += 1
        if 2 * r > period:
            r = period - r
            u, inv = power * inv % n, back * u % n
            work['signature_multiplications'] += 2
        fixed = r == 0 or 2 * r == period
        copies = (Q // 2 - r) // period + 1 if fixed else lift
        for copy in range(copies):
            x = r + copy * period
            if 2 * x <= Q:
                t, trace = x, (u + inv) % n
            else:
                t, trace = Q - x, (lifted_power * inv + lifted_back * u) % n
                work['signature_multiplications'] += 2
            table[trace].append(t)
            work['right_built'] += 1
            if copy + 1 < copies:
                u, inv = power * u % n, back * inv % n
                work['signature_multiplications'] += 2
    return table


def _prepare(n, base, lower, menus, plan, work):
    period, lift = plan['period'], plan['lift']

    def shifted(moduli):
        return [(m, {(v - lower) % m for v in menus[m]}) for m in moduli]

    power = pow(base, period, n)
    back = pow(power, -1, n)
    fitted_power = pow(power, lift, n)
    fitted_back = pow(fitted_power, -1, n)
    center, right = _layers(shifted(plan['right_moduli']), period, n, base, power, back,
                            lower, right=True, work=work)
    _, left = _layers(shifted(plan['left_moduli']), period, n, base, power, back,
                      lower, right=False, work=work)
    table = _lifted_table(right, n, period, lift, power, back, fitted_power, fitted_back, work)
    if work['right_built'] != plan['right_entries']:
        raise ArithmeticError('lifted orbit enumeration disagrees with the planned count')
    work['right_buckets'] = len(table)
    exponent = n + 1 - lower - center
    start = pow(base, exponent, n)
    inverse_start = pow(start, -1, n)
    work['setup_powers'] += 3
    work['signature_inversions'] += 3 + int(exponent < 0)
    return left, center, table, start, inverse_start, fitted_power, fitted_back


def _sweep(n, base, lower, first_offset, last_offset, plan, prepared, reverse, work):
    left, center, table, start, inverse_start, fitted_power, fitted_back = prepared
    period, Q = plan['period'], plan['lifted_period']
    first_powers = {}
    for a, y, inv in _walk(left, period, n, start, inverse_start, False, reverse, work):
        work['left_visited'] += 1
        first = -((last_offset + Q // 2 - a - center) // Q)
        last = (a + center + Q // 2 - first_offset) // Q
        if first > last:
            continue
        if first:
            if first not in first_powers:
                if first > 0:
                    positive, negative = fitted_power, fitted_back
                else:
                    positive, negative = fitted_back, fitted_power
                first_powers[first] = pow(positive, abs(first), n), pow(negative, abs(first), n)
                work['setup_powers'] += 2
            forward, backward = first_powers[first]
            y, inv = y * forward % n, inv * backward % n
            work['signature_multiplications'] += 2
        for k in range(first, last + 1):
            work['lookups'] += 1
            offset = a + center - k * Q
            for t in table.get((y + inv) % n, ()):
                work['bucket_entries_seen'] += 1
                plus = first_offset <= offset + t <= last_offset
                minus = 0 < 2 * t < Q and first_offset <= offset - t <= last_offset
                if not plus and not minus:
                    continue
                u = pow(base, t, n)
                work['orientation_powers'] += 1
                if u != y and u != inv:
                    factor = gcd(u - y, n)
                    work['trace_gcds'] += 1
                    if not 1 < factor < n:
                        raise ArithmeticError('invalid mixed trace gcd')
                    return 'trace_mixed_gcd', factor
                orientations = ((plus and u == y, t), (minus and u == inv, -t))
                for accepted, signed in orientations:
                    if not accepted:
                        continue
                    total = lower + offset + signed
                    discriminant = total * total - 4 * n
                    root = isqrt(discriminant)
                    work['square_tests'] += 1
                    if root * root == discriminant and (total - root) % 2 == 0:
                        factor = (total - root) // 2
                        if 1 < factor < n:
                            return 'sum_square', factor
            if k != last:
                y, inv = y * fitted_power % n, inv * fitted_back % n
                work['signature_multiplications'] += 2
    return 'exhausted', None


def search(n, *, max_right=20000, max_visited=32256, max_lookups=100000, reverse=True,
           candidates=(2,), sum_interval=None, power_limit=10000, drop_limit=3,
           plan_budget=2000000, plan_only=False, full_period_only=False):
    """Choose a product-only setup whose *complete* row and lookup bounds fit the caps.

    The score counts stored positions plus guaranteed lookup budget; powering, local
    inverses and candidate processing are charged separately in work. A nonfeasible
    input still reports its best inspected uncapped plan. full_period_only
    retains prime-power replacements while requiring the wheel itself to span the interval.
    """
    limits = (max_right, max_visited, max_lookups, power_limit, drop_limit, plan_budget)
    if n < 9 or n % 2 == 0 or min(limits) < 0:
        raise ValueError('expected an odd input at least 9 and nonnegative budgets')
    lower, upper = isqrt(4 * n - 1) + 1, isqrt(9 * n // 2)
    if sum_interval is not None:
        lower, upper = max(lower, sum_interval[0]), min(upper, sum_interval[1])
    counters = (
        'wheel_gcds', 'local_sites', 'local_inverses', 'wheel_layouts', 'lift_candidates',
        'plan_budget_hit', 'right_built', 'right_buckets', 'base_orbits', 'left_visited',
        'lookups', 'bucket_entries_seen', 'orientation_powers', 'trace_gcds', 'square_tests',
        'setup_powers', 'signature_multiplications', 'signature_inversions', 'crt_inverses',
        'digit_powers',
    )
    work = Counter(dict.fromkeys(counters, 0))
    probes = []
    best = plan = None

    def finish(outcome, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError('invalid divisor')
        if plan is not None:
            if work['lookups'] > plan['lookup_bound'] or work['left_visited'] > plan['left_rows']:
                raise ArithmeticError('search exceeded its guaranteed work bound')
            work['left_unvisited'] = plan['left_rows'] - work['left_visited']
        factors = list(map(str, sorted((factor, n // factor)))) if factor else []
        caps = dict(right=max_right, visited=max_visited, lookups=max_lookups, planning=plan_budget)
        return dict(outcome=outcome, factors=factors,
                    lower=str(lower), upper=str(upper), probes=probes, best_plan=best,
                    feasible_plan=plan, work=dict(work), caps=caps)

    if lower > upper:
        return finish('empty_interval')
    probes, base, factor = _fermat_preflight(n, candidates)
    if factor:
        return finish('preflight_gcd', factor)
    if base is None:
        return finish('no_witness_within_cap')
    factor, menus, best, plan = _plan(
        n, upper - lower, max_right=max_right, max_visited=max_visited, max_lookups=max_lookups,
        power_limit=power_limit, drop_limit=drop_limit, budget=plan_budget, work=work,
        full_period_only=full_period_only,
    )
    if factor:
        return finish('local_gcd', factor)
    if plan is None:
        return finish('no_complete_plan_within_caps')
    if plan_only:
        return finish('planned')
    prepared = _prepare(n, base, lower, menus, plan, work)
    outcome, factor = _sweep(n, base, lower, 0, upper - lower, plan, prepared, reverse, work)
    return finish(outcome, factor)
