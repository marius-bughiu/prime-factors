"""Store one centered CRT position per sign orbit and join on the unit trace u + 1/u.

Each local menu of sums x+N/x is closed under negation. The ordinary right
residues already subtract the lower interval endpoint L, so their center C
has value -L on the right moduli and zero on the left. For a left offset a,
the two possible sums are L+a+C-k*M ± t with 0 ≤ t ≤ M/2. Their powers
can share one trace. A collision with different signs at the two primes
gives a divisor directly via the difference of the corresponding units.
"""

from bisect import bisect_left, bisect_right
from collections import defaultdict
from math import gcd, prod


def orbit_count(groups, lower, ordinary_count):
    """Fixed points have local centered sum 0, or m/2 when m is even."""
    fixed = prod(int((-lower) % m in values) +
                 int(m % 2 == 0 and (m//2-lower) % m in values)
                 for m, values in groups)
    return (ordinary_count + fixed)//2, fixed


def _layers(groups, period, n, base, period_power, period_inverse, lower, right, work):
    """Compute the CRT center and paired multipliers for regular and wrapped edges."""
    center = 0
    layers = []
    for m, values in sorted(groups, key=lambda group: len(group[1])):
        other = period//m
        basis = other * pow(other, -1, m)
        work['crt_inverses'] += 1
        if right:
            center = (center - lower*basis) % period
            values = {(v+lower) % m for v in values}
        if values == {0}:
            continue
        all_choices = []
        representatives = []
        for v in sorted(values):
            digit = basis*v % period
            plain = inverse = wrap = inv_wrap = 1
            if digit:
                plain = pow(base, digit, n)
                inverse = pow(plain, -1, n)
                work['digit_powers'] += 1
                work['setup_powers'] += 1
                work['signature_inversions'] += 1
                if right:
                    wrap, inv_wrap = plain*period_inverse % n, inverse*period_power % n
                else:
                    plain, inverse = inverse, plain
                    wrap, inv_wrap = plain*period_power % n, inverse*period_inverse % n
                work['signature_multiplications'] += 2
            negative = (-v) % m
            choice = (digit, plain, inverse, wrap, inv_wrap, v != negative)
            all_choices.append(choice)
            if v <= negative:
                representatives.append(choice)
        layers.append((all_choices, representatives))
    return center, layers


def _walk(layers, period, n, start, start_inverse, restrict_sign, reverse, work):
    """The first non-fixed *local* residue sets the sign before the remaining digits branch."""
    if not layers:
        yield 0, start, start_inverse
        return
    order = reversed if reverse else iter
    stack = [(0, start, start_inverse, restrict_sign, order(layers[0][int(restrict_sign)]))]
    while stack:
        a, u, inv, restricted, choices = stack[-1]
        choice = next(choices, None)
        if choice is None:
            stack.pop()
            continue
        digit, plain, inverse, wrapped, inv_wrapped, nonfixed = choice
        value = a + digit
        if digit:
            if value >= period:
                value -= period
                plain, inverse = wrapped, inv_wrapped
            u, inv = u*plain % n, inv*inverse % n
            work['signature_multiplications'] += 2
        if len(stack) == len(layers):
            yield value, u, inv
        else:
            restricted = restricted and not nonfixed
            choices = order(layers[len(stack)][int(restricted)])
            stack.append((value, u, inv, restricted, choices))


def _right_table(layers, period, n, power, inverse, work):
    buckets = defaultdict(list)
    for raw, u, inv in _walk(layers, period, n, 1, 1, True, False, work):
        work['right_orbits_visited'] += 1
        t = raw
        if 2*raw > period:
            t = period-raw
            u, inv = power*inv % n, inverse*u % n
            work['signature_multiplications'] += 2
        buckets[(u+inv) % n].append(t)
        work['right_built'] += 1
    for bucket in buckets.values():
        bucket.sort()
    work['right_buckets'] = len(buckets)
    return buckets


def _targets(a, center, width, period, power, inverse, squares, n, y, inv, work):
    """Shift the public target only when an oriented position can fall in the interval."""
    half = period//2
    first = -((width+half-a-center)//period)
    last = (a+center+half)//period
    for k in range(first, last+1):
        if k == 0:
            yield k, y, inv
            continue
        if k == 2:
            if not squares:
                squares.extend((power*power % n, inverse*inverse % n))
                work['signature_multiplications'] += 2
            multiplier, back = squares
        elif k == 1:
            multiplier, back = power, inverse
        else:
            # 0 <= a,center < period and 0 <= width < period imply -1 <= k <= 2.
            assert k == -1
            multiplier, back = inverse, power
        work['signature_multiplications'] += 2
        yield k, y*multiplier % n, inv*back % n


def events(n, base, lower, width, period, left, right, max_visited, reverse, work):
    """Yield (matching sum, None) or (None, proper divisor) under the caller's caps."""
    power = pow(base, period, n)
    inverse = pow(power, -1, n)
    work['setup_powers'] += 1
    work['signature_inversions'] += 1
    center, right_layers = _layers(right, period, n, base, power, inverse, lower, True, work)
    _, left_layers = _layers(left, period, n, base, power, inverse, lower, False, work)
    work['trace_center'] = center
    buckets = _right_table(right_layers, period, n, power, inverse, work)
    exponent = n+1-lower-center
    start = pow(base, abs(exponent), n)
    start_inverse = pow(start, -1, n)
    work['setup_powers'] += 1
    work['signature_inversions'] += 1
    if exponent < 0:
        start, start_inverse = start_inverse, start
    squares = []
    for a, y, inv in _walk(left_layers, period, n, start, start_inverse, False, reverse, work):
        work['left_visited'] += 1
        work['left_unvisited'] -= 1
        for k, target, inv_target in _targets(a, center, width, period, power, inverse,
                                               squares, n, y, inv, work):
            trace = (target+inv_target) % n
            work['lookups'] += 1
            bucket = buckets.get(trace)
            if not bucket:
                continue
            work['matched_range_queries'] += 1
            offset = a+center-k*period
            for sign in (1, -1):
                if sign == 1:
                    lo, hi = max(0, -offset), min(period//2, width-offset)
                else:
                    # The possible self-opposite positions are emitted only with plus sign.
                    lo, hi = max(1, offset-width), min((period-1)//2, offset)
                if lo > hi:
                    continue
                first = bisect_left(bucket, lo)
                stop = bisect_right(bucket, hi)
                for index in range(first, stop):
                    t = bucket[index]
                    u = pow(base, t, n)
                    work['orientation_powers'] += 1
                    work['trace_matches'] += 1
                    same = u == target
                    mate = u == inv_target
                    if not same and not mate:
                        divisor = gcd(target-u, n)
                        work['trace_gcds'] += 1
                        if not 1 < divisor < n:
                            raise ArithmeticError('trace collision failed its factor identity')
                        work['trace_split'] = dict(a=a, k=k, t=t, u=str(u), target=str(target),
                                                   trace=str(trace), sign=sign, divisor=str(divisor))
                        yield None, divisor
                        return
                    if (sign == 1 and same) or (sign == -1 and mate):
                        yield lower+offset+sign*t, None
        if work['left_visited'] == max_visited:
            break
