"""Report stationary weighted traces from two lists of CRT half sums."""

from bisect import bisect_left, bisect_right
from collections import Counter, defaultdict
from itertools import product
from math import gcd, isqrt, prod

from . import hex_weight_interval, midpoint_weights
from .curved_weight_interval import curved_interval
from .powered_order import prime_powers


def local_slope_tables(n, radix, work):
    """Precompute local lifts of x and n/x to m², grouped by n/x² modulo m."""
    step = radix*radix
    tables, moduli = [], []
    units, fixed = 1, 1
    for p, m in prime_powers(radix, work).items():
        moduli.append(m)
        basis = radix//m * pow(radix//m, -1, m)
        square = m*m
        lift_basis = step//square * pow(step//square, -1, square)
        groups = defaultdict(list)
        for x in range(1, m):
            if x % p == 0:
                continue
            inverse = pow(x, -1, square)
            y = n*inverse % square
            slope = y*inverse % m
            groups[slope].append((lift_basis*x % step, lift_basis*y % step, x <= y % m))
        local_units = sum(map(len, groups.values()))
        units *= local_units
        fixed *= len(groups.get(1, ()))
        work['table_entries'] += local_units
        rows = []
        for slope, digits in groups.items():
            all_digits = [(x, y) for x, y, _ in digits]
            canonical = [(x, y) for x, y, first in digits if first]
            rows.append((slope*basis % radix, slope != 1, all_digits, canonical))
        tables.append(rows)
    return tables, moduli, (units+fixed)//2


def split_lists(configuration, a, b, step):
    """Discard equal local traces and balance the products of the remaining list sizes."""
    tied, offset, orbits = True, 0, 1
    choices = []
    for _, differs, digits, canonical in configuration:
        selected = canonical if tied and differs else digits
        tied = tied and not differs
        orbits *= len(selected)
        traces = {(a*y+b*x) % step for x, y in selected}
        if len(traces) == 1:
            offset += next(iter(traces))
        else:
            choices.append(traces)
    sides, sizes = ([], []), [1, 1]
    for traces in sorted(choices, key=len, reverse=True):
        side = 0 if sizes[0] <= sizes[1] else 1
        sides[side].append(traces)
        sizes[side] *= len(traces)
    return sides, sizes, offset, orbits


def half_sums(groups, step):
    values = [0]
    for group in groups:
        values = [(x+y) % step for x in values for y in group]
    return values


def joined_traces(sides, offset, left, right, step):
    """Report every sum in [left,right] after reduction to the interval starting at left."""
    alpha = half_sums(sides[0], step)
    beta = sorted(half_sums(sides[1], step))
    width = right-left
    for x in alpha:
        x = (x+offset-left) % step
        end = bisect_right(beta, width-x)
        for j in range(end):
            yield left+x+beta[j]
        start = bisect_left(beta, step-x)
        end = bisect_right(beta, step+width-x)
        for j in range(start, end):
            yield left+x+beta[j]-step


def in_slope(x, y, slope, radix, moduli):
    if y % radix != (slope*x) % radix:
        return False
    for m in moduli:
        u, w = x % m, y % m
        if u != w:
            return u < w
    return True


def search(n, *, multiplier=1, max_slopes=None, max_half_entries=65536, geometry='rectangle', curve=False):
    """Run a complete or budgeted search, with a per-slope limit on each half list."""
    if n < 3 or n % 2 == 0 or multiplier < 1 or gcd(n, multiplier) != 1:
        raise ValueError('expected odd N >= 3 and a positive coprime radix multiplier')
    if geometry not in ('rectangle', 'hexagon', 'hexagon_slope'):
        raise ValueError('unknown weight geometry')
    if any(k is not None and k < 0 for k in (max_slopes, max_half_entries)):
        raise ValueError('budgets must be nonnegative')
    lo, hi, gap = isqrt(n-1)+1, isqrt(9*n//8), isqrt(n//8)
    if hi <= lo:
        direct = midpoint_weights.search(n, max_orbits=max_slopes)
        return dict(radix=None, outcome='complete' if not direct['remaining_orbits'] else 'slope_limit',
                    total_slopes=direct['total_orbits'], visited_slopes=direct['visited_orbits'],
                    remaining_slopes=direct['remaining_orbits'], total_orbits=direct['total_orbits'],
                    remaining_orbits=direct['remaining_orbits'], pairs=direct['pairs'],
                    work=dict(square_tests=direct['square_tests'], candidate_traces=direct['visited_orbits']))
    height, gap_width = hi-lo, 2*gap
    work, hits = Counter(), set()
    if geometry == 'rectangle':
        radix = midpoint_weights.choose_radix(n, 4*height*gap_width)
        weight_interval = midpoint_weights.weight_interval
    else:
        if geometry == 'hexagon_slope':
            radix = hex_weight_interval.choose_slope_radix(n, height, gap_width, work, multiplier)
        else:
            radix = midpoint_weights.choose_radix(n, hex_weight_interval.cube_threshold(height, gap_width))
        weight_interval = hex_weight_interval.weight_interval
    radix *= multiplier
    step = radix*radix
    tables, moduli, total_orbits = local_slope_tables(n, radix, work)
    total_slopes = prod(map(len, tables))
    outcome, visited, used_orbits = 'complete', 0, 0
    for configuration in product(*tables):
        if visited == max_slopes:
            outcome = 'slope_limit'
            break
        slope = sum(row[0] for row in configuration) % radix
        a, b, left, right = weight_interval(radix, slope, lo, hi, gap, work)
        if curve:
            left, right = curved_interval(n, a, b, left, right)
        sides, sizes, offset, orbits = split_lists(configuration, a, b, step)
        if max_half_entries is not None and max(sizes) > max_half_entries:
            work['next_half_size'] = max(sizes)
            outcome = 'half_list_limit'
            break
        visited += 1
        used_orbits += orbits
        work['distinct_trace_residues'] += prod(sizes)
        work['half_entries'] += sum(sizes)
        for trace in joined_traces(sides, offset, left, right, step):
            work['candidate_traces'] += 1
            for x in midpoint_weights.possible_x(n, a, b, trace, work):
                if x <= 1 or n % x:
                    continue
                y = n//x
                if y > 1 and max(x, y) <= 2*min(x, y) and in_slope(x, y, slope, radix, moduli):
                    hits.add(tuple(sorted((x, y))))
    return dict(radix=radix, outcome=outcome, total_slopes=total_slopes, visited_slopes=visited,
                remaining_slopes=total_slopes-visited, total_orbits=total_orbits,
                remaining_orbits=total_orbits-used_orbits, work=dict(work),
                pairs=[[str(p), str(q)] for p, q in sorted(hits)])
