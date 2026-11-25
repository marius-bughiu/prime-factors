"""Enumerate the balanced factor pairs of an odd integer using one trace per residue pair."""

from collections import Counter
from math import gcd, isqrt

from .curved_weight_interval import curved_interval
from .reduced_weight_discriminant import discriminant_root
from .powered_order import prime_powers
from .short_basis_sieve import reduced_lattice_basis


def choose_radix(n, volume):
    """Choose a smooth radix coprime to n whose cube strictly exceeds volume."""
    low, high = 0, 1 << ((volume.bit_length() + 2) // 3)
    while low + 1 < high:
        middle = (low + high) // 2
        if middle**3 <= volume:
            low = middle
        else:
            high = middle
    return smooth_radix(n, max(2, low+1))


def smooth_radix(n, target):
    """Round a positive threshold upward to a smooth modulus coprime to odd n."""
    wheel, candidate, primes = 1, 2, []
    while wheel * candidate <= target // 16:
        if all(candidate % p for p in primes if p*p <= candidate):
            primes.append(candidate)
            if n % candidate:
                wheel *= candidate
        candidate += 1
    multiplier = (target + wheel - 1) // wheel
    if gcd(multiplier, n) > 1:
        multiplier = 1 << (multiplier - 1).bit_length()
    return wheel * multiplier


def residue_pairs(n, radix, work):
    """Count swap orbits exactly and stream their lexicographic CRT representatives."""
    stages = []
    units = fixed = 1
    for p, m in prime_powers(radix, work).items():
        scale = radix // m
        scale *= pow(scale, -1, m)
        digits = []
        for u in range(1, m):
            if u % p:
                w = n * pow(u, -1, m) % m
                digits.append((scale*u % radix, scale*w % radix, u-w))
        canonical = [row for row in digits if row[2] <= 0]
        stages.append((digits, canonical))
        units *= len(digits)
        fixed *= sum(order == 0 for _, _, order in canonical)
        work['table_entries'] += len(digits)

    def extend(index, x, y, tied):
        if index == len(stages):
            yield x % radix, y % radix
            return
        digits, canonical = stages[index]
        for a, b, order in canonical if tied else digits:
            yield from extend(index+1, x+a, y+b, tied and order == 0)

    return (units + fixed) // 2, extend(0, 0, 0, True)


def weight_interval(radix, slope, lower, upper, gap, work):
    """Minimize the range over the midpoint/half-gap rectangle in this lattice."""
    h, g = upper-lower, 2*gap

    def transform(pair):
        a, b = pair
        center, spread = h*(a+b), g*(a-b)
        return center+spread, center-spread

    first, second = reduced_lattice_basis(radix, slope, transform, work)
    a, b = first
    c, d = second
    choices = (first, second, (c+a, d+b), (c-a, d-b))
    a, b = min(choices, key=lambda v: max(map(abs, transform(v))))
    left, right = sorted(((a+b)*lower, (a+b)*upper))
    spread = gap*abs(a-b)
    left, right = left-spread, right+spread
    if ((a, b) == (0, 0) or (b-slope*a) % radix or right-left >= radix**2):
        raise ArithmeticError('failed to certify the one-trace interval')
    return a, b, left, right


def possible_x(n, a, b, trace, work, square_divisor=1):
    """Integer solutions of b*x² - trace*x + a*n = 0, including linear cases."""
    if b == 0:
        if trace and a*n % trace == 0:
            yield a*n // trace
        return
    disc = trace*trace - 4*a*b*n
    if square_divisor > 1:
        root = discriminant_root(disc, square_divisor, work)
        if root is None:
            return
    else:
        if disc < 0:
            return
        work['square_tests'] += 1
        root = isqrt(disc)
        if root*root != disc:
            return
    for numerator in {trace-root, trace+root}:
        if numerator % (2*b) == 0:
            yield numerator // (2*b)


def search(n, max_orbits=None, *, reduce_discriminant=False, curve=False):
    """Return all balanced pairs in visited orbits and account for every unvisited orbit."""
    if n < 3 or n % 2 == 0 or (max_orbits is not None and max_orbits < 0):
        raise ValueError('expected an odd n >= 3 and a nonnegative optional orbit budget')
    lower, upper, gap = isqrt(n-1)+1, isqrt(9*n//8), isqrt(n//8)
    work, hits = Counter(), set()
    if upper <= lower:
        total = int(upper == lower)
        visited = total if max_orbits is None else min(total, max_orbits)
        if visited:
            work['square_tests'] = 1
            delta = lower*lower-n
            root = isqrt(delta)
            x, y = lower-root, lower+root
            if delta == root*root and 1 < x and y <= 2*x:
                hits.add((x, y))
        radix = None
    else:
        radix = choose_radix(n, 4*(upper-lower)*(2*gap))
        total, representatives = residue_pairs(n, radix, work)
        visited = 0
        step = radix*radix
        inv_n = pow(n, -1, radix)
        weights = {}
        # range supports orbit budgets larger than a machine word.
        if max_orbits is not None and max_orbits < total:
            representatives = (pair for _, pair in zip(range(max_orbits), representatives))
        square_divisor = radix if reduce_discriminant else 1
        for u, w in representatives:
            visited += 1
            inverse = w * inv_n % radix
            slope = w * inverse % radix
            if slope not in weights:
                a, b, left, right = weight_interval(radix, slope, lower, upper, gap, work)
                if curve:
                    left, right = curved_interval(n, a, b, left, right)
                weights[slope] = a, b, left, right
                work['weight_choices'] += 1
            a, b, left, right = weights[slope]
            lift = w + radix * (((n-u*w)//radix * inverse) % radix)
            trace = left + (a*lift+b*u-left) % step
            if trace > right:
                continue
            work['candidate_traces'] += 1
            for x in possible_x(n, a, b, trace, work, square_divisor):
                if x <= 1 or x % radix != u or n % x:
                    continue
                y = n // x
                if y % radix == w and max(x, y) <= 2*min(x, y):
                    hits.add(tuple(sorted((x, y))))
    return dict(radix=radix, total_orbits=total, visited_orbits=visited,
                remaining_orbits=total-visited, weight_choices=work['weight_choices'],
                candidate_traces=work['candidate_traces'], square_tests=work['square_tests'],
                table_entries=work['table_entries'], gauss_iterations=work['gauss_iterations'],
                reduced_discriminant=reduce_discriminant,
                discriminant_work={k: work[k] for k in (
                    'nonnegative_discriminants', 'max_full_radicand_bits', 'max_reduced_radicand_bits',
                    'full_radicand_bits', 'reduced_radicand_bits')} if reduce_discriminant else {},
                pairs=[[str(x), str(y)] for x, y in sorted(hits)])
