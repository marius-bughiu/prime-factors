"""Compare twelve rationally related residues with one key per sampled integer."""
from math import gcd
from random import Random
from time import perf_counter

from experiments.wide_modulus import product_tree, values_on_tree


def mask(x, n):
    t = x*x % n
    return x*(t-1)*(t-9)*(t+3)*(t-3)*((t-3)**2-36*t) % n


def keys(samples, n):
    """Normalize all rational values with a single modular inverse."""
    squares = [x*x % n for x in samples]
    prefixes = [1]
    for t in squares:
        prefixes.append(prefixes[-1]*(t+3) % n)
    inverse = pow(prefixes[-1], -1, n)
    result = []
    for t, prefix in zip(reversed(squares), reversed(prefixes[:-1])):
        local_inverse = inverse*prefix % n
        inverse = inverse*(t+3) % n
        sextic = (((t-45)*t+135)*t-27) % n
        result.append(pow(sextic*pow(local_inverse, 3, n) % n, 2, n))
    return result[::-1]


def regular_samples(samples, n, work):
    masks = [mask(x, n) for x in samples]
    batch = 1
    for value in masks:
        batch = batch*value % n
    divisor = gcd(batch, n)
    work['setup_gcds'] += 1
    if divisor == 1:
        return None, samples
    # Find an individual witness even when the batch contains both primes.
    retained = []
    for x, value in zip(samples, masks):
        divisor = gcd(value, n)
        work['setup_gcds'] += 1
        if 1 < divisor < n:
            work.update(source='regularity check', witness=[str(x)])
            return divisor, []
        if divisor == 1:
            retained.append(x)
    return None, retained


def directions(x):
    return ((x, 1), (3*x-3, x+3), (x-3, x+1), (-3, x),
            (-x-3, x-1), (-3*x-3, x-3))


def refine_duplicates(samples, values, n, work):
    groups = {}
    for x, key in zip(samples, values):
        previous = groups.setdefault(key, set())
        if x in previous:
            continue
        for y in sorted(previous):
            for direction, (a, b) in enumerate(directions(y)):
                for sign, difference in enumerate((b*x-a, b*x+a)):
                    divisor = gcd(difference, n)
                    work['orientation_gcds'] += 1
                    if 1 < divisor < n:
                        work.update(source='shared key', witness=[str(y), str(x)],
                                    orientation=2*direction+sign, signed_difference=str(difference))
                        return divisor
        previous.add(x)
    return None


def search_values(samples, values, n, work):
    # Equal residues give zero modulo both factors. Keep one representative.
    representatives = dict(zip(values, samples))
    points = list(representatives)
    work['distinct_keys'] = len(points)
    if len(points) < 2:
        return None
    tree = product_tree(points, n)
    polynomial = tree[-1][0]
    derivative = [i*polynomial[i] % n for i in range(1, len(polynomial))]
    rows = values_on_tree(derivative, tree, n)
    work['derivative_values'] = len(rows)
    for i, value in enumerate(rows):
        divisor = gcd(value, n)
        work['row_gcds'] += 1
        if divisor == 1:
            continue
        # The same scan provides a two-seed receipt for a hit, and resolves
        # a saturated row. Distinct keys prevent a saturated difference.
        for j, other in enumerate(points):
            if i == j:
                continue
            divisor = gcd(points[i]-other, n)
            work['pair_gcds'] += 1
            if 1 < divisor < n:
                work.update(source='pair', witness=[str(representatives[points[i]]),
                                                    str(representatives[other])])
                return divisor
        raise ArithmeticError('nonunit derivative had no proper difference')
    return None


def search(n, draws, seed, mode):
    if n <= 1 or draws < 0 or mode not in ('twelve', 'raw', 'matched', 'power'):
        raise ValueError('invalid modulus, sample budget, or mode')
    start = perf_counter()
    rng = Random(seed)
    samples = [rng.randrange(n) for _ in range(draws)]
    work = dict(mode=mode, draws=draws, regular=None, setup_gcds=0, inversions=0,
                distinct_keys=0, derivative_values=0, row_gcds=0, pair_gcds=0, orientation_gcds=0,
                witness=[], source='none')
    factor = None
    if mode in ('twelve', 'matched') and samples:
        factor, samples = regular_samples(samples, n, work)
        if factor is None:
            work['regular'] = len(samples)
    if factor is None and samples:
        values = samples
        if mode == 'twelve':
            values = keys(samples, n)
            work['inversions'] = 1
        elif mode == 'power':
            values = [pow(x, 12, n) for x in samples]
        if mode == 'twelve':
            factor = refine_duplicates(samples, values, n, work)
            if factor is not None:
                work['distinct_keys'] = len(set(values))
        if factor is None:
            factor = search_values(samples, values, n, work)
    return factor, work, perf_counter()-start
