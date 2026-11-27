"""Group complementary labels, or look only for matches at the prime where three is a square."""
from math import gcd
from random import Random
from time import perf_counter

from experiments.opposite_key_polynomial import opposite_factor
from experiments.twelve_residue_collision import keys, refine_duplicates, regular_samples, search_values
from experiments.wide_modulus import product_tree, values_on_tree


def fold(u, n):
    return u*(1-u) % n


def batch_product(values, n):
    result = 1
    for v in values:
        result = result*v % n
    return result


def norm_forms(x, y):
    """Six integral conjugate pairs whose product is the cleared complement equation."""
    for u, v in ((x*y + 3, x-y), (3-x*y, x+y)):
        three_v_squared = 3*v*v
        yield u*u - three_v_squared
        yield (u+3*v)**2 - 4*three_v_squared
        yield (u-3*v)**2 - 4*three_v_squared


def refine_complement(x, y, n, work):
    for index, form in enumerate(norm_forms(x, y)):
        divisor = gcd(form, n)
        work['norm_gcds'] += 1
        if 1 < divisor < n:
            work.update(source='complement norm', branch='complement', norm_index=index,
                        witness=[str(x), str(y)])
            return divisor
    return None


def middle_hit(samples, values, n, work):
    """Test the fixed point of the complement in every sample, including a singleton."""
    terms = [(2*v-1) % n for v in values]
    d = gcd(batch_product(terms, n), n)
    work['middle_gcds'] += 1
    if d == 1:
        return None
    for x, term in zip(samples, terms):
        d = gcd(term, n)
        work['middle_gcds'] += 1
        if 1 < d < n:
            work.update(source='middle', witness=[str(x)])
            return d
        if d == n:
            divisor = refine_complement(x, x, n, work)
            if divisor is not None:
                return divisor
    return None


def shared_fold(samples, values, folded, n, work):
    """Refine a global fold tie, retaining each distinct seed for norm comparisons."""
    groups = {}
    for x, u, key in zip(samples, values, folded):
        previous = groups.setdefault(key, {})
        if x in previous:
            continue
        for y, v in previous.items():
            if u != v:
                for expression, difference in (('original', u-v), ('complement', u+v-1)):
                    d = gcd(difference, n)
                    work['shared_gcds'] += 1
                    if 1 < d < n:
                        work.update(source='shared fold', branch=expression, witness=[str(y), str(x)])
                        return d
            if (u+v-1) % n == 0:
                divisor = refine_complement(y, x, n, work)
                if divisor is not None:
                    return divisor
        previous[x] = u
    return None


def target(samples, values, n, work):
    """All ordered complement comparisons, including a position paired with itself."""
    if not values:
        return None
    points = [(2*u-1) % n for u in values]
    tree = product_tree(points, n)
    poly = tree[-1][0]
    reflected = [c if i % 2 == 0 else (-c) % n for i, c in enumerate(poly)]
    rows = values_on_tree(reflected, tree, n)
    work['target_values'] = len(rows)
    divisor = gcd(batch_product(rows, n), n)
    work['target_gcds'] = 1
    if divisor == n:
        raise ArithmeticError('all regular complement comparisons cannot saturate a mixed semiprime')
    if divisor == 1:
        return None
    work.update(source='complement product')
    return divisor


def search(n, draws, seed, mode='folded'):
    if n < 2 or draws < 0 or mode not in ('folded', 'target', 'euclid'):
        raise ValueError('invalid input or search mode')
    if mode in ('target', 'euclid') and n % 12 not in (5, 7):
        raise ValueError('the directed comparison requires remainder 5 or 7 modulo 12')
    start = perf_counter()
    rng = Random(seed)
    samples = [rng.randrange(n) for _ in range(draws)]
    work = dict(mode=mode, draws=draws, regular=None, setup_gcds=0, inversions=0, middle_gcds=0,
                shared_gcds=0, norm_gcds=0, target_values=0, target_gcds=0, orientation_gcds=0, row_gcds=0,
                pair_gcds=0, distinct_keys=0, derivative_values=0, euclid_gcds=0, euclid_inversions=0,
                coefficient_updates=0, source='none', witness=[])
    divisor = None
    if samples:
        divisor, samples = regular_samples(samples, n, work)
    if divisor is None:
        work['regular'] = len(samples)
    if samples:
        values = keys(samples, n)
        work['inversions'] = 1
        if mode == 'target':
            divisor = target(samples, values, n, work)
        elif mode == 'euclid':
            divisor = opposite_factor(values, n, work)
        else:
            divisor = middle_hit(samples, values, n, work)
            if divisor is None:
                divisor = refine_duplicates(samples, values, n, work)
            if divisor is None:
                folded = [fold(u, n) for u in values]
                work['distinct_keys'] = len(set(folded))
                divisor = shared_fold(samples, values, folded, n, work)
                if divisor is None:
                    divisor = search_values(samples, folded, n, work)
                    if divisor is not None:
                        x, y = map(int, work['witness'])
                        u, v = keys([x,y], n)
                        work['branch'] = 'original' if (u-v) % divisor == 0 else 'complement'
    return divisor, work, perf_counter()-start
