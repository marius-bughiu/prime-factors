"""Use two witnessed equal powers inside a sum interval to resolve an ambiguous join."""

from math import gcd, isqrt


def difference_tree(values):
    """Build a range-gcd tree over consecutive differences of a sorted bucket."""
    size = 1
    while size < len(values)-1:
        size *= 2
    tree = [0] * (2*size)
    for j in range(len(values)-1):
        tree[size+j] = values[j+1]-values[j]
    for j in range(size-1, 0, -1):
        tree[j] = gcd(tree[2*j], tree[2*j+1])
    return tree, size


def range_gcd(tree, size, start, stop):
    lo, hi = size+start, size+stop
    result = 0
    while lo < hi:
        if lo % 2:
            result = gcd(result, tree[lo])
            lo += 1
        if hi % 2:
            hi -= 1
            result = gcd(result, tree[hi])
        lo //= 2
        hi //= 2
    return result


def common_gap(anchor, buckets, ranges):
    """Gcd of every matched sum minus one anchor, without expanding the hits."""
    trees = {}
    value = 0
    queries = 0
    for key, offset, start, stop in ranges:
        bucket = buckets[key]
        value = gcd(value, offset+bucket[start]-anchor)
        if stop-start >= 2:
            if key not in trees:
                trees[key] = difference_tree(bucket)
            tree, size = trees[key]
            value = gcd(value, range_gcd(tree, size, start, stop-1))
            queries += 1
    return value, queries, sum(len(tree) for tree, _ in trees.values())


def factor_from_gap(n, base, lower, upper, first, second, trial_cap, *, common_multiple=None):
    """Charge ordinary trial division of the short gap and every modular test.

    Given a complete factorization of any positive difference of two matching
    sums, strip it to the exact order modulo n. Every proposed divisor is checked.
    """
    if trial_cap < 0 or not lower <= min(first, second) < max(first, second) <= upper:
        raise ValueError('expected two distinct in-range sums and a nonnegative trial cap')
    difference = abs(first-second)
    gap = difference if common_multiple is None else common_multiple
    if gap < 1 or difference % gap:
        raise ValueError('expected a positive common gap dividing the sample difference')
    work = dict(sums=[str(first), str(second)], gap=str(gap), sample_gap=str(difference),
                trial_cap=trial_cap, trial_divisions=0, factor_divisions=0,
                remaining=str(gap), order_powers=0, projection_gcds=0, order=None,
                class_modulus=None, candidate=None, square_tests=0)
    if pow(base, gap, n) != 1:
        raise ValueError('supplied sums have different powers')
    work['order_powers'] += 1

    def finish(status, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError('invalid projected divisor')
        return status, factor, work

    order = gap
    primes = []

    def strip(ell):
        nonlocal order
        primes.append(ell)
        while order % ell == 0:
            reduced = order // ell
            residue = pow(base, reduced, n)
            work['order_powers'] += 1
            work['projection_gcds'] += 1
            shared = gcd(residue-1, n)
            if 1 < shared < n:
                return shared
            if shared != n:
                break
            order = reduced
        return None

    cofactor = gap
    divisor = 2
    while divisor * divisor <= cofactor:
        if work['trial_divisions'] == trial_cap:
            return finish('gap_budget')
        work['trial_divisions'] += 1
        if cofactor % divisor == 0:
            while cofactor % divisor == 0:
                cofactor //= divisor
                work['factor_divisions'] += 1
            work['remaining'] = str(cofactor)
            found = strip(divisor)
            if found is not None:
                return finish('gap_order_gcd', found)
        divisor = 3 if divisor == 2 else divisor+2
    work['remaining'] = '1'
    if cofactor > 1:
        found = strip(cofactor)
        if found is not None:
            return finish('gap_order_gcd', found)
    # Earlier tests at oversized exponents can succeed modulo both primes.
    # Each prime left in the exact order gets a final projection test.
    for ell in primes:
        if order % ell:
            continue
        residue = pow(base, order//ell, n)
        work['order_powers'] += 1
        work['projection_gcds'] += 1
        shared = gcd(residue-1, n)
        if 1 < shared < n:
            return finish('gap_order_gcd', shared)
    work['order'] = str(order)
    modulus = order * order
    work['class_modulus'] = str(modulus)
    candidate = lower + (n+1-lower) % modulus
    work['candidate'] = str(candidate)
    if candidate > upper or candidate + modulus <= upper:
        return finish('short_common_order')
    disc = candidate*candidate - 4*n
    work['square_tests'] += 1
    if disc >= 0:
        root = isqrt(disc)
        factor = (candidate-root)//2
        if root*root == disc and (candidate-root)%2 == 0 and 1 < factor < n and n%factor == 0:
            return finish('common_order_sum', factor)
    return finish('no_verified_split')
