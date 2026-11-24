"""Bounded continued-fraction search on pairs of public auxiliary primes."""

from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt

if __package__:
    from .midpoint_readings import reading
    from .sieve_forecast import primes_through
else:
    from midpoint_readings import reading
    from sieve_forecast import primes_through


def center(n, multiplier, budget):
    """Find a symmetry, retaining consecutive convergent numerators only modulo n."""
    d = n * multiplier
    base = isqrt(d)
    if base * base == d:
        raise ValueError('a square radicand has no continued-fraction period')
    offset, denominator, quotient = 0, 1, base
    older, previous = 0, 1
    for step in range(1, budget + 1):
        numerator = (quotient * previous + older) % n
        offset = quotient * denominator - offset
        denominator = (d - offset * offset) // denominator
        quotient = (base + offset) // denominator
        if denominator == 1:
            return step, None
        if quotient * denominator == 2 * offset:
            sign = -1 if step % 2 else 1
            if (numerator * numerator - sign * denominator) % n:
                raise ArithmeticError('center norm disagrees with the numerator')
            return step, (denominator, sign, numerator)
        older, previous = previous, numerator
    return budget, None


def search(n, max_prime, max_steps, triangles=True):
    """Try the smallest eligible prime against later ones, optionally closing triangles.

    max_steps is a total budget across all walks. Trial division in the prime
    list generator uses only the public max_prime, independently of n.
    """
    if n <= 1 or n % 4 != 1 or isqrt(n)**2 == n:
        raise ValueError('expected an odd nonsquare product congruent to one modulo four')
    if max_prime < 0 or max_steps < 0:
        raise ValueError('budgets must be nonnegative')
    work = dict(factor=None, outcome='exhausted', steps=0, walks=0, centers=0,
                prime_gcds=0, cycles=0, root=None, edges=[])
    vertices = []
    for prime in primes_through(max_prime):
        if prime % 4 != 3:
            continue
        work['prime_gcds'] += 1
        divisor = gcd(prime, n)
        if 1 < divisor < n:
            return dict(work, factor=divisor, outcome='prime_gcd')
        if divisor == 1 and reading(prime, n) == -1:
            vertices.append(prime)
    if len(vertices) < 2:
        return work
    anchor, *others = vertices
    spoke = {}
    for index, vertex in enumerate(others):
        partners = [anchor]
        if triangles and index and others[index - 1] in spoke:
            partners.append(others[index - 1])
        for partner in partners:
            multiplier = partner * vertex
            if 4 * multiplier > n:
                continue
            remaining = max_steps - work['steps']
            if remaining <= 0:
                return dict(work, outcome='budget')
            steps, observation = center(n, multiplier, remaining)
            work['steps'] += steps
            work['walks'] += 1
            if observation is None:
                if steps == remaining:
                    return dict(work, outcome='budget')
                continue
            denominator, sign, residue = observation
            work['centers'] += 1
            work['edges'].append([partner, vertex, steps, denominator, residue])
            divisor = gcd(n, denominator)
            if 1 < divisor < n:
                return dict(work, factor=divisor, outcome='center')
            if denominator != multiplier or sign != 1:
                raise ArithmeticError('unexpected center for a negative-Jacobi prime pair')
            if partner == anchor:
                spoke[vertex] = residue
            elif vertex in spoke:
                scale = anchor * partner * vertex
                root = (spoke[partner] * spoke[vertex] * residue * pow(scale, -1, n)) % n
                if root * root % n != 1:
                    raise ArithmeticError('the three center norms do not form a square')
                work['root'] = root
                work['cycles'] += 1
                divisor = gcd(root - 1, n)
                if 1 < divisor < n:
                    return dict(work, factor=divisor, outcome='cycle')
    return work


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-prime', type=int, default=43)
    parser.add_argument('--max-steps', type=int, default=10000)
    parser.add_argument('--star-only', action='store_true')
    options = parser.parse_args()
    print(dumps(search(options.n, options.max_prime, options.max_steps, not options.star_only)))
