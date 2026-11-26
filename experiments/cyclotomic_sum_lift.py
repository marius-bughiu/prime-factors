"""Search a balanced odd product using a fifth-order witness near its fourth root."""

from math import gcd, isqrt


def _positions(lower, upper, residue, modulus):
    first = lower + (residue-lower) % modulus
    return range(first, upper+1, modulus)


def _count(positions):
    return max(0, (positions.stop-positions.start+positions.step-1)//positions.step)


def _check_sum(n, total):
    delta = total*total-4*n
    root = isqrt(delta)
    if root*root == delta and (total-root) % 2 == 0:
        p = (total-root)//2
        if 1 < p < n and n % p == 0:
            return p
    return None


def search(n, max_tests):
    """Probe the one public base and cap subsequent discriminant tests."""
    if n < 9 or n % 2 == 0 or max_tests < 0:
        raise ValueError('expected an odd input at least 9 and a nonnegative test cap')
    base = isqrt(isqrt(n))
    lower, upper = isqrt(4*n-1)+1, isqrt(9*n//2)
    residue = pow(base, 5, n)
    work = dict(base=base, residue=residue, base_tests=1, order_gcds=0, modulus_gcds=0, lower=lower, upper=upper,
                even_positions=_count(_positions(lower, upper, 0, 2)), max_tests=max_tests,
                sum_modulus=None, sum_residue=None, eligible=None, unvisited=None,
                square_tests=0, hit_sum=None)
    if residue != 1:
        return None, dict(work, outcome='no_order_witness')
    common = gcd(base-1, n)
    work['order_gcds'] += 1
    if common != 1:
        if common < n:
            return common, dict(work, outcome='witness_gcd')
        return None, dict(work, outcome='trivial_order')

    modulus = 5*gcd(5, n-1)
    work['modulus_gcds'] += 1
    # Both factors are odd. The fifth order supplies a congruence modulo this odd modulus.
    positions = _positions(lower, upper, n+1, 2*modulus)
    work.update(sum_modulus=modulus, sum_residue=(n+1)%modulus, eligible=_count(positions),
                unvisited=_count(positions))
    for total in positions[:max_tests]:
        work['square_tests'] += 1
        work['unvisited'] -= 1
        factor = _check_sum(n, total)
        if factor is not None:
            return factor, dict(work, outcome='sum_square', hit_sum=total)
    return None, dict(work, outcome='test_cap' if work['unvisited'] else 'exhausted')


def comparisons(n, max_sites):
    """Run two bounded independent baselines after the primary search succeeds."""
    if max_sites < 0:
        raise ValueError('expected a nonnegative comparison cap')
    lower, upper = isqrt(4*n-1)+1, isqrt(9*n//2)
    evens = _positions(lower, upper, 0, 2)
    menu = {(i+n*pow(i, -1, 25)) % 25 for i in range(1, 25) if gcd(i, 25) == 1}
    ordinary = dict(menu=sorted(menu), local_gcds=24, local_inverses=20, even_sites_visited=0,
                    eligible=0, square_tests=0, factor=None, exhausted=False)
    # Count the eligible population even after the first split; charge every inspected site.
    for s in evens[:max_sites]:
        ordinary['even_sites_visited'] += 1
        if s%25 not in menu:
            continue
        ordinary['eligible'] += 1
        if ordinary['factor'] is None:
            ordinary['square_tests'] += 1
            found = _check_sum(n, s)
            if found is not None:
                ordinary['factor'] = str(found)
    ordinary['exhausted'] = ordinary['even_sites_visited'] == _count(evens)

    # gcd(base−1,n)=1 and base^5=1 already force every prime factor to be 1 modulo 5.
    divisors = _positions(isqrt((n-1)//2)+1, isqrt(n), 1, 10)
    trial = dict(eligible=_count(divisors), divisor_tests=0, factor=None)
    for d in divisors[:max_sites]:
        trial['divisor_tests'] += 1
        if n % d == 0:
            trial['factor'] = str(d)
            break
    return dict(ordinary=ordinary, trial=trial, max_sites=max_sites)
