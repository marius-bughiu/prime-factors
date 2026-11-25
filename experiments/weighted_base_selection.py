"""Select a common base for the weighted search, retaining certified short orders."""
from math import gcd, prod

from .weighted_stride_search import search as weighted_search


def _primes(limit):
    previous = []
    candidate = 2
    while candidate <= limit:
        prime = True
        for p in previous:
            if p*p > candidate:
                break
            if candidate % p == 0:
                prime = False
                break
        if prime:
            previous.append(candidate)
            yield candidate
        candidate += 1 if candidate == 2 else 2


def _order_test(n, h, m, work):
    """Return a proper factor, an exact common order <m, or a verified adequate base."""
    power = product = 1
    differences = []
    order = None
    for i in range(1, m):
        work['order_steps'] += 1
        power = power*h % n
        if power == 1:
            order = i
            break
        differences.append(power-1)
        product = product*(power-1) % n
    divisor = gcd(product, n)
    work['order_gcds'] += 1
    if divisor == n:
        # Zero differences were excluded, so some individual gcd must be proper.
        for difference in differences:
            work['order_gcds'] += 1
            divisor = gcd(difference, n)
            if 1 < divisor < n:
                return divisor, None
        raise ArithmeticError('nonzero differences with whole-modulus product lacked a divisor')
    return (divisor if divisor > 1 else None), order


def _prime_powers(value):
    p = 2
    while p*p <= value:
        power = 1
        while value % p == 0:
            value //= p
            power *= p
        if power > 1:
            yield p, power
        p += 1 if p == 2 else 2
    if value > 1:
        yield value, value


def select(n, baby_steps, *, prime_limit=1000, max_primes=256, max_babies=262144, stride=24):
    """Test primes in increasing order, or combine short bases by prime-power projections."""
    if n < 3 or baby_steps < 1 or min(prime_limit,max_primes,max_babies) < 0 or stride not in (1,24):
        raise ValueError('expected N≥3, positive baby_steps, nonnegative caps and stride 1 or 24')
    work = dict(bases_tested=0, base_gcds=0, exponent_gcds=0, redundant_bases=0,
                order_scans=0, order_steps=0, order_gcds=0,
                short_orders=[], components=[], combined_order='1')
    result = dict(factor=None, selected_base=None, work=work)
    if baby_steps > max_babies:
        return dict(result, outcome='baby_limit')
    components = {}
    combined_order = 1
    for beta in _primes(prime_limit):
        if work['bases_tested'] >= max_primes:
            return dict(result, outcome='prime_count_limit')
        work['bases_tested'] += 1
        work['base_gcds'] += 1
        divisor = gcd(beta, n)
        if 1 < divisor < n:
            return dict(result, factor=divisor, outcome='base_divisor')
        if divisor == n:
            continue
        if baby_steps == 1:
            return dict(result, selected_base=beta, outcome='prime_base')
        h = pow(beta, stride, n)
        contained = gcd(pow(h, combined_order, n)-1, n)
        work['exponent_gcds'] += 1
        if 1 < contained < n:
            return dict(result, factor=contained, outcome='exponent_divisor')
        if contained == n:
            work['redundant_bases'] += 1
            continue
        work['order_scans'] += 1
        factor, order = _order_test(n, h, baby_steps, work)
        if factor:
            return dict(result, factor=factor, outcome='order_divisor')
        if order is None:
            return dict(result, selected_base=beta, outcome='prime_base')
        work['short_orders'].append([beta,order])
        for ell, power in _prime_powers(order):
            if ell not in components or components[ell][0] < power:
                components[ell] = (power, beta, order//power)
        combined_order = prod(power for power,_,_ in components.values())
        work['combined_order'] = str(combined_order)
        work['components'] = [[ell,*components[ell]] for ell in sorted(components)]
        if combined_order >= baby_steps:
            selected = 1
            for _, base, exponent in components.values():
                selected = selected*pow(base,exponent,n) % n
            return dict(result, selected_base=selected, outcome='combined_base')
    return dict(result, outcome='prime_limit')


def search(n, k, baby_steps, max_giants, *, prime_limit=1000, max_primes=256,
           max_babies=262144, max_slopes=131072, stride=24):
    """Apply bounded deterministic selection, then run the unchanged weighted engine."""
    if k < 1 or min(max_giants,max_slopes) < 0:
        raise ValueError('expected a positive k and nonnegative giant and slope caps')
    selection = select(n,baby_steps,prime_limit=prime_limit,max_primes=max_primes,
                       max_babies=max_babies,stride=stride)
    if selection['selected_base'] is None:
        return dict(factor=selection['factor'], outcome=selection['outcome'],
                    selection=selection, weighted=None)
    weighted = weighted_search(n,k,baby_steps,max_giants,beta=selection['selected_base'],
                               max_slopes=max_slopes,max_babies=max_babies,stride=stride)
    return dict(factor=weighted['factor'], outcome=weighted['outcome'],
                selection=selection, weighted=weighted)
