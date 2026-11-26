"""Find the smallest separating period extending a wheel and evaluate its selected product."""
from math import gcd

from .character_divisor_column import MAX_PERIOD, _before, _evaluate
from .short_pascal_row import interval


def basic_moduli(period):
    """Odd prime divisors and the largest relevant dyadic test, if any."""
    if period % 8 == 0:
        yield 8
    elif period % 4 == 0:
        yield 4
    while period % 2 == 0:
        period //= 2
    divisor = 3
    while divisor * divisor <= period:
        if period % divisor == 0:
            yield divisor
            while period % divisor == 0:
                period //= divisor
        divisor += 2
    if period > 1:
        yield period


def least_period(n, wheel, limit, reflect, work):
    """Return a period with no roots of n (and, for reflection, of -n).

    Search in order among multiples of wheel. A nonunit gcd can expose a
    divisor first. Cache each square test across all periods in the search.
    """
    signs = (1, -1) if reflect else (1,)
    cache = {}
    for period in range(wheel, limit+1, wheel):
        work['period_gcds'] += 1
        common = gcd(n, period)
        if 1 < common < n:
            return None, common
        if common > 1:
            continue
        tests = tuple(basic_moduli(period))
        def nonsquare(sign, modulus):
            key = sign, modulus
            if key not in cache:
                work['square_tests'] += 1
                value = (sign*n) % modulus
                if modulus in (4, 8):
                    cache[key] = value != 1
                else:
                    cache[key] = pow(value, (modulus-1)//2, modulus) != 1
            return cache[key]
        if all(any(nonsquare(s, d) for d in tests) for s in signs):
            return period, None
    return None, None


def select_mask(n, *, wheel=30, period_limit=MAX_PERIOD, reflect=False, max_work=2_000_000):
    """Return the public selection, inclusive endpoints and its sorted offsets, if available."""
    if not 2 <= wheel <= period_limit <= MAX_PERIOD or max_work < 0:
        raise ValueError('expected a bounded wheel, period limit and nonnegative budget')
    low, _ = interval(n)
    base = 1 << ((n.bit_length()-1)//2)
    high = min(2*base-1, n//base)
    prep = dict(period_gcds=0, square_tests=0, residue_gcds=0, inverses=0)
    period, factor = least_period(n, wheel, period_limit, reflect, prep)
    report = dict(mode='reflected' if reflect else 'unrestricted', selection=prep,
                  period=period, visited='0', factor=factor, work={}, max_work=max_work)
    if period is None:
        return dict(report, outcome='period_divisor' if factor else 'period_limit'), low, high, None

    groups = [[], []]
    for x in range(1, period):
        prep['residue_gcds'] += 1
        if gcd(x, period) != 1:
            continue
        y = n*pow(x, -1, period) % period
        prep['inverses'] += 1
        left, right = (min(x, period-x), min(y, period-y)) if reflect else (x, y)
        if left == right:
            raise ArithmeticError('the selected period has a fixed pair')
        groups[left < right].append(x)
    if len(groups[0]) != len(groups[1]):
        raise ArithmeticError('inconsistent partner orbits')
    counts = [_before(high+1, period, g)-_before(low, period, g) for g in groups]
    which = min(range(2), key=lambda i: (counts[i], -i))
    report.update(canonical=bool(which), residues_per_period=len(groups[which]))
    return report, low, high, groups[which]


def search(n, *, wheel=30, period_limit=MAX_PERIOD, reflect=False, max_work=2_000_000):
    """Under the equal-width semiprime promise, try the smaller of the two masks."""
    report, low, high, offsets = select_mask(n, wheel=wheel, period_limit=period_limit,
                                             reflect=reflect, max_work=max_work)
    if offsets is None:
        return report
    return _evaluate(n, low, high, report['period'], offsets, max_work, report)
