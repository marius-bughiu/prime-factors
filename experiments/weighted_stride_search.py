"""Balanced weighted-sum collision search. All search settings are public.

The product-tree and geometric evaluation follow Harvey's Lemmas 2.3 and 2.4
(https://arxiv.org/abs/2010.05450). Windows, stride-24 conversion and full
equality readout use the project's balanced-factor lemmas.
"""
from math import gcd

from .factorial_progressions import decimal_convolution
from .short_basis_sieve import recover_trace
from .wide_modulus import multiply
from .weighted_windows import weighted_window
from .weighted_residue_tables import Wheel


def root_polynomial(roots, n):
    """Balanced tree for the monic polynomial with the supplied roots."""
    def build(lo, hi):
        if hi-lo <= 12:
            poly = [1]
            for i in range(lo, hi):
                root = roots[i]
                poly.append(1)
                for j in range(len(poly)-2, 0, -1):
                    poly[j] = (poly[j-1]-root*poly[j]) % n
                poly[0] = -root*poly[0] % n
            return poly
        mid = (lo+hi)//2
        left, right = build(lo, mid), build(mid, hi)
        conv = multiply if len(left) < 64 else decimal_convolution
        return conv(left, right, n)
    return build(0, len(roots))


def triangular_powers(h, count, n):
    """Return h^(i(i−1)/2) for 0 ≤ i < count."""
    values = []
    power = step = 1
    for _ in range(count):
        values.append(power)
        power = power*step % n
        step = step*h % n
    return values


def geometric_values(poly, h, count, n):
    """Evaluate poly(1),…,poly(h^(count-1)) using one convolution."""
    degree = len(poly)-1
    upwards = triangular_powers(h, degree+count, n)
    downwards = triangular_powers(pow(h, -1, n), max(count, degree+1), n)
    reversed_coeffs = [poly[j]*downwards[j] % n for j in range(degree, -1, -1)]
    mixed = decimal_convolution(reversed_coeffs, upwards, n)
    return [mixed[degree+i]*downwards[i] % n for i in range(count)]


def _setup_babies(n, h, m, work):
    powers = [1]
    check = 1
    for _ in range(1, m):
        powers.append(powers[-1]*h % n)
        check = check*(powers[-1]-1) % n
    common = gcd(check, n)
    work['order_gcds'] += 1
    if common == n:
        for power in powers[1:]:
            work['order_gcds'] += 1
            divisor = gcd(power-1, n)
            if 1 < divisor < n:
                return powers, divisor
    return powers, common


def _giants(n, k, m, max_giants, max_slopes, beta, stride, work, *, wheel=None):
    records = []
    jump = pow(beta, -stride*m, n)
    for b in range(1, k+1):
        for a in range(b, 2*b+1):
            if work['slope_visits'] >= max_slopes:
                return records, 'slope_limit'
            work['slope_visits'] += 1
            if gcd(a, b) != 1:
                continue
            work['primitive_slopes'] += 1
            low, high = weighted_window(n, k, a, b)
            public = a+b*n
            step = gcd(stride, 2*public)
            first = low + (public-low) % step
            if first > high:
                continue
            work['nonempty_slopes'] += 1
            length = (high-first)//step+1
            phases = (0,) if wheel is None else wheel.phases(a,b,n,step,first)
            for phase in phases:
                if wheel is not None:
                    work['phase_schedules'] += 1
                power = None
                for offset in range(0, phase+length, m):
                    begin, end = max(0,phase-offset), min(m,phase+length-offset)
                    valid = end-begin if wheel is None else wheel.prefix(end)-wheel.prefix(begin)
                    if valid:
                        if len(records) >= max_giants:
                            return records, 'giant_limit'
                        start = first+(offset-phase)*step
                        if power is None:
                            power = pow(beta, (stride//step)*(public-start), n)
                        records.append((power,a,b,start,step,begin,end))
                        work['labels_covered'] += valid
                    if power is not None:
                        power = power*jump % n
    return records, None


def records_from_allocation(n, m, max_giants, max_slopes, beta, stride, work,
                            fractions, windows, lengths, slope_visits):
    """Build the collision records for a complete allocation of label prefixes."""
    work['slope_visits'] = work['primitive_slopes'] = slope_visits
    if work['slope_visits'] > max_slopes:
        raise ValueError("the benchmark requires a complete allocation")
    work['allocated_slopes'] = len(fractions)
    work['nonempty_slopes'] = sum(bool(length) for length in lengths)
    work['labels_covered'] = sum(lengths)
    if sum((length+m-1)//m for length in lengths) > max_giants:
        raise ValueError("the benchmark requires a complete allocation")
    records = []
    jump = pow(beta, -stride*m, n)
    # Preserve the ordinary denominator-first search order among retained slopes.
    ordered = sorted(zip(fractions, windows, lengths), key=lambda row: (row[0][1], row[0][0]))
    for (a, b), (start, step), length in ordered:
        if not length:
            continue
        power = pow(beta, (stride//step)*(a+b*n-start), n)
        for offset in range(0, length, m):
            records.append((power, a, b, start+step*offset, step, 0, min(length-offset, m)))
            power = power*jump%n
    return records, None


def search(n, k, baby_steps, max_giants, *, beta=2, max_babies=262144,
           max_slopes=131072, stride=24, record_builder=_giants, wheel_primes=None,
           max_span=262144):
    """Search an explicit prefix of windows for odd balanced primes p<q≤2p.

    stride=1 runs the same windows without modular stride compression.
    With wheel_primes, baby_steps caps the retained table and max_span caps
    the full span used by the order check and dense geometric convolution.
    """
    if n < 3 or k < 1 or baby_steps < 1 or min(max_babies,max_giants,max_slopes,max_span) < 0:
        raise ValueError('expected N≥3, positive k and baby_steps, and nonnegative caps')
    if stride not in (1,24):
        raise ValueError('stride must be 1 or 24')
    if wheel_primes is not None and record_builder is not _giants:
        raise ValueError('the translated wheel uses the Farey window record builder')
    work = dict(base_gcds=0, slope_visits=0, primitive_slopes=0, nonempty_slopes=0, giants=0,
                labels_covered=0, babies=0, order_gcds=0, equality_checks=0,
                polynomial_degree=0, evaluations=0, collision_gcds=0)
    result = dict(factor=None, schedule_complete=False, limit=None, work=work)
    wheel = None if wheel_primes is None else Wheel(wheel_primes)
    span = baby_steps
    if wheel is not None:
        span = wheel.period*(baby_steps//len(wheel.allowed))
        work.update(wheel_period=wheel.period, hole_lengths=wheel.holes, baby_span=span,
                    order_positions=0, phase_schedules=0, retained_evaluations=0)
    for value in (2, 3, beta, *(wheel.primes if wheel is not None else ())):
        work['base_gcds'] += 1
        divisor = gcd(value, n)
        if divisor > 1:
            if divisor < n:
                return dict(result, factor=divisor, outcome='setup_divisor')
            return dict(result, outcome='nonunit_base_or_modulus')
    if baby_steps > max_babies:
        return dict(result, limit='baby_limit', outcome='baby_limit')
    if wheel is not None and (not span or span > max_span):
        limit = 'wheel_capacity' if not span else 'span_limit'
        return dict(result, limit=limit, outcome=limit)
    h = pow(beta, stride, n)
    powers, common = _setup_babies(n, h, span, work)
    indices = range(span)
    if wheel is not None:
        work['order_positions'] = span-1
        indices = [offset+i for offset in range(0,span,wheel.period) for i in wheel.allowed]
    work['babies'] = len(indices)
    if common != 1:
        if common < n:
            return dict(result, factor=common, outcome='order_divisor')
        return dict(result, outcome='short_order')
    if wheel is None:
        records, limit = record_builder(n, k, span, max_giants, max_slopes, beta, stride, work)
    else:
        records, limit = _giants(n, k, span, max_giants, max_slopes, beta, stride, work, wheel=wheel)
    result.update(schedule_complete=limit is None, limit=limit)
    work['giants'] = len(records)
    index = {powers[i]: i for i in indices}
    pending = []
    for power, a, b, start, step, begin, end in records:
        i = index.get(power)
        if i is None:
            pending.append(power)
        elif begin <= i < end:
            work['equality_checks'] += 1
            factor = recover_trace(n, a, b, start+step*i)
            if factor:
                return dict(result, factor=factor, outcome='trace_divisor')
    if pending:
        unique = list(dict.fromkeys(pending))
        work['polynomial_degree'] = len(unique)
        poly = root_polynomial(unique, n)
        values = geometric_values(poly, h, span, n)
        work['evaluations'] = len(values)
        if wheel is not None:
            work['retained_evaluations'] = len(indices)
        batch = 1
        for i in indices:
            batch = batch*values[i] % n
        divisor = gcd(batch, n)
        work['collision_gcds'] += 1
        if 1 < divisor < n:
            return dict(result, factor=divisor, outcome='collision_divisor')
        if divisor == n:
            for i in indices:
                divisor = gcd(values[i], n)
                work['collision_gcds'] += 1
                if 1 < divisor < n:
                    return dict(result, factor=divisor, outcome='collision_divisor')
                if divisor == n:
                    for power in unique:
                        divisor = gcd(powers[i]-power, n)
                        work['collision_gcds'] += 1
                        if 1 < divisor < n:
                            return dict(result, factor=divisor, outcome='collision_divisor')
    return dict(result, outcome=limit or 'no_split')
