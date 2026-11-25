"""Count primitive top-offset tests and two modular exclusions by whole intervals."""

import argparse
from array import array
from bisect import bisect_left, bisect_right
import json
from math import gcd, isqrt
from pathlib import Path
from time import perf_counter

from experiments.phase_interval import approximate_slope
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]


def ceil_div(value, positive):
    return -((-value)//positive)


def discriminant(T, h, j, k):
    return j*j + 4*k*(T*j-h*k)


def frame(T, h, limit):
    B, error, _ = approximate_slope(T, h, isqrt(limit))
    A = (B*T-error)//h
    C = -pow(A, -1, B) % B if B > 1 else 0
    if 2*C > B:
        C -= B
    D = (1+A*C)//B
    assert B*D-A*C == 1
    return A, B, C, D, error


def rejecting_primes(coefficient, primes):
    return [p for p in primes if p > 2 and pow(coefficient % p, (p-1)//2, p) == p-1]


def local_failures(coefficient, primes, bound):
    """Minimal prime powers which obstruct a square modulo the coordinate."""
    if not coefficient:
        return [], []
    single, higher = [], []
    for p in primes:
        if p > bound:
            break
        unit = coefficient
        power = 1
        odd_valuation = False
        while unit % p == 0:
            unit //= p
            power *= p
            odd_valuation = not odd_valuation
        if odd_valuation:
            obstruction = power*p
        elif p == 2:
            obstruction = power*(4 if unit%4 != 1 else 8) if unit%8 != 1 else 0
        else:
            obstruction = power*p if pow(unit%p, (p-1)//2, p) != 1 else 0
        if obstruction and obstruction <= bound:
            (single if obstruction == p else higher).append(obstruction)
    return single, higher


def integer_square(n):
    return n >= 0 and isqrt(n)**2 == n


def inclusion_products(powers, bound):
    terms = [1]
    for power in powers:
        terms.extend([-term*power for term in terms if abs(term)*power <= bound])
    return terms


def admissible_magnitudes(bound, rejecting):
    """Allowed absolute coordinate values. Every prime divides zero."""
    good = bytearray([1])*(bound+1)
    if rejecting:
        good[0] = 0
    for p in rejecting:
        if p <= bound:
            good[p::p] = bytes(bound//p)
    return good


def signed_prefix(prefix, zero, x):
    """F(x)-F(x-1) is the indicator of the signed value x."""
    return prefix[x]+zero if x >= 0 else -prefix[-x-1]


def smallest_primes(n):
    factors = array('I', [0])*(n+1)
    for p in range(2, isqrt(n)+1):
        if factors[p] == 0:
            for k in range(p*p, n+1, p):
                if not factors[k]:
                    factors[k] = p
    return factors


def mobius_divisors(n, factors):
    terms = [1]
    while n > 1:
        p = factors[n] or n
        terms.extend([-p*d for d in terms])
        while n % p == 0:
            n //= p
    return terms


def signed_values(magnitudes, low, high, zero_ok):
    if low < 0:
        start = bisect_left(magnitudes, max(1, -high))
        stop = bisect_right(magnitudes, -low)
        for idx in range(stop-1, start-1, -1):
            yield -magnitudes[idx]
    if low <= 0 <= high and zero_ok:
        yield 0
    if high > 0:
        start = bisect_left(magnitudes, max(1, low))
        stop = bisect_right(magnitudes, high)
        for idx in range(start, stop):
            yield magnitudes[idx]


def scan_interval(T, h, basis, t, candidates, limit, report):
    """Try surviving coordinates, stopping at the stated budget or a proper divisor."""
    A, B, C, D = basis
    n = T*T+h
    for r in candidates:
        if gcd(r, t) != 1:
            continue
        j, k = B*r+C*t, A*r+D*t
        f = discriminant(T, h, j, k)
        d = isqrt(f)
        report['square_tests'] += 1
        if d*d == f:
            m = (d-j)//2
            for summand in (k*T-m, k*T+m+j):
                factor = gcd(n, summand)
                if 1 < factor < n:
                    report.update(factor=str(factor), offset=j, multiplier=str(k))
                    return
        if report['square_tests'] >= limit:
            return


def bounded_rows(T, h, limit, prime_limit, *, max_prefix=8_000_000, basis=None, max_square_tests=0):
    """Exact counts for 1 <= j <= limit and k=(T*j-1)//h > 0.

    Set max_prefix=None to disable the memory guard. If the second coordinate
    is too wide, the first-axis count is still returned in full.
    """
    if min(T, h, limit) <= 0 or max_square_tests < 0 or (prime_limit is not None and prime_limit < 0):
        raise ValueError('positive root, offset and search limit required')
    first_j = h//T+1
    raw = max(0, limit-first_j+1)
    report = dict(square_tests=0, factor=None)
    if not raw:
        return dict(raw=0, primitive=0, first_axis=0, both_axes=0, rows=0, search=report)
    if basis is None:
        A, B, C, D, e = frame(T, h, limit)
    else:
        A, B, C, D = basis
        if B <= 0 or B*D-A*C != 1:
            raise ValueError('basis must have positive first denominator and determinant one')
        e = B*T-h*A
    ep = T*C-h*D
    tmin = ceil_div(min(e*first_j, e*limit)-B*h, h)
    tmax = (max(e*first_j, e*limit)-B)//h
    extent = max(abs(tmin), abs(tmax))
    # j=B*r+C*t bounds |r| on all nonempty rows.
    rmax = (limit+abs(C)*extent)//B
    can_count_both = max_prefix is None or rmax <= max_prefix
    full = prime_limit is None
    primes = primes_through(max(extent, rmax if can_count_both else 0) if full else prime_limit)
    ft, fr = discriminant(T, h, B, A), discriminant(T, h, C, D)
    if full:
        bad_t, powers_t = local_failures(ft, primes, extent)
        bad_r, powers_r = local_failures(fr, primes, rmax) if can_count_both else ([], [])
    else:
        bad_t, powers_t = rejecting_primes(ft, primes), []
        bad_r, powers_r = rejecting_primes(fr, primes), []
    tg = admissible_magnitudes(extent, bad_t+powers_t)
    if full:
        tg[0] = integer_square(ft)
    if can_count_both:
        # The ordinary-prime filter commutes with scaling by any good d.
        # The remaining exceptional prime powers are handled by inclusion-exclusion.
        rg = admissible_magnitudes(max(rmax, extent), bad_r)
        zero_ok = integer_square(fr) if full else not bad_r
        higher_terms = inclusion_products(powers_r, rmax)
        prefix = array('I' if rmax < 2**32 else 'Q', [0])
        total = 0
        for i in range(1, rmax+1):
            total += rg[i]
            prefix.append(total)
        if max_square_tests:
            allowed_r = admissible_magnitudes(rmax, bad_r+powers_r)
            magnitudes = array('I' if rmax < 2**32 else 'Q',
                               (i for i in range(1, rmax+1) if allowed_r[i]))
    factors = smallest_primes(extent)
    primitive = first_axis = both_axes = nonempty = skipped_rows = sites = 0
    for t in range(tmin, tmax+1):
        low = ceil_div(first_j-C*t, B)
        high = (limit-C*t)//B
        if e > 0:
            low = max(low, ceil_div(1-ep*t, e))
            high = min(high, (h-ep*t)//e)
        elif e < 0:
            low = max(low, ceil_div(ep*t-h, -e))
            high = min(high, (ep*t-1)//(-e))
        elif not 1 <= ep*t <= h:
            continue
        if low > high:
            continue
        nonempty += 1
        sites += high-low+1
        t_ok = tg[abs(t)]
        if not t_ok:
            skipped_rows += 1
        if t_ok and report['square_tests'] < max_square_tests and report['factor'] is None:
            candidates = (signed_values(magnitudes, low, high, zero_ok) if can_count_both
                          else range(low, high+1))
            scan_interval(T, h, (A, B, C, D), t, candidates, max_square_tests, report)
        if t == 0:
            units = int(low <= -1 <= high) + int(low <= 1 <= high)
            primitive += units
            if t_ok:
                first_axis += units
                if can_count_both:
                    both_axes += units  # |r|=1
            continue
        units = screened = 0
        for signed in mobius_divisors(abs(t), factors):
            d = abs(signed)
            sign = 1 if signed > 0 else -1
            left, right = (low-1)//d, high//d
            units += sign*(right-left)
            if can_count_both and t_ok and rg[d]:
                screened += sign*(signed_prefix(prefix, 0, right) - signed_prefix(prefix, 0, left))
                for term in higher_terms[1:]:
                    multiple = d*(abs(term)//gcd(d, abs(term)))
                    screened += (sign if term>0 else -sign)*(
                        signed_prefix(prefix, 0, high//multiple) -
                        signed_prefix(prefix, 0, (low-1)//multiple))
        if can_count_both and t_ok and abs(t)==1 and low<=0<=high:
            screened += int(zero_ok)
        primitive += units
        if t_ok:
            first_axis += units
            both_axes += screened
    assert sites == raw
    return dict(raw=raw, primitive=primitive, first_axis=first_axis,
                both_axes=both_axes if can_count_both else None,
                rows=nonempty, rows_rejected=skipped_rows, t_range=[tmin,tmax],
                max_abs_r=rmax, A=str(A), B=B, C=C, D=str(D), prime_limit=prime_limit,
                rejecting_t=len(bad_t), rejecting_r=len(bad_r),
                rejecting_powers_t=powers_t, rejecting_powers_r=powers_r, search=report)


def direct(T, h, limit, prime_limit, *, basis=None):
    """Independent reference: visit individual offsets for small checks."""
    A, B, C, D = basis if basis is not None else frame(T, h, limit)[:4]
    ft, fr = discriminant(T, h, B, A), discriminant(T, h, C, D)
    if prime_limit is not None:
        primes = primes_through(prime_limit)
        bad_t = rejecting_primes(ft, primes)
        bad_r = rejecting_primes(fr, primes)

    def square_mod(n, modulus):
        if not modulus:
            return integer_square(n)
        return any((x*x-n)%abs(modulus) == 0 for x in range(abs(modulus)))
    raw = primitive = first = both = hits = 0
    for j in range(1, limit+1):
        k = (T*j-1)//h
        if k == 0:
            continue
        raw += 1
        if gcd(j, k) != 1:
            continue
        primitive += 1
        t, r = B*k-A*j, D*j-C*k
        t_ok = square_mod(ft,t) if prime_limit is None else all(t%p for p in bad_t)
        r_ok = square_mod(fr,r) if prime_limit is None else all(r%p for p in bad_r)
        first += int(t_ok)
        both += int(t_ok and r_ok)
        f = discriminant(T, h, j, k)
        if isqrt(f)**2 == f:
            assert t_ok and r_ok
            hits += 1
    return [raw, primitive, first, both], hits


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=1<<40)
    parser.add_argument('--prime-limit', type=int, help='test only odd primes through this limit')
    parser.add_argument('--max-square-tests', type=int, default=0)
    args = parser.parse_args()
    cases = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
    for case in cases:
        if case['id'] not in ('grouped-norm-fresh-2048','grouped-norm-crossed-2048'):
            continue
        n = int(case['n'])
        T = isqrt(n)
        start = perf_counter()
        result = bounded_rows(T, n-T*T, args.limit, args.prime_limit, max_square_tests=args.max_square_tests)
        print(json.dumps(dict(id=case['id'], limit=args.limit,
                              seconds=perf_counter()-start, **result)), flush=True)


if __name__ == '__main__':
    main()
