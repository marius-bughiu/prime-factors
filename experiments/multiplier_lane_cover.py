"""Compare signed dyadic factor lanes for N and 3N, including Newton's factorial divisors."""

import argparse
from collections import Counter
import json
from math import isqrt
from statistics import median
from time import perf_counter

from .midpoint_weights import residue_pairs
from .newton_lanes import coprime_factorials, radix_threshold
from .norm_auxiliary import integer_roots
from .quartic_factor_lanes import equation, pairs_in_windows, signed_representatives
from .sieve_forecast import primes_through


def signed_log_three(n, exponent):
    """Lift one bit at a time to find k with 3^k = ±n modulo 2^exponent."""
    if n % 2 == 0 or exponent < 3:
        raise ValueError('the input must be odd and the dyadic exponent at least three')
    k = 0
    for bits in range(3, exponent+1):
        modulus = 1 << bits
        if pow(3, k, modulus) not in (n % modulus, -n % modulus):
            k += 1 << (bits-3)
    return k


def multiplier_lanes(n, exponent):
    k = signed_log_three(n, exponent)
    modulus = 1 << exponent
    start = (k+1)//2
    vertices = (modulus//8)+1-k%2
    count = (vertices+1)//2
    # On each edge the two original residues differ by multiplication by three.
    def representatives():
        for t in range(count):
            position = min(2*t+1, vertices-1)
            yield pow(3, start+position, modulus)
    return count, representatives()


def multiplied_pairs(n, u, radix, lower, upper, power, factorials, work):
    windows = ((lower, upper), (-upper, -lower), (3*lower, 3*upper), (-3*upper, -3*lower))
    polynomial = None
    for left, right in windows:
        first, last = -((u-left)//radix), (right-u)//radix
        if first > last:
            continue
        if polynomial is None:
            polynomial = equation(3*n, u, radix, 3*upper, work, power, factorials)
        for k in integer_roots(polynomial, first, last, work):
            work['candidate_roots'] += 1
            x = abs(u+radix*k)
            y, remainder = divmod(3*n, x)
            if remainder:
                continue
            if x % 3 == 0:
                x //= 3
            else:
                y //= 3
            x, y = sorted((x, y))
            if x > 1 and y <= 2*x and x*y == n:
                yield x, y


def run(n, power, multiplier, basis):
    if n < 5 or n % 2 == 0 or n % 3 == 0 or power < 1:
        raise ValueError('expected an odd input coprime to three and a positive factor power')
    if multiplier not in (1, 3) or basis not in ('taylor', 'newton'):
        raise ValueError('unsupported multiplier or basis')
    lower, upper = max(2, isqrt((n-1)//2)+1), isqrt(2*n)
    factorials = coprime_factorials(multiplier*n, 2*power) if basis == 'newton' else None
    threshold = radix_threshold(multiplier*upper, power, factorials or [1]*(2*power+1))
    exponent = max(3, (threshold-1).bit_length())
    radix = 1 << exponent
    work, found = Counter(), set()
    if multiplier == 1:
        _, pairs = residue_pairs(n, radix, work)
        lanes = 0
        for u, w in signed_representatives(pairs, radix, work):
            lanes += 1
            windows = ((lower, upper),) if u+w == radix else ((lower, upper), (-upper, -lower))
            found.update(pairs_in_windows(n, u, w, radix, upper, windows, work, power, factorials))
    else:
        lanes, representatives = multiplier_lanes(n, exponent)
        for u in representatives:
            found.update(multiplied_pairs(n, u, radix, lower, upper, power, factorials, work))
    return dict(radix=radix, lanes=lanes, pairs=[[str(a),str(b)] for a,b in sorted(found)], work=dict(work))


def compare(n, power, basis, repetitions=5):
    if repetitions < 1:
        raise ValueError('repetitions must be positive')
    records, elapsed = {}, {1: [], 3: []}
    for i in range(repetitions):
        for multiplier in ((1, 3) if i % 2 == 0 else (3, 1)):
            start = perf_counter()
            records[multiplier] = run(n, power, multiplier, basis)
            elapsed[multiplier].append(perf_counter()-start)
    if records[1]['pairs'] != records[3]['pairs']:
        raise ArithmeticError('the two complete searches disagree')
    for multiplier in (1, 3):
        records[multiplier]['median_seconds'] = median(elapsed[multiplier])
    return dict(n=str(n), degree=2*power, basis=basis, results=records)


def scale_exponent(power, multiplier, basis):
    """Exact worst-case dyadic threshold for X² ≤ 2^2049 and primes larger than 2m."""
    if power < 1 or multiplier not in (1, 3) or basis not in ('newton', 'taylor'):
        raise ValueError('unsupported scale parameters')
    degree, dim = 2*power, 2*power+1
    h = power*(power+1)
    powers = Counter({2: power*dim + 2049*h})
    if multiplier == 3:
        powers[3] += 2*h
    for p in primes_through(dim):
        part = dim
        while part % p == 0:
            powers[p] += dim
            part //= p
        if basis == 'newton' and multiplier % p:
            # Sum v_p(j!) over j from zero to degree. Exclude primes dividing TN.
            step = p
            while step <= degree:
                q, r = divmod(degree, step)
                powers[p] -= 2*(step*q*(q-1)//2 + q*(r+1))
                step *= p
    denominator = 2*power*dim
    # For odd p, bit_length(p^s)-1 < s*log2(p) < bit_length(p^s).
    # The rational strict inequality can therefore be certified without
    # expanding the giant product of factorials. Handle exact powers of 2 first.
    odd_terms = [(p,v) for p,v in powers.items() if p != 2 and v]
    if not odd_terms:
        return max(3, powers[2]//denominator+1)
    precision = 16
    while True:
        low = high = powers[2]*precision
        for p, v in odd_terms:
            bits = (p**precision).bit_length()
            x, y = v*(bits-1), v*bits
            low += min(x, y)
            high += max(x, y)
        low_e = low//(denominator*precision)+1
        high_e = (high-1)//(denominator*precision)+1
        if low_e == high_e:
            return max(3, low_e)
        precision *= 2


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest='command', required=True)
    scales = modes.add_parser('scales', help='certify exact dyadic exponents for the full-size envelope')
    scales.add_argument('--powers', nargs='+', type=int, default=[2, 3, 4, 8, 32, 512, 1024, 2048])
    fixtures = modes.add_parser('fixtures', help='repeat the bounded comparisons from the research note')
    fixtures.add_argument('--repetitions', type=int, default=5)
    fixtures.add_argument('--basis', choices=['taylor','newton'], default='taylor')
    single = modes.add_parser('compare', help='run both complete searches on an input')
    single.add_argument('n', type=int)
    single.add_argument('--power', type=int, default=2)
    single.add_argument('--repetitions', type=int, default=5)
    single.add_argument('--basis', choices=['taylor','newton'], default='taylor')
    args = parser.parse_args()
    if args.command == 'scales':
        rows = [dict(power=m, **{basis: [scale_exponent(m, t, basis) for t in (1, 3)]
                                for basis in ('taylor','newton')}) for m in args.powers]
    elif args.command == 'fixtures':
        rows = [compare(n, m, args.basis, args.repetitions)
                for n, m in ((1225,4),(34387,2),(43657,2),(43657,3))]
    else:
        rows = compare(args.n, args.power, args.basis, args.repetitions)
    print(json.dumps(rows, indent=2))
