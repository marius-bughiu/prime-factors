"""Search for two different modular roots using positive definite norm equations."""
import argparse
from fractions import Fraction
import json
from math import gcd, isqrt, prod

from .gap_coverage import primes_through
from .mixed_ratio_heights import jacobi
from .phase_interval import approximate_slope, cube_radius


def discriminants(n, primes):
    """A public Jacobi pivot reduces all products of two generators to at most k+1 tests."""
    signs = [jacobi(p, n) for p in primes]
    for p, sign in zip(primes, signs):
        if not sign:
            divisor = gcd(p, n)
            if divisor < n:
                return [], divisor
    entries = [(p, s) for p, s in zip(primes, signs) if s]
    pivot = next((p for p, s in entries if s == -1), None)
    target = jacobi(-1, n)
    if pivot is None:
        return ([1] + [p for p, _ in entries] if target == 1 else []), None
    initial = 1 if target == 1 else pivot
    forms = [initial]
    for p, sign in entries:
        if p != pivot:
            forms.append(p if sign == target else pivot*p)
    return forms, None


def input_failure_bound(primes):
    """Finite upper bound for distinct 1024-bit primes conditioned on 2048-bit product."""
    if (not primes or primes[0] != 2 or len(set(primes)) != len(primes)
            or any(p < 2 or p >= 2**1023 or any(p % f == 0 for f in range(2, isqrt(p)+1))
                   for p in primes)):
        raise ValueError('supply distinct small primes beginning with two')
    x = 2**1023
    modulus = 4*prod(primes)
    phi = 4*prod(p-1 for p in primes[1:])
    cells = phi // 2**(len(primes)+1)
    partners = cells*((x+modulus-1)//modulus)
    return 3 * Fraction(1511, 1000) * 710 * partners / (Fraction(22,100)**2 * x)


def arc(n, a, b, lo, hi, work):
    """Find all positive solutions to a*x²+b*y²=n with lo≤x≤hi and a*x²≤n/2."""
    span = hi-lo
    width = span+1
    scale = 4*(a+b+1)*width**2
    left = isqrt((n-a*lo*lo)*scale**2//b)
    right = isqrt((n-a*hi*hi)*scale**2//b)
    low_slope = Fraction(a*lo*scale, b*(left+1))
    high_slope = Fraction(a*(2*lo+span)*scale, b*(left+right))
    den, remainder, steps = approximate_slope(low_slope.numerator, low_slope.denominator, width)
    num = (den*low_slope.numerator-remainder)//low_slope.denominator
    work['euclidean_steps'] += steps
    # For j=x-lo the integer intercept den*y+num*j lies between these bounds.
    low = Fraction(den*left, scale) + min(0, (num-den*high_slope)*span)
    high = Fraction(den*(left+1), scale) + max(0, (num-den*low_slope)*span)
    quadratic = a*den**2+b*num**2
    for intercept in range(-((-low.numerator)//low.denominator), high.numerator//high.denominator + 1):
        work['line_tests'] += 1
        linear = a*den**2*lo-b*num*intercept
        constant = a*den**2*lo**2+b*intercept**2-n*den**2
        delta = linear**2-quadratic*constant
        if delta < 0:
            continue
        work['discriminant_roots'] += 1
        r = isqrt(delta)
        if r*r != delta:
            continue
        for offset in ((r, -r) if r else (0,)):
            j, extra = divmod(offset-linear, quadratic)
            if extra or not 0 <= j <= span:
                continue
            y, extra = divmod(intercept-num*j, den)
            if not extra and y > 0:
                x = lo+j
                if a*x*x+b*y*y != n:
                    raise ArithmeticError('line root is off the ellipse')
                yield x, y


def scan(n, d, k, work, max_blocks):
    """Cover the two arcs on which one weighted coordinate contributes at most half."""
    total = k*n
    if total < 1+d:
        return
    for a,b,swapped in ((1,d,False), (d,1,True)):
        last = isqrt(total//(2*a))
        # cube_radius(c) is the largest w with 64*w³≤c.
        width = max(1, cube_radius(8*isqrt(b*total)//a))
        for lo in range(1, last+1, width):
            if work['blocks'] == max_blocks:
                work['outcome'] = 'block_limit'
                return
            hi = min(last, lo+width-1)
            work['blocks'] += 1
            work['coordinate_positions'] += hi-lo+1
            for x,y in arc(total,a,b,lo,hi,work):
                if swapped and a*x*x == b*y*y:
                    continue
                yield (y,x) if swapped else (x,y)


def admissible_multipliers(n, d):
    """A shortest vector has 3*k²≤4*d. Screen its equation at 8 and the odd primes of d."""
    odd = d
    while odd % 2 == 0:
        odd //= 2
    prime_factors = []
    candidate = 3
    while candidate*candidate <= odd:
        if odd % candidate == 0:
            prime_factors.append(candidate)
            while odd % candidate == 0:
                odd //= candidate
        candidate += 2
    if odd > 1:
        prime_factors.append(odd)
    squares = (0, 1, 4)
    possible = {(t+d*a) % 8 for t in squares for a in squares}
    for k in range(1, isqrt(4*d//3)+1):
        value = k*n
        if value % 8 in possible and all(jacobi(value, p) >= 0 for p in prime_factors):
            yield k


def search(n, last_prime, max_blocks):
    if n <= 2 or n % 2 == 0 or last_prime < 2 or max_blocks < 0:
        raise ValueError('expected an odd input >2, prime bound ≥2 and nonnegative block budget')
    choices, factor = discriminants(n, primes_through(last_prime))
    work = dict(factor=factor, outcome='prime_gcd' if factor else 'no_split', forms=0,
                multiples=0, excluded_multiples=0, blocks=0, coordinate_positions=0, line_tests=0,
                discriminant_roots=0, euclidean_steps=0, representations=0, witnesses=[])
    if factor:
        return work
    for d in choices:
        work['forms'] += 1
        first = None
        eligible = list(admissible_multipliers(n, d))
        work['excluded_multiples'] += isqrt(4*d//3)-len(eligible)
        for k in eligible:
            work['multiples'] += 1
            for t,v in scan(n, d, k, work, max_blocks):
                work['representations'] += 1
                divisor = gcd(v,n)
                if 1 < divisor < n:
                    return dict(work, outcome='coordinate_gcd', factor=divisor)
                if divisor != 1:
                    continue
                root = t*pow(v,-1,n) % n
                witness = [d,k,str(t),str(v)]
                if first is None:
                    first = root, witness
                    continue
                if root in (first[0], -first[0] % n):
                    continue
                divisor = gcd(root-first[0], n)
                if not 1 < divisor < n:
                    raise ArithmeticError('different square-root classes did not split the modulus')
                return dict(work, outcome='norm_pair', factor=divisor, witnesses=[first[1],witness])
            if work['outcome'] == 'block_limit':
                return work
    return work


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--last-prime', type=int, default=13)
    parser.add_argument('--max-blocks', type=int, default=10000)
    args = parser.parse_args()
    print(json.dumps(search(args.n,args.last_prime,args.max_blocks)))
