"""Use supplied prime labels to verify the norm witnesses whose locations the search seeks."""
import json
from math import gcd, isqrt

from .gap_coverage import primes_through
from .mixed_ratio_heights import jacobi
from .norm_directions import discriminants
from .phase_interval import approximate_slope
from .seed_height_certificate import crossed_factors


def prime_root(value, p):
    """Tonelli–Shanks at an odd prime, for a nonzero quadratic residue."""
    if p <= 2 or not p % 2 or pow(value, (p-1)//2, p) != 1:
        raise ValueError('expected a nonzero square at an odd prime')
    odd, exponent = p-1, 0
    while odd % 2 == 0:
        odd //= 2
        exponent += 1
    root = pow(value, (odd+1)//2, p)
    residual = pow(value, odd, p)
    if residual == 1:
        return root
    nonresidue = next(v for v in range(2,p) if jacobi(v,p) == -1)
    unity = pow(nonresidue, odd, p)
    while residual != 1:
        t, i = residual, 0
        while t != 1:
            t = t*t % p
            i += 1
            if i >= exponent:
                raise ArithmeticError('invalid order in square-root calculation')
        adjust = pow(unity, 1 << (exponent-i-1), p)
        root = root*adjust % p
        unity = adjust*adjust % p
        residual = residual*unity % p
        exponent = i
    if (root*root-value) % p:
        raise ArithmeticError('incorrect prime square root')
    return root


def check_labels(p, q, last_prime):
    """Factor labels construct witnesses for validation; the public search does not read them."""
    n = p*q
    forms, divisor = discriminants(n, primes_through(last_prime))
    if divisor:
        return dict(trial_divisor=str(divisor))
    d = next((d for d in forms if jacobi(-d,p) == jacobi(-d,q) == 1), None)
    if d is None:
        return dict(forms=len(forms),d=None)
    u, v = prime_root(-d,p), prime_root(-d,q)
    s = 1+isqrt(d-1)
    limit = isqrt(n//s)
    witnesses = []
    roots = []
    for other in (v,-v):
        z = u+p*((other-u)*pow(p,-1,q) % q)
        a,t,steps = approximate_slope(z,n,limit)
        k,rem = divmod(t*t+d*a*a,n)
        if rem or not 0 < k < 2*s or abs(t)*(limit+1)>n or gcd(a,n) != 1:
            raise ArithmeticError('failed small multiple certificate')
        witnesses.append([k,str(abs(t)),str(a),steps])
        roots.append(abs(t)*pow(a,-1,n)%n)
    split = gcd(roots[0]-roots[1],n)
    if split not in (p,q):
        raise ArithmeticError('representations failed to split')
    return dict(forms=len(forms),d=d,witnesses=witnesses,divisor=str(split))


if __name__ == '__main__':
    print(json.dumps(check_labels(*crossed_factors(),739),indent=2))
