"""Coefficients of a finite q-binomial product over a composite modulus.

The shifted finite product and reflection are classical. See Bostan and
Yurkevich (https://arxiv.org/abs/2012.08656) and ReflectedGeometricBlocks.lean.
"""

from math import gcd


def reflected_polynomial(roots, ratio, modulus, n, work):
    """Return (monic coefficients, proper divisor), or (None, None) for the tree.

    roots contains 1, ratio, ..., ratio**(B-1) modulo a power of n.
    The caller can use an ordinary product tree when a whole-n denominator
    prevents division. No invertibility is assumed before the public gcd.
    """
    width = len(roots)
    half = width//2
    work.update(reflected_status='coefficients', reflected_denominators=half,
                reflected_batch_gcds=0, reflected_scan_gcds=0, reflected_inversions=0,
                reflected_products=0, reflected_mirrors=0, reflected_factor=None)
    if half == 0:
        return ([-1 % modulus, 1] if width else [1]), None

    prefix = [1]
    for i in range(1, half+1):
        prefix.append(prefix[-1]*(1-roots[i]) % modulus)
    work['reflected_products'] += half
    common = gcd(prefix[-1], n)
    work['reflected_batch_gcds'] = 1
    if common != 1:
        if common == n:
            for i in range(1, half+1):
                common = gcd(1-roots[i], n)
                work['reflected_scan_gcds'] += 1
                if 1 < common < n:
                    break
            else:
                work['reflected_status'] = 'tree_fallback'
                return None, None
        work.update(reflected_status='proper_divisor', reflected_factor=str(common))
        return None, common

    inverse = pow(prefix[-1], -1, modulus)
    work['reflected_inversions'] = 1
    for i in range(half, 0, -1):
        reciprocal = inverse*prefix[i-1] % modulus
        if i > 1:
            inverse = inverse*(1-roots[i]) % modulus
        prefix[i] = reciprocal
    work['reflected_products'] += 2*half-1

    edge = roots[-1]*ratio % modulus
    coefficients = [1]*(width+1)
    for i in range(1, half+1):
        coefficients[i] = coefficients[i-1]*(edge-roots[i-1])*prefix[i] % modulus
    work['reflected_products'] += 1+2*half

    # c[B-i] / c[i] advances by ratio**(B-1) as i decreases.
    i = half if width % 2 else half-1
    multiplier = -roots[half] if width % 2 else roots[-1]
    for j in range(i, -1, -1):
        coefficients[width-j] = coefficients[j]*multiplier % modulus
        if j:
            multiplier = multiplier*roots[-1] % modulus
    work['reflected_mirrors'] = i+1
    work['reflected_products'] += 2*i+1
    return coefficients[::-1], None
