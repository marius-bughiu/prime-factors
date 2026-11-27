"""Balanced semiprime search with one public interval and a signed weight box.

The collision backend uses packed polynomial products and a monic remainder
tree over Z/N. The measured costs are those of Python integer arithmetic.
"""
from collections import Counter
from math import gcd, isqrt, prod

from .exceptional_weights import squarefree_primes
from .powered_order import search as select_order
from .short_basis_sieve import recover_trace, shifted_giant, shortest_lattice_vector


def multiply(f, g, n):
    """Kronecker substitution with enough bits to prevent coefficient carries."""
    if not f or not g:
        return []
    length = len(f) + len(g) - 1
    bound = min(len(f), len(g)) * (n-1)**2
    width = max(1, (bound.bit_length()+7)//8)

    def pack(poly):
        return int.from_bytes(b''.join(c.to_bytes(width, 'little') for c in poly), 'little')

    raw = memoryview((pack(f)*pack(g)).to_bytes(width*length, 'little'))
    return [int.from_bytes(raw[i:i+width], 'little') % n for i in range(0, len(raw), width)]


def monic_remainder(f, g, n):
    if len(f) < len(g):
        return f
    if len(g) == 2:
        value = 0
        for coeff in reversed(f):
            value = (coeff-value*g[0]) % n
        return [value]
    length = len(f)-len(g)+1
    rev = g[::-1]
    inv = [1]
    while len(inv) < length:
        size = min(2*len(inv), length)
        error = multiply(rev[:size], inv, n)[:size]
        correction = [(-x) % n for x in error] + [0]*(size-len(error))
        correction[0] = (correction[0]+2) % n
        inv = multiply(inv, correction, n)[:size]
    quotient = multiply(f[:-length-1:-1], inv, n)[:length][::-1]
    remainder = multiply(quotient, g, n)
    return [(f[i]-remainder[i]) % n for i in range(len(g)-1)]


def product_tree(points, n):
    levels = [[[(-x) % n, 1] for x in points]]
    while len(levels[-1]) > 1:
        rows = levels[-1]
        parents = [multiply(rows[i], rows[i+1], n) for i in range(0, len(rows)-1, 2)]
        if len(rows) % 2:
            parents.append(rows[-1])
        levels.append(parents)
    return levels


def values_at(poly, points, n):
    if not points:
        return []
    return values_on_tree(poly, product_tree(points, n), n)


def values_on_tree(poly, tree, n):
    """Evaluate on a previously built nonempty monic product tree."""
    level = [monic_remainder(poly, tree[-1][0], n)]
    for children in reversed(tree[:-1]):
        level = [monic_remainder(level[j//2], g, n) for j, g in enumerate(children)]
    return [x[0] if x else 0 for x in level]


def collision(n, beta, step, exponents, giants, work):
    """Each row carries (power, a, b, trace offset, first index, last index)."""
    alpha = pow(beta, step, n)
    babies = {pow(alpha, e, n): e for e in exponents}
    if len(babies) != len(exponents):
        raise ValueError('baby span exceeds the certified order')
    work['baby_powers'] += len(babies)
    work['giant_powers'] += len(giants)
    other = []
    for power, a, b, offset, first, last in giants:
        if power not in babies:
            other.append(power)
            continue
        e = babies[power]
        if first <= e <= last:
            work['exact_trace_tests'] += 1
            factor = recover_trace(n, a, b, offset+step*e)
            if factor is not None:
                return factor, 'exact_trace'
    if not babies or not other:
        return None, None
    # Equal nonmatching giant values need only one polynomial root.
    roots = list(dict.fromkeys(other))
    work['polynomial_roots'] += len(roots)
    points = list(babies)
    poly = product_tree(roots, n)[-1][0]
    evaluated = values_at(poly, points, n)
    work['points_evaluated'] += len(points)
    for x, value in zip(points, evaluated):
        d = gcd(value, n)
        work['evaluation_gcds'] += 1
        if d == n:
            for y in roots:
                d = gcd(x-y, n)
                work['refinement_gcds'] += 1
                if 1 < d < n:
                    break
        if 1 < d < n:
            return min(d, n//d), 'polynomial_collision'
    return None, None


def search(n, m, selected, divisor_cut, base_cap, divisor_threshold, fallback_cap,
           run_exceptional=True):
    """Finite public caps can leave an input unresolved; report the work in either case."""
    if n < 9 or not 2 <= m < n or divisor_cut < 2:
        raise ValueError('need N>=9, a modulus between 2 and N-1, and cutoff >=2')
    work = Counter()
    primes = squarefree_primes(m, work)
    if len(set(selected)) != len(selected) or any(l == 2 or l not in primes for l in selected):
        raise ValueError('selected primes must be distinct odd factors of m')
    height = isqrt(m) * 2 + 2
    s = isqrt(n) + 1
    # |p| <= s, |q| <= 2s and both shortest-vector coefficients are <= height.
    radius = (3*s*height)//(m*m)+2
    period = prod(selected)
    span = 2*radius+period
    order = select_order(n, m, span, base_cap, divisor_threshold, fallback_cap)
    result = dict(m=m, selected=list(selected), divisor_cut=divisor_cut,
                  run_exceptional=run_exceptional, span=span, radius=radius,
                  height=height, order=order, work=work, factor=None, route='unresolved')
    if order['status'] != 'certified_base':
        if order['status'] == 'factor':
            result.update(factor=order['factor'], route='order_setup')
        else:
            result['unresolved_stage'] = order['method']
        return result
    beta = order['beta']
    squares = {l: {x*x % l for x in range(l)} for l in selected}
    forbidden = {l: {i for i in range(l) if i not in squares[l]
                     and (i-1) % l in squares[l] and (i-1) % l != 0} for l in selected}
    # Maximum possible number of failed selected primes when d < divisor_cut.
    h, bad_product = 0, 1
    for l in sorted(selected):
        if bad_product*l >= divisor_cut:
            break
        bad_product *= l
        h += 1
    allowed = [r for r in range(period) if sum(r % l in forbidden[l] for l in selected) <= h]
    exponents = [e for r in allowed for e in range(r, 2*radius+period, period)]
    work['period_residues_scanned'] = period
    work['local_membership_tests'] = period*len(selected)
    work['unit_gcds'] = m
    giants = []
    exceptional = []
    for sigma in range(1, m+1):
        if gcd(m, sigma) != 1:
            continue
        eta = n*pow(sigma, -2, m) % m
        a, b = shortest_lattice_vector(m, eta, lambda pair: pair, work)
        d = gcd(gcd(a, b), m)
        if d >= divisor_cut:
            step = m*m
            tau = (a*n*pow(sigma, -1, step)+b*sigma) % step
            work['trace_residue_inverses'] += 1
            exceptional.append((a, b, tau-step*radius))
            continue
        g = shifted_giant(n, m, selected, squares, radius, sigma, 0, 0, a, b, 0, work)
        offset = g.offset-m*m*g.shift
        power = pow(beta, a*n+b-offset, n)
        giants.append((power, a, b, offset, g.shift, g.shift+2*radius))
    result.update(ordinary_giants=len(giants), exceptional_giants=len(exceptional))
    factor, kind = collision(n, beta, m*m, exponents, giants, work)
    if factor is not None:
        result.update(factor=factor, route='ordinary_'+kind)
        return result
    if not run_exceptional:
        result['unresolved_stage'] = 'exceptional_search_disabled'
        return result
    if exceptional:
        width = 2*radius+1
        chunk = min(width, 1+isqrt(len(exceptional)*width-1))
        result['exceptional_chunk'] = chunk
        step = m*m
        rows = []
        for a, b, offset in exceptional:
            for first in range(0, width, chunk):
                j = offset+step*first
                last = min(chunk-1, width-first-1)
                rows.append((pow(beta, a*n+b-j, n), a, b, j, 0, last))
        factor, kind = collision(n, beta, step, list(range(chunk)), rows, work)
        if factor is not None:
            result.update(factor=factor, route='exceptional_'+kind)
            return result
    result['unresolved_stage'] = 'collision_search_exhausted'
    return result
