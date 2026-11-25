"""Certify integer points on ellipse sectors with exact lattice reduction.

For z in [0,1], set x = sqrt(T)*(1-z²)/(1+z²) and
y = sqrt(T/d)*2z/(1+z²). Each of 1,x,x²,y,xy then has a quartic numerator
over (1+z²)². Reduce the five numerator rows in local sector coordinates,
enclose the error of the dyadic square roots, and solve every resulting
integer level. The enclosure is checked even for a caller's coarser sectors.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from math import comb, factorial, gcd, isqrt

from .norm_directions import scan as line_scan


def reduced_basis(rows, work=None, *, initial_coefficients=None, dual_coordinates=None):
    """Exact LLL with delta=3/4; return reduced rows and their input coefficients.

    If supplied, update the mutable dual_coordinates in place so their linear
    combination of the basis rows continues to represent the same vector.
    """
    if work is None:
        work = Counter()
    work['lll_calls'] += 1
    basis = [list(row) for row in rows]
    n = len(basis)
    if not n or any(len(v) != len(basis[0]) for v in basis):
        raise ValueError('expected a nonempty rectangular row matrix')
    if dual_coordinates is not None and len(dual_coordinates) != n:
        raise ValueError('expected one dual coordinate per row')
    transform = ([list(row) for row in initial_coefficients] if initial_coefficients is not None
                 else [[int(i == j) for j in range(n)] for i in range(n)])
    # D[j] is the Gram determinant of the first j rows. Lambda[i,j]/D[j+1]
    # is the Gram-Schmidt projection coefficient for row i onto row j.
    det = [1]
    lam = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1):
            v = sum(x*y for x, y in zip(basis[i], basis[j]))
            for h in range(j):
                v = (det[h+1]*v-lam[i][h]*lam[j][h])//det[h]
            if i == j:
                if v <= 0:
                    raise ValueError('lattice rows must be linearly independent')
                det.append(v)
            else:
                lam[i][j] = v

    k = 1
    while k < n:
        for j in range(k-1, -1, -1):
            q = (2*lam[k][j]+det[j+1])//(2*det[j+1])
            if q:
                work['lll_reductions'] += 1
                if dual_coordinates is not None:
                    dual_coordinates[j] += q*dual_coordinates[k]
                for array in (basis, transform):
                    array[k] = [v-q*w for v, w in zip(array[k], array[j])]
                for h in range(j):
                    lam[k][h] -= q*lam[j][h]
                lam[k][j] -= q*det[j+1]
        mu = lam[k][k-1]
        numerator = det[k-1]*det[k+1]+mu*mu
        if 4*numerator >= 3*det[k]*det[k]:
            k += 1
            continue
        work['lll_swaps'] += 1
        if dual_coordinates is not None:
            dual_coordinates[k-1], dual_coordinates[k] = dual_coordinates[k], dual_coordinates[k-1]
        for array in (basis, transform):
            array[k-1], array[k] = array[k], array[k-1]
        for j in range(k-1):
            lam[k-1][j], lam[k][j] = lam[k][j], lam[k-1][j]
        for i in range(k+1, n):
            a, b = lam[i][k-1], lam[i][k]
            lam[i][k-1] = (det[k-1]*b+mu*a)//det[k]
            lam[i][k] = (det[k+1]*a-mu*b)//det[k]
        det[k] = numerator//det[k]
        k = max(1, k-1)
    return basis, transform


def short_vector(rows, work=None):
    """Return the first exact LLL-reduced lattice row."""
    return reduced_basis(rows, work)[0][0]


def multiply(p, q):
    out = [0]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def integer_roots(coefficients, lo, hi, work=None):
    """Isolate every integer root on the inclusive interval using Bernstein signs."""
    if work is None:
        work = Counter()
    p = list(coefficients)
    while p and p[-1] == 0:
        p.pop()
    if not p:
        raise ValueError('the zero polynomial has no isolated roots')
    if lo > hi or len(p) == 1:
        return []
    degree = len(p)-1
    denominator = factorial(degree)
    weights = [[comb(m, j)*(denominator//comb(degree, j)) for j in range(m+1)]
               for m in range(degree+1)]
    roots = []
    pending = [(lo, hi)]
    while pending:
        left, right = pending.pop()
        work['integer_root_nodes'] += 1
        # Shift and dilate, then convert coefficients to Bernstein form.
        span = right-left
        scaled = [span**j*sum(p[h]*comb(h, j)*left**(h-j) for h in range(j, degree+1))
                  for j in range(degree+1)]
        values = [sum(v*w for v, w in zip(scaled, row)) for row in weights]
        if min(values) >= 0 or max(values) <= 0:
            if values[0] == 0:
                roots.append(left)
            if right != left and values[-1] == 0:
                roots.append(right)
        else:
            middle = (left+right)//2
            pending.extend(((middle+1, right), (left, middle)))
    return roots


def ellipse_intersection(total, d, coefficients, lo, hi, work=None):
    """Integer intersections for basis [1,x,x²,y,xy] and x²+d*y²=total, x,y>0."""
    if work is None:
        work = Counter()
    c, x, xx, y, xy = coefficients
    polynomial = [d*v for v in multiply([c, x, xx], [c, x, xx])]
    other = multiply([total, 0, -1], multiply([y, xy], [y, xy]))
    resultant = [a-b for a, b in zip(polynomial, other)]
    work['resultants'] += 1
    points = []
    for t in integer_roots(resultant, max(1, lo), min(hi, isqrt(total-1)), work):
        square, remainder = divmod(total-t*t, d)
        work['point_checks'] += 1
        v = isqrt(square)
        if not remainder and v*v == square and c+x*t+xx*t*t+(y+xy*t)*v == 0:
            points.append((t, v))
    return points


def sector_count(total, d):
    """Least J with d*J^10 >= 8^10*T^3."""
    target = 8**10*total**3
    lo, hi = 0, 1 << ((target.bit_length()+9)//10)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if d*mid**10 >= target:
            hi = mid
        else:
            lo = mid
    return hi


def amplitudes(total, d, sectors):
    # Exact floor at a common binary scale. A dyadic element that is already
    # exact contributes no rounding error to a certified interval.
    scale = 1 << (2+4*(2*sectors-1).bit_length())
    squares = ((1, 1), (total, 1), (total**2, 1), (total, d), (total**2, d))
    roots = [isqrt(n*scale**2//b) for n, b in squares]
    errors = [int(root*root*b != n*scale**2)
              for root, (n, b) in zip(roots, squares)]
    return scale, roots, errors


def sector_points(total, d, sectors, i, amplitude, work, *, previous=None):
    """Use the rational angle parameter z=(i+u)/J for 0 <= u <= 1."""
    scale, roots, errors = amplitude
    j2 = sectors*sectors
    denominator = [j2+i*i, 2*i, 1]
    cosine = [j2-i*i, -2*i, -1]
    sine = [2*sectors*i, 2*sectors, 0]
    def floor_x(boundary):
        b2 = boundary*boundary
        return isqrt(total*(j2-b2)**2//(j2+b2)**2)
    # x decreases with z. Assign the shared boundary to the following sector.
    lo, hi = floor_x(i+1)+1, floor_x(i)
    work['coordinate_positions'] += max(0, hi-lo+1)
    if lo > hi:
        work['empty_coordinate_intervals'] += 1
        return []
    if previous:
        # The next local parameter is the old one minus the sector displacement.
        # Translating each reduced quartic keeps its integral auxiliary coefficients.
        step = i-previous['sector']
        powers = [step**h for h in range(5)]
        rows = [[sum(row[h]*comb(h, j)*powers[h-j] for h in range(j, 5))
                 for j in range(5)] for row in previous['rows']]
        vectors, transform = reduced_basis(rows, work, initial_coefficients=previous['transform'])
        work['reused_bases'] += 1
    else:
        # Parameterized monomials after clearing (J²+(i+u)²)².
        shapes = [multiply(denominator, denominator), multiply(cosine, denominator),
                  multiply(cosine, cosine), multiply(sine, denominator), multiply(cosine, sine)]
        rows = [[r*c for c in shape] for r, shape in zip(roots, shapes)]
        vectors, transform = reduced_basis(rows, work)
    if previous is not None:
        previous.update(sector=i, rows=vectors, transform=transform)
    lower_den = scale*(j2+i*i)**2
    upper_den = scale*(j2+(i+1)**2)**2
    best = None
    for row, coeffs in zip(vectors, transform):
        if not any(coeffs[1:]):
            continue
        low = row[0]+sum(min(0, v) for v in row[1:])
        high = row[0]+sum(max(0, v) for v in row[1:])
        error = Fraction(sum(abs(c)*e for c, e in zip(coeffs, errors)), scale)
        low = Fraction(low, upper_den if low >= 0 else lower_den)-error
        high = Fraction(high, lower_den if high >= 0 else upper_den)+error
        start, end = -((-low.numerator)//low.denominator), high.numerator//high.denominator
        score = end-start+1, high-low
        if best is None or score < best[0]:
            best = score, coeffs, start, end
    _, coeffs, start, end = best
    work['possible_levels'] += end-start+1
    if start > end:
        work['empty_level_intervals'] += 1
    if start == end == 0:
        work['single_zero_levels'] += 1
    points = []
    for level in range(start, end+1):
        c = list(coeffs)
        c[0] -= level
        points.extend(ellipse_intersection(total, d, c, lo, hi, work))
    return sorted(points)


EXTRA_COUNTERS = ('empty_coordinate_intervals', 'lll_calls', 'lll_reductions', 'lll_swaps',
                  'possible_levels', 'empty_level_intervals', 'single_zero_levels',
                  'resultants', 'integer_root_nodes', 'point_checks', 'reused_bases')


def scan(n, d, k, work, max_blocks, *, sectors=None, reuse_basis=False):
    """Yield all points of the public ellipse up to the shared block budget."""
    for key in ('blocks', 'coordinate_positions')+EXTRA_COUNTERS:
        work.setdefault(key, 0)
    total = k*n
    if sectors is None:
        sectors = sector_count(total, d)
    if sectors < 1:
        raise ValueError('expected at least one sector')
    if total < 1+d:
        return
    amplitude = amplitudes(total, d, sectors)
    previous = {} if reuse_basis else None
    for i in range(sectors):
        if max_blocks is not None and work['blocks'] >= max_blocks:
            work['outcome'] = 'block_limit'
            return
        work['blocks'] += 1
        yield from sector_points(total, d, sectors, i, amplitude, work, previous=previous)


def search(n, d=1, k=1, *, sectors=None, max_blocks=None, reuse_basis=False):
    """Search one public ellipse with a sector budget and retain all verified points."""
    if n < 3 or d <= 0 or k <= 0 or (max_blocks is not None and max_blocks < 0):
        raise ValueError('expected n >= 3, positive d,k and nonnegative block budget')
    if sectors is None:
        sectors = sector_count(k*n, d)
    work = Counter()
    points = list(scan(n, d, k, work, max_blocks, sectors=sectors, reuse_basis=reuse_basis))
    complete = work.get('outcome') != 'block_limit'
    first_root = None
    factor = None
    for t, v in points:
        common = gcd(v, n)
        if 1 < common < n:
            factor = common
            break
        if common == 1:
            root = t*pow(v, -1, n) % n
            if first_root is None:
                first_root = root
            elif root not in (first_root, -first_root % n):
                factor = gcd(root-first_root, n)
                break
    return dict(sectors=sectors, interval_complete=complete, work=dict(work),
                points=sorted(points), factor=factor)


def compare(n, d=1, k=1, *, sectors=None, max_blocks=None, reuse_basis=False):
    """Compare the auxiliary and established scans; each receives the same block cap."""
    result = search(n, d, k, sectors=sectors, max_blocks=max_blocks, reuse_basis=reuse_basis)
    work = Counter()
    points = list(line_scan(n, d, k, work, max_blocks))
    return dict(auxiliary=result, lines=dict(work=dict(work), points=sorted(points),
                                            interval_complete=work.get('outcome') != 'block_limit'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--d', type=int, default=1)
    parser.add_argument('--k', type=int, default=1)
    parser.add_argument('--sectors', type=int)
    parser.add_argument('--max-blocks', type=int)
    parser.add_argument('--reuse-basis', action='store_true')
    args = parser.parse_args()
    print(json.dumps(compare(args.n, args.d, args.k, sectors=args.sectors,
                             max_blocks=args.max_blocks, reuse_basis=args.reuse_basis), indent=2))
