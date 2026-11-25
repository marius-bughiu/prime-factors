"""Compare one adapted quartic with ordinary quartics on the two public windows of 9009."""

from collections import Counter
import json
import argparse
from math import isqrt

from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_divisor_window import checked_height, jet_basis, search


def paired_coordinates(row, shift):
    """Coordinates of a quartic in 1, x, P, xP, P² for P=x²−shift."""
    a,b,c,d,e = row
    return [a+shift*(c+shift*e), b+shift*d, c+2*shift*e, d, e]


def compare(n, *, half_separation=3, radius=1):
    """Test both disjoint windows around the public equal-width midpoint."""
    if n < 3 or n%2 == 0 or not 0 < radius < half_separation:
        raise ValueError('expected an odd product and two disjoint positive-radius windows')
    factor_bits = (n.bit_length()+1)//2
    largest = (1<<factor_bits)-1
    floor = max(1<<(factor_bits-1),(n+largest-1)//largest)
    ceiling = isqrt(n)
    center = ((floor+ceiling)//2)|1
    anchor = (n-center)//2
    bound_x = half_separation+radius
    if center-2*bound_x < floor or center+2*bound_x > ceiling:
        raise ValueError('the requested odd windows extend beyond the feasible smaller-factor band')
    bound_p = 2*half_separation*radius
    shift = half_separation**2+radius**2
    weights = [1,bound_x,bound_p,bound_x*bound_p,bound_p**2]
    work = Counter()
    basis = jet_basis(n,anchor)
    scaled = [[a*b for a,b in zip(paired_coordinates(row,shift),weights)] for row in basis]
    _, rows = reduced_basis(scaled,work,initial_coefficients=basis)
    heights = []
    for row in rows:
        checked_height(n,anchor,radius,row)
        heights.append(sum(abs(a)*w for a,w in zip(paired_coordinates(row,shift),weights)))
    chosen = min(range(len(rows)),key=heights.__getitem__)
    lower = center-2*bound_x
    verified = heights[chosen] < lower**2
    roots = []
    if verified:
        for offset_center in (-half_separation,half_separation):
            roots.extend(integer_roots(rows[chosen],offset_center-radius,offset_center+radius,work))
    divisors = [center+2*x for x in sorted(roots) if n%(center+2*x)==0]
    ordinary = []
    for c,w in ((center-2*half_separation,radius),(center+2*half_separation,radius),
                (center,bound_x)):
        result = search(n,c,w,modulus_limit=0)
        ordinary.append({key:result[key] for key in ('center','radius','height','height_bound',
                        'relation_verified','divisors','lll_calls','lll_reductions','lll_swaps')})
    return dict(n=n,feasible=[floor,ceiling],center=center,anchor=anchor,
                half_separation=half_separation,radius=radius,row=rows[chosen],
                coordinates=paired_coordinates(rows[chosen],shift),weights=weights,
                height=heights[chosen],height_bound=lower**2,relation_verified=verified,
                roots=sorted(roots),divisors=divisors,
                work=dict(work),ordinary=ordinary)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int,nargs='?',default=9009)
    parser.add_argument('--half-separation',type=int,default=3)
    parser.add_argument('--radius',type=int,default=1)
    args = parser.parse_args()
    print(json.dumps(compare(args.n,half_separation=args.half_separation,radius=args.radius),indent=2))
