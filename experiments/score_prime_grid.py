"""Bound aggregate score-order savings using the published prime counts per residue bin.

The range is the triangular population of two distinct sorted 1,024-bit primes
with a full 2,048-bit product. Only aggregate integer rectangle bounds enter the
calculation. This program accepts neither a product nor a list of candidate sums.
"""

from fractions import Fraction
from math import isqrt

B = 2**1024
ROOT_SCALE = 2**24


def rounded_root(n, up):
    root = isqrt(n)
    return root + (up and root*root != n)


def lengths(mesh, product, gap, up):
    """Outward bounds on D, the two opposing-group distances, and the total cap.

    The grid coordinate product and gap are integers scaled by mesh² and mesh.
    The returned lengths share denominator (mesh * ROOT_SCALE)².
    """
    m = mesh * ROOT_SCALE
    # All three distances decrease with n, and increase with gap.
    base = rounded_root(ROOT_SCALE**2 * product, not up)

    def distance(c, d):
        radical = ROOT_SCALE**2 * (4*d*d*product + c*c*gap*gap)
        num = rounded_root(radical, up) - 2*d*base
        return m*max(0, (num + (d-1 if up else 0)) // d)

    return distance(1, 1), distance(2, 5), distance(5, 2), (m-base)**2


def grid(mesh):
    """Positive gains come only from full boxes. Every possible box pays losses."""
    vals = dict(ascending_gain=0, ascending_loss=0, global_gain=0, global_loss=0,
                square_ascending=0, square_global=0, other_cost=0, possible=0, full=0)
    for i in range(mesh//2, mesh):
        for j in range(i, mesh):
            nlo, nhi = i*j, (i+1)*(j+1)
            if 2*nhi <= mesh**2:
                continue
            vals['possible'] += 1
            complete = i < j and 2*nlo >= mesh**2
            vals['full'] += complete
            dlo, small_lo, big_lo, cap_lo = lengths(mesh, nhi, max(0, j-i-1), False)
            dhi, small_hi, big_hi, cap_hi = lengths(mesh, nlo, j-i+1, True)
            # Ascending vs score. Favored hits skip some ordinary tests before
            # the true sum. Ordinary hits pay extra favored tests after it.
            vals['ascending_gain'] += complete * 5*max(0, dlo-small_hi)
            vals['ascending_loss'] += 2*max(0, min(cap_hi, big_hi)-dlo)
            # Global favored-first vs score. Ordinary hits skip favored tests in
            # the tail. Favored hits pay ordinary tests from a shortened prefix.
            vals['global_gain'] += complete * 2*max(0, cap_lo-big_hi)
            vals['global_loss'] += 5*small_hi
            # Square-product branches each have four residue pairs. The
            # nonsquare branch has eight, hence twice the base cell mass.
            vals['square_ascending'] += 14*dhi
            vals['square_global'] += 7*dhi + 2*cap_hi
            vals['other_cost'] += 2*10*dhi
    return vals


def result(mesh):
    vals = grid(mesh)
    width = B // mesh
    lo_den, hi_den = {256: (2851, 2826), 512: (2861, 2816)}[mesh]
    # PrimeGridMass.bmor_five_bin gives these one-axis cardinality bounds.
    # Rectangles in full cells have distinct disjoint sorted factor intervals.
    # Subtracting one in the lower mass also suffices in a common-interval bound.
    low = (width//lo_den - 1)**2
    high = (width//hi_den)**2
    assert 2000*(mesh*ROOT_SCALE)**2 < B
    # Allow one integer unit per member of a branch for endpoint, tie and
    # incomplete-period errors after scaling counts by 100*(mesh*ROOT_SCALE)²/B.
    # A mod-100 class count on a real interval differs from length/100 by ≤1.
    # Endpoints of the integer factor-width interval differ by at most 2 from
    # the continuous endpoints, so 2000 in unscaled hundred-test units suffices.
    k = vals['possible']
    for name in ('ascending', 'global'):
        margin = low*vals[name+'_gain'] - high*(vals[name+'_loss'] + 2*k)
        assert margin > 0
        for group in ('squares', 'all'):
            base = vals['square_'+name] + 2*k
            if group == 'all':
                base += vals['other_cost'] + 2*k
            fraction = Fraction(margin, high*base)
            per_million = fraction.numerator * 10**6 // fraction.denominator
            print(f'{mesh} {name:9s} {group:7s} {per_million}/1000000')


if __name__ == '__main__':
    for size in (256, 512):
        result(size)
