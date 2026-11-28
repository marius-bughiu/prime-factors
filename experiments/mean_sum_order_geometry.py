"""Bound pooled square-test savings on the normalized area 1/2 < xy, x < y < 1.

Write D=(sqrt(y)-sqrt(x))² for the ascending prefix length and G=(1-x)(1-y)
for the remaining length. The unit product residue 1 modulo 25 admits ten
ordered residue pairs in each group. Favoring the two singular sums saves
5D/100 for the first group and costs 2G/100 for the second, in units of the
upper factor bound B. Ordinary ascending search costs 7D/100 in both.
"""

import json
from fractions import Fraction as F
from math import isqrt


def grid(mesh):
    """Bound both integrals using integer bounds on each dyadic rectangle."""
    root_den = 2**24
    roots = [isqrt(i*root_den**2//mesh) for i in range(mesh+1)]
    ceilings = [r + (mesh*r*r < i*root_den**2) for i, r in enumerate(roots)]
    d_lo = d_hi = g_lo = g_hi = full = possible = 0
    for i in range(mesh//2, mesh):
        for j in range(i, mesh):
            # This box lies entirely below xy=1/2.
            if 2*(i+1)*(j+1) <= mesh**2:
                continue
            possible += 1
            d_hi += (ceilings[j+1]-roots[i])**2
            g_hi += (mesh-i)*(mesh-j)
            # Diagonal and product-boundary boxes contribute only an upper bound.
            if i < j and 2*i*j >= mesh**2:
                full += 1
                d_lo += max(0, roots[j]-ceilings[i+1])**2
                g_lo += (mesh-i-1)*(mesh-j-1)
    return (F(d_lo, mesh**2*root_den**2), F(d_hi, mesh**2*root_den**2),
            F(g_lo, mesh**4), F(g_hi, mesh**4), full, possible)


def closed_integrals():
    """Independent rational bounds for the two exact iterated integrals.

    Integrating first in x from 1/(2y) to y, then in y from 1/sqrt(2) to 1,
    gives D=-23/72+sqrt(2)/9+sqrt(2)*log(2)/6 and G=7/32-5*log(2)/16.
    """
    scale = 2**80
    root = isqrt(2*scale**2)
    u, v = F(root, scale), F(root+1, scale)
    # log(2)=2*atanh(1/3). Upper-bound the remaining positive geometric tail.
    terms = 32
    log_lo = sum(F(2, (2*k+1)*3**(2*k+1)) for k in range(terms))
    log_hi = log_lo + F(2, (2*terms+1)*3**(2*terms+1))*F(9, 8)
    d_lo = -F(23, 72)+u/9+u*log_lo/6
    d_hi = -F(23, 72)+v/9+v*log_hi/6
    g_lo = F(7, 32)-5*log_hi/16
    g_hi = F(7, 32)-5*log_lo/16
    return d_lo, d_hi, g_lo, g_hi


def saving_bounds(bounds, ratio=F(1), rounding=F(0)):
    """Apply box count bounds after normalizing the smallest full-box mass to one.

    Each complete box and ordered pair of unit residues has relative mass between
    1 and ratio; every partial box has mass at most ratio. Rounding bounds the
    total normalized cost error after pooling the favorable and unfavorable groups.
    """
    dl, du, gl, gu = bounds
    net_lower = 5*dl-2*ratio*gu-rounding
    net_upper = 5*ratio*du-2*gl+rounding
    base_lower = 14*dl-rounding
    if base_lower <= 0 or net_upper <= 0:
        raise AssertionError('the given enclosure is too wide')
    lower_den = 14*ratio*du+rounding if net_lower >= 0 else base_lower
    return net_lower/lower_den, net_upper/base_lower


def decimal_interval(lo, hi, places=8):
    """Decimal endpoints rounded outwards using only integers."""
    scale = 10**places
    low = (lo.numerator*scale)//lo.denominator
    high = -((-hi.numerator*scale)//hi.denominator)
    if hi < lo:
        raise AssertionError('expected ordered bounds')
    return [f'{"-" if x < 0 else ""}{abs(x)//scale}.{abs(x)%scale:0{places}d}' for x in (low, high)]


def bmor25_ratio(mesh):
    """Use the supplied unconditional error 2B/(840·709²) on a 25-residue bin."""
    b = 2**1024
    denom = 840*709**2
    err = (2*b+denom-1)//denom
    lo = b//(14200*mesh) - err
    hi = (b+14180*mesh-1)//(14180*mesh) + err
    return F(hi**2, (lo-1)**2)


def main():
    exact = closed_integrals()
    exact_saving = saving_bounds(exact)
    if not (F(70357236, 10**9) < exact_saving[0] <= exact_saving[1] < F(70357237, 10**9)):
        raise AssertionError('closed-form enclosure failed')
    for mesh in (128, 256, 512, 4096):
        dl, du, gl, gu, full, possible = grid(mesh)
        if not (dl <= exact[0] <= exact[1] <= du and gl <= exact[2] <= exact[3] <= gu):
            raise AssertionError('grid and independent integral bounds disagree')
        cells = dl, du, gl, gu
        area_saving = saving_bounds(cells)
        # Every interval length differs from its continuous counterpart by at
        # most two integers. Counting at most seven residue classes modulo
        # 100 costs <1000/B of error after multiplying a count by 100/B.
        # Two equally numerous residue groups enter each of the net and base sums.
        ratio = F(1005, 1000)
        error_unit = F(2000, 2**1024)*F(possible, mesh**2)
        weighted_saving = saving_bounds(cells, ratio, ratio*error_unit)
        if mesh == 4096 and weighted_saving[0] <= F(659, 10000):
            raise AssertionError('fine grid did not certify the stated lower bound')
        result = dict(mesh=mesh, full=full, possible=possible,
                      signed_integral=decimal_interval(5*dl-2*gu, 5*du-2*gl),
                      area_saving=decimal_interval(*area_saving),
                      closed_form_area_saving=decimal_interval(*exact_saving, places=10),
                      conditional_rectangle_saving=decimal_interval(*weighted_saving),
                      assumed_max_to_min_rectangle_mass=str(ratio))
        if mesh <= 512:
            r25 = bmor25_ratio(mesh)
            result['fixed_one_mod25_bmor_saving'] = decimal_interval(
                *saving_bounds(cells, r25, r25*error_unit))
        if mesh in (256, 512):
            # PrimeGridMass.five_mass_ratios applies to the pooled square-product
            # group. Four pairs of unit residues give each of y=x and y=-x mod 5.
            r5 = F(1018 if mesh == 256 else 1033, 1000)
            interval = saving_bounds(cells, r5, r5*error_unit)
            if mesh == 256 and interval[0] <= F(25, 1000):
                raise AssertionError('coarse grid lost the 2.5% saving')
            result['all_square_products_mod5_bmor_saving'] = decimal_interval(*interval)
        print(json.dumps(result))


if __name__ == '__main__':
    main()
