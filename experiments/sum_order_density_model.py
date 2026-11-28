"""Compare three orders in the continuous equal-area factor-pair model.

On a fixed product n in [1/2, 1), H=-log(n)/2 and a is uniform on [0,H].
The normalized sum is 2*sqrt(n)*cosh(a). For square product residues modulo
five, two candidate classes have weight five each, and five have weight two
each. The target lies in either group with probability one half. This
calculation integrates these continuous lengths. It uses no integer targets.
"""

import json
from fractions import Fraction
from math import asinh, exp, isqrt, log, sinh, sqrt

if __package__:
    from .mean_sum_order_geometry import closed_integrals, decimal_interval
else:
    from mean_sum_order_geometry import closed_integrals, decimal_interval


def simpson(f, left, right, panels):
    """Composite Simpson quadrature on an interval where f is smooth."""
    step = (right - left) / panels
    return step / 3 * (f(left) + f(right) + sum(
        (4 if i % 2 else 2) * f(left + i * step) for i in range(1, panels)
    ))


def span(gap):
    """cosh(gap)-1 evaluated without subtracting almost equal numbers."""
    return 2 * sinh(gap / 2) ** 2


def cutoff_span(gap, weight_ratio):
    """cosh(asinh(weight_ratio*sinh(gap)))-1, before clipping to H."""
    z = (weight_ratio * sinh(gap)) ** 2
    return z / (sqrt(1 + z) + 1)


def costs(panels):
    """Area integrals in identical units; the comparison uses their ratios."""
    hmax = log(2) / 2

    def slice_cost(h, schedule):
        # dn = -2 exp(-2h) dh. Each physical sum length supplies 2 exp(-h).
        # The common factor 1/100 converting class lengths to tests cancels.
        width = span(h)
        # A weight-two target beyond this gap follows all weight-five candidates.
        split = asinh(2 / 5 * sinh(h))
        def at(a):
            d = span(a)
            if schedule == 'ascending':
                return 7 * d
            if schedule == 'favored_first':
                return (2 * d + (2 * width + 5 * d)) / 2
            if schedule == 'density':
                favored_work = 2 * d + 5 * cutoff_span(a, 2 / 5)
                ordinary_work = 5 * d + 2 * min(width, cutoff_span(a, 5 / 2))
                return (favored_work + ordinary_work) / 2
            raise ValueError(schedule)
        return 4 * exp(-3 * h) * (
            simpson(at, 0, split, panels) + simpson(at, split, h, panels)
        )

    return {name: simpson(lambda h: slice_cost(h, name), 0, hmax, panels)
            for name in ('ascending', 'favored_first', 'density')}


def summary(totals):
    a, f, d = (totals[key] for key in ('ascending', 'favored_first', 'density'))
    # With all eligible unit residue pairs included, half are nonsquare
    # products and unchanged ascending work is 10/7 of the square baseline.
    other = 10 / 7 * a
    return {
        'square_product_model': {
            'favored_first_saving_vs_ascending': 1 - f / a,
            'density_saving_vs_ascending': 1 - d / a,
            'density_saving_vs_favored_first': 1 - d / f,
        },
        'all_products_model': {
            'favored_first_saving_vs_ascending': 1 - (f + other) / (a + other),
            'density_saving_vs_ascending': 1 - (d + other) / (a + other),
            'density_saving_vs_favored_first': 1 - (d + other) / (f + other),
        },
    }


def grid_density_cost(mesh=1024):
    """Rational enclosure on square boxes of the original factor triangle.

    For factor coordinates x≤y, let n=xy and gap=y−x. Each cross-group
    prefix length is sqrt(4n+(ratio*gap)²)−2sqrt(n). Rationalizing it
    shows this length increases with gap and decreases with n. The overall
    cap (1−sqrt(n))² decreases with n in [1/2,1]. We bound each expression
    using these monotonicities, with outward-rounded integer square roots.
    Only full boxes contribute to the lower integral.
    """
    unit = 2**24
    denom = mesh*unit
    lower = upper = 0

    def root(t, up):
        z = isqrt(t)
        return z + (up and z*z < t)

    def bound(product, gap, up):
        # All returned lengths use common denominator denom².
        product_root = root(unit**2 * product, not up)
        cap = (denom - product_root)**2

        def length(c, d):
            radical = 4*d*d*product + c*c*gap*gap
            numerator = root(unit**2*radical, up) - 2*d*product_root
            # Round outwards while dividing by d; length is nonnegative.
            return denom*max(0, (numerator + (d-1 if up else 0))//d)

        return 7*length(1, 1) + 5*length(2, 5) + 2*min(cap, length(5, 2))

    for i in range(mesh//2, mesh):
        for j in range(i, mesh):
            product_hi = (i+1)*(j+1)
            if 2*product_hi <= mesh**2:
                continue
            product_lo = i*j
            upper += bound(product_lo, j+1-i, True)
            if i < j and 2*product_lo >= mesh**2:
                lower += bound(product_hi, j-i-1, False)
    # Equal target probabilities for the two residue groups and box area 1/m².
    divisor = 2*mesh**2*denom**2
    return Fraction(lower, divisor), Fraction(upper, divisor)


def main():
    coarse, fine = costs(32), costs(64)
    if max(abs(coarse[k] / fine[k] - 1) for k in fine) > 1e-6:
        raise AssertionError('quadrature refinement changed a cost unexpectedly')
    result = summary(fine)
    # An independent integration of the baseline and favored-first costs.
    d = -23 / 72 + sqrt(2) / 9 + sqrt(2) * log(2) / 6
    g = 7 / 32 - 5 * log(2) / 16
    if abs(fine['ascending'] / (7*d) - 1) > 1e-7:
        raise AssertionError('ascending cost disagrees with its closed form')
    if abs(fine['favored_first'] / ((9*d + 2*g)/2) - 1) > 1e-7:
        raise AssertionError('favored-first cost disagrees with its closed form')
    dlo, dhi, glo, ghi = closed_integrals()
    lower, upper = grid_density_cost()
    if not lower <= fine['density'] <= upper:
        raise AssertionError('quadrature left the independent rectangle enclosure')
    result['rational_grid_square_product_savings'] = {
        'vs_ascending': decimal_interval(1-upper/(7*dlo), 1-lower/(7*dhi)),
        'vs_favored_first': decimal_interval(1-2*upper/(9*dlo+2*glo), 1-2*lower/(9*dhi+2*ghi)),
    }
    # Carry the unchanged half into both totals before forming the ratios.
    result['rational_grid_all_product_savings'] = {
        'vs_ascending': decimal_interval((7-upper/dlo)/17, (7-lower/dhi)/17),
        'vs_favored_first': decimal_interval(
            1-(2*upper+20*dhi)/(29*dlo+2*glo),
            1-(2*lower+20*dlo)/(29*dhi+2*ghi)),
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
