"""Stationary weights on a six-sided bound for balanced factor pairs."""

from math import gcd

from .midpoint_weights import choose_radix
from .powered_order import prime_powers
from .short_basis_sieve import reduced_lattice_basis


def cube_threshold(height, gap_width):
    """R³ must strictly exceed this integer for every slope to have one trace."""
    return 4*height*gap_width**2 // (gap_width+3*height)


def slope_count(radix, work):
    """Compute the number of stationary slopes in the unit group of a public radix."""
    count = 1
    for p, power in prime_powers(radix, work).items():
        units = power//p*(p-1)
        roots = (1 if power == 2 else 2 if power == 4 else 4) if p == 2 else 2
        count *= units//roots
    return count


def choose_slope_radix(n, height, gap_width, work, multiplier=1):
    """Minimize the slope count over at most 64 admissible common-stride choices."""
    original = choose_radix(n, 4*height*gap_width)
    smaller = choose_radix(n, cube_threshold(height, gap_width))
    low, high = sorted((original, smaller))
    stride = gcd(low, high)
    steps = (high-low)//stride
    samples = min(steps, 63)
    best = None
    for j in range(samples+1):
        index = j*steps//samples if samples else 0
        radix = low+index*stride
        if gcd(n, radix) == 1:
            work['radix_candidates'] += 1
            current = (slope_count(multiplier*radix, work), radix)
            if best is None or current < best:
                best = current
    return best[1]


def weight_interval(radix, slope, lower, upper, gap, work):
    """Minimize the hexagonal width using the four directions of the rectangular basis."""
    height, gap_width = upper-lower, 2*gap

    def transform(pair):
        a, b = pair
        z, v = height*(a+b), gap_width*(a-b)
        return z+v, z-v

    def width(pair):
        a, b = pair
        spread = abs(a-b)
        return max(gap_width*spread, height*abs(a+b)+(gap_width-3*height)*spread)

    first, second = reduced_lattice_basis(radix, slope, transform, work)
    a, b = first
    c, d = second
    choices = (first, second, (c+a, d+b), (c-a, d-b))
    a, b = min(choices, key=width)
    x, y = abs(a+b), abs(a-b)
    left = min(x*lower-y*(gap-3*height), x*upper-y*gap)
    right = x*upper+y*gap
    if a+b < 0:
        left, right = -right, -left
    if (a, b) == (0, 0) or (b-slope*a) % radix or right-left >= radix**2:
        raise ArithmeticError('failed to certify the hexagonal one-trace interval')
    return a, b, left, right
