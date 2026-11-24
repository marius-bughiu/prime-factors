"""Evaluate the fixed Salié reading using signed inverse orbits and polynomial blocks."""
from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt

if __package__:
    from .divisor_samples import MAX_PRODUCT
    from .folded_square import decode
    from .midpoint_readings import reading
    from .phase_interval import decode_word
    from .salie_reference import SCALE, ceil_div, cosine_bounds
    from .salie_seed import normalize_word
else:
    from divisor_samples import MAX_PRODUCT
    from folded_square import decode
    from midpoint_readings import reading
    from phase_interval import decode_word
    from salie_reference import SCALE, ceil_div, cosine_bounds
    from salie_seed import normalize_word


ONE = (SCALE, SCALE, 0, 0)
ZERO = (0, 0, 0, 0)


def unit_rectangle(turn, n):
    return (*cosine_bounds(turn, n), *cosine_bounds(n-4*turn, 4*n))


def multiply(x, y):
    """Outward-rounded product of two complex rectangles in units of 2^-128."""
    def bounds(a, b):
        products = [i*j for i in a for j in b]
        return min(products), max(products)

    ac, bd = bounds(x[:2], y[:2]), bounds(x[2:], y[2:])
    ad, bc = bounds(x[:2], y[2:]), bounds(x[2:], y[:2])
    return ((ac[0]-bd[1])//SCALE, ceil_div(ac[1]-bd[0], SCALE),
            (ad[0]+bc[0])//SCALE, ceil_div(ad[1]+bc[1], SCALE))


def add_multiple(total, rect, weight):
    if weight < 0:
        rect = rect[1], rect[0], rect[3], rect[2]
    return tuple(t + weight*x for t, x in zip(total, rect))


def search(n, max_orbits, fractional_bits=None):
    """Report sum work and any divisor encountered while identifying units."""
    if n < 3 or n % 2 == 0 or max_orbits < 0:
        raise ValueError("expected an odd product and a nonnegative orbit budget")
    if fractional_bits is None:
        fractional_bits = n.bit_length()
    if type(fractional_bits) is not int or not 1 <= fractional_bits <= n.bit_length():
        raise ValueError("invalid fractional precision")
    work = dict(outcome="budget", factor=None, scan_factor=None, word=None,
                orbits=0, unit_terms=0, membership_checks=0, inverses=0,
                trig_calls=0, complex_products=0, max_orbits=max_orbits,
                fractional_bits=fractional_bits, lift_tests=0)
    if n > MAX_PRODUCT:
        return dict(work, outcome="size_limit")
    if max_orbits == 0:
        return work

    width = isqrt(n-1)+1
    blocks = [ZERO]*ceil_div(n, width)
    step = unit_rectangle(1, n)
    work["trig_calls"] += 2
    powers = [ONE, step]
    while len(powers) < width:
        powers.append(multiply(powers[-1], step))
        work["complex_products"] += 1

    # Negation has equal real projection after Gauss normalization. Inversion
    # has identical phase and Jacobi sign. Visit one of these orbits at a time.
    a = (n+1)//2
    visited = bytearray(n//2+1)
    for x in range(1, n//2+1):
        if visited[x]:
            continue
        work["membership_checks"] += 1
        common = gcd(x, n)
        if common != 1:
            if work["scan_factor"] is None:
                work["scan_factor"] = common
                work["factor"] = common
            continue
        if work["orbits"] == max_orbits:
            return work
        inverse = pow(x, -1, n)
        partner = min(inverse, n-inverse)
        visited[partner] = 1
        multiplicity = 2 if partner == x else 4
        phase = a*(x+inverse) % n
        block, offset = divmod(phase, width)
        blocks[block] = add_multiple(blocks[block], powers[offset], multiplicity*reading(x, n))
        work["orbits"] += 1
        work["inverses"] += 1
        work["unit_terms"] += multiplicity

    stride = unit_rectangle(width, n)
    work["trig_calls"] += 2
    value = blocks[-1]
    for block in reversed(blocks[:-1]):
        value = add_multiple(block, multiply(value, stride), 1)
        work["complex_products"] += 1
    low, high = value[:2] if n % 4 == 1 else value[2:]
    if reading(a, n) < 0:
        low, high = -high, -low
    try:
        work["word"] = normalize_word(n, fractional_bits, low, high)
        if fractional_bits == n.bit_length():
            factor = int(decode(n, work["word"])["factors"][0])
        else:
            split = decode_word(n, work["word"], fractional_bits)
            factor = split["factor"]
            work["lift_tests"] = split["square_tests"]
    except ValueError:
        return dict(work, outcome="uncertified")
    if factor is None:
        return dict(work, outcome="unresolved_reading")
    return dict(work, outcome="decoded", factor=factor)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-orbits", type=int, default=MAX_PRODUCT)
    parser.add_argument("--fractional-bits", type=int)
    args = parser.parse_args()
    print(dumps(search(args.n, args.max_orbits, args.fractional_bits)))
