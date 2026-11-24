"""Recover a mixed square root in a short interval using continued fractions."""
from argparse import ArgumentParser
from json import dumps, load
from math import gcd, isqrt
import sys

if __package__:
    from .folded_square import first_quarter_phase, produce, working_bits
    from .salie_reference import ceil_div, cosine_bounds, fixture
else:
    from folded_square import first_quarter_phase, produce, working_bits
    from salie_reference import ceil_div, cosine_bounds, fixture


def approximate_slope(numerator, n, bound):
    """Return the last convergent denominator <= bound and its signed residue."""
    previous, current = n, numerator % n
    old_b, b = 0, 1
    steps = 0
    while current:
        a, remainder = divmod(previous, current)
        next_b = old_b+a*b
        if next_b > bound:
            break
        old_b, b = b, next_b
        previous, current = current, remainder
        steps += 1
    residue = numerator*b % n
    if 2*residue > n:
        residue -= n
    return b, residue, steps


def search_interval(n, low, high, max_lifts, *, single_only=False):
    """Use a scaled quadratic. A cap applies to all possible integer lifts."""
    if n < 3 or not 0 <= low <= high < n or max_lifts < 0:
        raise ValueError("invalid root interval or lift budget")
    center = (low+high)//2
    radius = high-center
    bound = max(1, isqrt(n//max(1, radius)))
    b, r, steps = approximate_slope(2*center, n, bound)
    s = b*(center*center-1) % n
    error = b*radius**2 + abs(r)*radius
    first, last = ceil_div(s-error, n), (s+error)//n
    work = dict(low=str(low), high=str(high), width=str(high-low), euclidean_steps=steps,
                possible_lifts=str(last-first+1), square_tests=0, root=None, factor=None)
    if single_only and last > first:
        return work
    for t in range(first, min(last+1, first+max_lifts)):
        work["square_tests"] += 1
        discriminant = r*r-4*b*(s-t*n)
        if discriminant < 0:
            continue
        d = isqrt(discriminant)
        if d*d != discriminant:
            continue
        for numerator in (-r-d, -r+d):
            v, remainder = divmod(numerator, 2*b)
            h = center+v
            if remainder or not low <= h <= high or h*h % n != 1:
                continue
            factor = gcd(h-1, n)
            if 1 < factor < n:
                return dict(work, root=str(h), factor=min(factor, n//factor))
    return work


def cube_radius(n):
    """Largest R with 64 R³ <= n."""
    lo, hi = 0, 1 << ((n.bit_length()+2)//3)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if 64*mid**3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def decode_word(n, word, fractional_bits, max_lifts=2, max_blocks=8):
    """Enclose folded roots consistent with a rounded reading, then search them."""
    # A cosine error near an extremum can become its square root in phase.
    # Use guard precision for the inverse endpoints separately from the word.
    bits = working_bits(n)+n.bit_length()
    if (type(fractional_bits) is not int or not 1 <= fractional_bits <= n.bit_length()
            or type(word) is not int or abs(word) > (4 << fractional_bits)
            or max_lifts < 0 or max_blocks < 0):
        raise ValueError("invalid reading, precision or lift budget")
    scale = 1 << bits
    grid = 1 << (bits-fractional_bits)
    public_low, public_high = cosine_bounds(1, n, bits)
    low = (word*grid-grid//2)//2-public_high
    high = ceil_div(word*grid+grid//2, 2)-public_low
    if low > scale or high < -scale:
        raise ValueError("word is inconsistent with its public cosine")
    intervals = []
    for reflected, (left, right) in enumerate(((low, high), (-high, -low))):
        if right < 0 or left > scale:
            continue
        x, y = first_quarter_phase(left, right, bits)
        if reflected:
            x, y = scale//2-y, scale//2-x
        lo, hi = ceil_div(n*x, scale), n*y//scale
        if lo <= hi:
            intervals.append((lo, hi))
    searches = []
    factor = None
    tests = blocks_needed = planning_steps = 0
    if intervals:
        # When the rounded cosine crosses zero, the two signed branches
        # meet at a quarter turn. Cover their union with one integer interval.
        lo, hi = intervals[0][0], intervals[-1][1]
        whole = search_interval(n, lo, hi, max_lifts if max_blocks else 0, single_only=True)
        if int(whole["possible_lifts"]) <= 1:
            blocks_needed = 1
            if max_blocks:
                searches.append(whole)
                tests, factor = whole["square_tests"], whole["factor"]
            else:
                planning_steps = whole["euclidean_steps"]
        else:
            planning_steps = whole["euclidean_steps"]
            width = 2*cube_radius(n)+1
            blocks_needed = ceil_div(hi-lo+1, width)
            for index in range(min(blocks_needed, max_blocks)):
                if tests == max_lifts:
                    break
                start = lo+index*width
                search = search_interval(n, start, min(hi, start+width-1), max_lifts-tests)
                searches.append(search)
                tests += search["square_tests"]
                factor = search["factor"]
                if factor is not None:
                    break
    return dict(fractional_bits=fractional_bits, max_lifts=max_lifts, max_blocks=max_blocks,
                blocks_needed=blocks_needed, planning_steps=planning_steps,
                intervals=searches, square_tests=tests, factor=factor)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--emit", type=int, metavar="BITS", help="generate a synthetic fixed reading")
    mode.add_argument("--decode", action="store_true", help="decode a reading from standard input")
    parser.add_argument("--max-lifts", type=int, default=2)
    parser.add_argument("--max-blocks", type=int, default=8)
    args = parser.parse_args()
    if args.emit is not None:
        p, q = fixture()
        payload, _ = produce(p, q, args.emit)
        print(dumps(dict(payload, fractional_bits=args.emit)))
    else:
        payload = load(sys.stdin)
        if set(payload) != {"n", "word", "fractional_bits"}:
            parser.error("expected exactly n, word and fractional_bits")
        print(dumps(decode_word(int(payload["n"]), int(payload["word"]),
                                payload["fractional_bits"], args.max_lifts, args.max_blocks)))
