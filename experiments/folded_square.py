"""Decode a single signed integer encoding 2^n F(1) for an n-bit product.

--emit generates synthetic side information from the already-certified fixture
factors. --decode reads just {"n": ..., "word": ...} from standard input.
Only the small direct-sum tests compute the reading from the product alone.
"""
from argparse import ArgumentParser
from json import dumps, load
from math import gcd, isqrt
import sys

if __package__:
    from .divisor_samples import MAX_PRODUCT
    from .salie_reference import FIXTURE, ceil_div, cosine_bounds, fixture, pi_bounds
    from .salie_seed import rounded_sum
else:
    from divisor_samples import MAX_PRODUCT
    from salie_reference import FIXTURE, ceil_div, cosine_bounds, fixture, pi_bounds
    from salie_seed import rounded_sum


MAX_BITS = 2048
SCORE_BITS = 40


def working_bits(n):
    if n < 3 or n % 2 == 0 or n.bit_length() > MAX_BITS:
        raise ValueError(f"expected an odd product of at most {MAX_BITS} bits")
    return max(128, n.bit_length()+96)


def produce(p, q):
    """Generate the rounded full sum synthetically via its four CRT roots."""
    n = p*q
    bits = working_bits(n)
    h = 1+p*((-2*pow(p, -1, q)) % q)
    public = cosine_bounds(1, n, bits)
    hidden = cosine_bounds(h, n, bits)
    low, high = [2*(public[i]+hidden[i]) for i in range(2)]
    grid = 1 << (bits-n.bit_length())
    word = (low+grid//2)//grid
    margin = min(low-(word*grid-grid//2), word*grid+grid//2-high)
    if margin <= 0:
        raise ArithmeticError("full sum interval crosses a quantization boundary")
    return dict(n=str(n), word=str(word)), dict(
        scale_bits=bits, raw_width_units=high-low, raw_rounding_margin_units=margin)


def first_quarter_phase(low, high, bits):
    """Enclose arccos(clip(c))/(2π) for the entire supplied cosine interval."""
    scale = 1 << bits
    low, high = [max(0, min(scale, endpoint)) for endpoint in (low, high)]
    if low == high == 0:
        return scale//4, scale//4
    if low == high == scale:
        return 0, 0

    # Four half angles reduce theta <= pi/2 to theta/16. Then
    # z = sin(theta/32) gives theta/(2*pi) = 16*arcsin(z)/pi.
    for _ in range(4):
        low = isqrt((scale+low)*scale//2)
        high = min(scale, 1+isqrt((scale+high)*scale//2))
    z_low = isqrt((scale-high)*scale//2)
    z_high = 1+isqrt((scale-low)*scale//2)
    square_low, square_high = z_low*z_low//scale, ceil_div(z_high*z_high, scale)
    if 4*square_high > scale:
        raise ArithmeticError("half-angle reduction failed its geometric-tail bound")

    # arcsin(z) has positive terms, with ratio z²(2j+1)²/[2(j+1)(2j+3)].
    term_low, term_high = z_low, z_high
    sum_low = sum_high = j = 0
    while term_high > 2:
        sum_low += term_low
        sum_high += term_high
        divisor = scale*2*(j+1)*(2*j+3)
        term_low = term_low*square_low*(2*j+1)**2//divisor
        term_high = ceil_div(term_high*square_high*(2*j+1)**2, divisor)
        j += 1
    # From the first omitted term onward the ratio is at most 1/4.
    sum_high += 2*term_high
    pi_low, pi_high = pi_bounds(bits)
    return 16*sum_low*scale//pi_high, min(scale//4, ceil_div(16*sum_high*scale, pi_low))


def score_certificate(n, b, low, high, bits):
    scale = 1 << bits
    phase_low, phase_high = first_quarter_phase(low, high, bits)
    score_scale = 1 << SCORE_BITS
    # Outward bounds on b²N*phase² - b²/N, in fixed units of 2^-SCORE_BITS.
    denominator = n*scale**2
    numerators = [b*b*score_scale*((n*z)**2-scale**2) for z in (phase_low, phase_high)]
    left = numerators[0]//denominator
    right = ceil_div(numerators[1], denominator)
    k = (left+score_scale//2)//score_scale
    margin = min(left-(k*score_scale-score_scale//2), k*score_scale+score_scale//2-right)
    return dict(multiplier=b, quotient=k, score_low_units=left, score_high_units=right,
                rounding_margin_units=margin)


def decode(n, word):
    """Verify the rounded quotient for each sign, then check squares and gcds."""
    bits = working_bits(n)
    if type(word) is not int or abs(word) > (4 << n.bit_length()):
        raise ValueError("full sum word lies outside its signed range")
    grid = 1 << (bits-n.bit_length())
    left, right = cosine_bounds(1, n, bits)
    low = (word*grid-grid//2)//2 - right
    high = ceil_div(word*grid+grid//2, 2) - left
    scale = 1 << bits
    if low > scale or high < -scale:
        raise ValueError("word is inconsistent with its public cosine")
    certificates = [score_certificate(n, 1, low, high, bits),
                    score_certificate(n, 2, -high, -low, bits)]
    for certificate in certificates:
        if certificate["rounding_margin_units"] <= 0:
            continue
        b = certificate["multiplier"]
        candidate = n*certificate["quotient"] + b*b
        if candidate < 0:
            continue
        a = isqrt(candidate)
        if a*a != candidate:
            continue
        root = a*pow(b, -1, n) % n
        if root in (1, n-1) or root*root % n != 1:
            continue
        p, q = sorted((gcd(root-1, n), gcd(root+1, n)))
        if p > 1 and p*q == n:
            return dict(bits=n.bit_length(), readings=1, score_scale_bits=SCORE_BITS,
                        branches=certificates, multiplier=b, root=str(root),
                        factors=[str(p), str(q)])
    raise ValueError("no certified split follows from the supplied word")


def direct(n, max_terms):
    """Evaluate F(1) from a bounded product, then decode only its rounded word."""
    if n < 3 or n % 2 == 0 or max_terms < 0:
        raise ValueError("expected an odd product and a nonnegative term limit")
    work = dict(outcome="budget", factor=None, terms=0, sums=0, unit_gcds=0,
                unit_inverses=0, jacobi_evaluations=0, word=None, multiplier=None)
    if n > MAX_PRODUCT:
        return dict(work, outcome="size_limit")
    if max_terms == 0:
        return work
    try:
        work["word"] = rounded_sum(n, 1, n.bit_length(), max_terms, work)
        if work["word"] is None:
            return work
        split = decode(n, work["word"])
    except ValueError:
        return dict(work, outcome="uncertified")
    return dict(work, outcome="split", factor=int(split["factors"][0]),
                multiplier=split["multiplier"])


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", action="store_true", help="emit the synthetic rounded-word payload")
    mode.add_argument("--decode", action="store_true", help="decode the public payload from stdin")
    mode.add_argument("--direct", type=int, metavar="N", help="evaluate the sum from a small product")
    parser.add_argument("--max-terms", type=int, default=MAX_PRODUCT)
    args = parser.parse_args()
    if args.direct is not None:
        result = direct(args.direct, args.max_terms)
    elif args.decode:
        payload = load(sys.stdin)
        if set(payload) != {"n", "word"}:
            parser.error("expected only n and word in the input")
        result = decode(int(payload["n"]), int(payload["word"]))
    else:
        p, q = fixture()
        payload, audit = produce(p, q)
        if args.emit:
            result = payload
        else:
            decoded = decode(int(payload["n"]), int(payload["word"]))
            if list(map(int, decoded["factors"])) != sorted((p, q)):
                raise ArithmeticError("decoded factors disagree with the certified fixture")
            result = dict(fixture=FIXTURE, mode="synthetic_side_information", **audit, **decoded)
    print(dumps(result))
