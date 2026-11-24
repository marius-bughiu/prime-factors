"""Synthetic 2048-bit Salié readings from certified factors, and a separate replay.

--emit writes only N and 89 signed decimal integers encoding 2^53 times F.
--decode reads that payload from stdin. Only the producer knows the factors.
All trigonometric enclosures use outward-rounded integers scaled by 2^128.
"""

import argparse
import json
import sys
from fractions import Fraction
from functools import lru_cache
from math import factorial
from pathlib import Path

if __package__:
    from .salie_residues import decode_phases, projection
else:
    from salie_residues import decode_phases, projection


FIXTURE = "continued-square-2048"
FRACTION_BITS = 53
SCALE = 1 << 128
GRID = SCALE >> FRACTION_BITS


def ceil_div(x, denominator):
    return -(-x // denominator)


@lru_cache(maxsize=1)
def pi_bounds():
    """Machin's identity, enclosing both arctangents by adjacent alternating sums."""
    def atan_bounds(q):
        partial = sum(Fraction((-1)**i, (2*i+1)*q**(2*i+1)) for i in range(40))
        return partial, partial + Fraction(1, 81*q**81)

    a, b = atan_bounds(5)
    c, d = atan_bounds(239)
    low, high = SCALE*(16*a-4*d), SCALE*(16*b-4*c)
    return low.numerator//low.denominator, ceil_div(high.numerator, high.denominator)


def cosine_bounds(turn, denominator):
    """Enclose cos(2π turn/denominator) by integer multiples of 1/SCALE."""
    residue = turn % denominator
    radius = min(residue, denominator-residue)
    negative = 4*radius > denominator
    numerator = denominator-2*radius if negative else 2*radius
    pi_low, pi_high = pi_bounds()
    x_low = pi_low*numerator//denominator
    x_high = ceil_div(pi_high*numerator, denominator)
    square_low = x_low*x_low//SCALE
    square_high = ceil_div(x_high*x_high, SCALE)
    term_low = term_high = low = high = SCALE
    for j in range(1, 25):
        divisor = SCALE*(2*j-1)*(2*j)
        term_low = term_low*square_low//divisor
        term_high = ceil_div(term_high*square_high, divisor)
        if j % 2:
            low, high = low-term_high, high-term_low
        else:
            low, high = low+term_low, high+term_high
    # The degree-49 Taylor polynomial ends at degree 48. All omitted
    # error is bounded by 2^50/50! because the reduced angle is < 2.
    if not pi_high < 4*SCALE or not SCALE*2**50 < factorial(50):
        raise ArithmeticError("Taylor remainder exceeds the one-unit allowance")
    return (-high-1, -low+1) if negative else (low-1, high+1)


def schedule(n):
    if n.bit_length() != 2048 or n % 2 == 0:
        raise ValueError("this reference expects a 2048-bit odd product")
    return projection(2048, FRACTION_BITS)["primes"]


def produce_readings(p, q):
    """Use one CRT root calculation for all readings. Never called by the decoder."""
    n = p*q
    root = 1+p*((-2*pow(p, -1, q)) % q)
    readings = []
    min_margin = GRID
    max_width = max_error = 0
    for prime in schedule(n):
        t = pow(prime, -1, n)
        public = cosine_bounds(t, n)
        hidden = cosine_bounds(t*root, n)
        low, high = 2*(public[0]+hidden[0]), 2*(public[1]+hidden[1])
        z = (low+GRID//2)//GRID
        center = z*GRID
        margin = min(low-(center-GRID//2), center+GRID//2-high)
        if margin <= 0 or high-low >= SCALE >> 66:
            raise ArithmeticError("the full sample or its dyadic rounding is ambiguous")
        readings.append(str(z))
        min_margin = min(min_margin, margin)
        max_width = max(max_width, high-low)
        max_error = max(max_error, abs(low-center), abs(high-center))
    return dict(n=str(n), readings=readings), dict(
        scale_bits=128, max_enclosure_width_units=max_width,
        min_rounding_margin_units=min_margin, max_quantization_error_units=max_error)


def folded_phase(cosine):
    """Invert a scaled cosine on [0,1/2] turns using a 40-bit dyadic grid."""
    denominator = 1 << 40
    lo, hi = 0, denominator//2
    while hi-lo > 1:
        mid = (lo+hi)//2
        left, right = cosine_bounds(mid, denominator)
        if cosine < left:
            lo = mid
        elif right < cosine:
            hi = mid
        else:
            return Fraction(mid, denominator)
    return Fraction(lo+hi, 2*denominator)


def decode_readings(n, readings):
    """Replay the actual quantized full F words with only N and the public schedule."""
    primes = schedule(n)
    if len(readings) != len(primes):
        raise ValueError("expected one full Salié reading per scheduled prime")
    samples, bounds = [], []
    max_cosine_radius = 0
    for prime, word in zip(primes, readings):
        if not isinstance(word, (str, int)) or abs(int(word)) > 4 << FRACTION_BITS:
            raise ValueError("expected a signed integer encoding a full Salié reading")
        center = int(word)*GRID
        left, right = cosine_bounds(pow(prime, -1, n), n)
        low = max(-SCALE, (center-GRID//2)//2 - right)
        high = min(SCALE, (center+GRID//2)//2 - left)
        if low > high:
            raise ValueError("full reading is inconsistent with its public cosine")
        midpoint = (low+high)//2
        radius = high-midpoint
        if radius*64*prime*prime > SCALE:
            raise ValueError("readout uncertainty exceeds its required cosine accuracy")
        max_cosine_radius = max(max_cosine_radius, radius)
        bounds.append((low, high))
        samples.append((prime, folded_phase(midpoint)))

    result = decode_phases(n, samples)
    if result["factor"] is None:
        raise ValueError("no verified split from the supplied readings")
    b = result["multiplier"]
    for (prime, phase), (low, high) in zip(samples, bounds):
        span = b*prime
        j = round(span*phase)
        # Cosine decreases on this half-turn. The two tests certify j for
        # every hidden cosine consistent with the complete transmitted cell.
        if 2*j-1 >= 0 and cosine_bounds(2*j-1, 2*span)[0] <= high:
            raise ValueError("left phase-rounding boundary intersects observation")
        if 2*j+1 <= span and cosine_bounds(2*j+1, 2*span)[1] >= low:
            raise ValueError("right phase-rounding boundary intersects observation")
    return dict(**result, certified_phase_cells=len(primes),
                max_inferred_cosine_radius_units=max_cosine_radius)


def fixture():
    path = Path(__file__).resolve().parents[1] / "benchmarks" / "continued-square.json"
    case = next(c for c in json.loads(path.read_text()) if c["id"] == FIXTURE)
    p, q = map(int, case["factors"])
    if p*q != int(case["n"]):
        raise ValueError("fixture product mismatch")
    return p, q


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", action="store_true", help="emit synthetic observations as JSON")
    mode.add_argument("--decode", action="store_true", help="decode a JSON observation payload from stdin")
    args = parser.parse_args()
    if args.decode:
        payload = json.load(sys.stdin)
        output = decode_readings(int(payload["n"]), payload["readings"])
    else:
        p, q = fixture()
        payload, metrics = produce_readings(p, q)
        if args.emit:
            output = payload
        else:
            decoded = decode_readings(int(payload["n"]), payload["readings"])
            if decoded["factor"] != min(p, q):
                raise ArithmeticError("decoded split disagrees with the certified fixture")
            output = dict(fixture=FIXTURE, mode="synthetic_side_information",
                          certified_readings=len(payload["readings"]), **metrics, **decoded)
    print(json.dumps(output))
