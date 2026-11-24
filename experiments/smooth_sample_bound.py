"""Certify upper bounds for smooth centered residues of uniform unit squares.

Run without arguments for all three factor bases, or pass --base-bits 16.
Integer arithmetic certifies the bounds; floats only propose an exponent
and an initial guess for an integer root that is checked independently.
"""

import argparse
from fractions import Fraction
from math import expm1, isqrt, log, log2


SCALE = 1 << 48
DENOMINATOR = 256
SUBDIVISIONS = 256


def ceil_div(a, b):
    return -(-a // b)


def prime_bins(base_bits):
    """Count primes in [left, right) by sieving only odds in small segments."""
    limit = 1 << base_bits
    small = bytearray([1]) * (isqrt(limit) + 1)
    small[:2] = b"\x00\x00"
    for p in range(2, isqrt(len(small) - 1) + 1):
        if small[p]:
            small[p * p :: p] = bytes((len(small) - 1 - p * p) // p + 1)
    primes = [p for p in range(3, len(small), 2) if small[p]]
    endpoints = sorted({
        (1 << j) + ((1 << j) * i // SUBDIVISIONS)
        for j in range(1, base_bits) for i in range(SUBDIVISIONS)
    } | {limit + 1})
    bins = []
    for left, right in zip(endpoints, endpoints[1:]):
        count = int(left <= 2 < right)
        start = left | 1
        while start < right:
            stop = min(start + 2 * (1 << 19), right)
            size = (stop - start + 1) // 2
            marks = bytearray([1]) * size
            for p in primes:
                if p * p >= stop:
                    break
                first = max(p * p, ceil_div(start, p) * p)
                if first % 2 == 0:
                    first += p
                index = (first - start) // 2
                if index < size:
                    marks[index::p] = bytes((size - 1 - index) // p + 1)
            count += marks.count(1)
            start += 2 * size
        if count:
            bins.append((left, count))
    return bins


def log_euler_upper(prime_lower, numerator):
    """An integer >= SCALE * -ln(1 - prime_lower**(-numerator/256))."""
    exponent = Fraction(numerator, DENOMINATOR)
    a, d = exponent.numerator, exponent.denominator
    target = SCALE ** d
    factor = prime_lower ** a
    q = int(SCALE * prime_lower ** -float(exponent)) + 1
    while q ** d * factor < target:
        q += 1
    assert 0 < q < SCALE
    power, total = SCALE, 0
    for k in range(1, 17):
        power = ceil_div(power * q, SCALE)
        total += ceil_div(power, k)
    return total + ceil_div(power * q, 17 * (SCALE - q))


def exponent_for(bins, width):
    """Use the derivative of the binned log product to propose a Rankin exponent."""
    terms = [(log(p), n * log2(p)) for p, n in bins]
    lo, hi = 1, DENOMINATOR - 1
    while lo < hi:
        mid = (lo + hi) // 2
        loss = sum(nbits / expm1(mid * ln_p / DENOMINATOR) for ln_p, nbits in terms)
        if loss > width:
            lo = mid + 1
        else:
            hi = mid
    return {max(1, lo - 1), lo}


def certified_bound(bins, width):
    """Return a rational upper bound on log2 Psi(2**width, B) and the exponent numerator."""
    # ln 2 = 2 atanh(1/3); the first eight positive terms are a lower bound.
    ln2_lower = sum(Fraction(2, j * 3 ** j) for j in range(1, 16, 2))
    candidates = []
    for a in exponent_for(bins, width):
        euler = sum(n * log_euler_upper(p, a) for p, n in bins)
        bits = Fraction(width * a, DENOMINATOR) + Fraction(euler, SCALE) / ln2_lower
        candidates.append((bits, a))
    return min(candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-bits", type=int, choices=(16, 24, 32),
                        nargs="+", default=[16, 24, 32])
    args = parser.parse_args()
    for b in sorted(set(args.base_bits)):
        bins = prime_bins(b)
        prime_count = sum(n for _, n in bins)
        print(f"B=2^{b} primes={prime_count}", flush=True)
        for label, width in (("centered", 2046), ("window", 1024), ("max", 2047)):
            count_bits, a = certified_bound(bins, width)
            psi = ceil_div(count_bits.numerator, count_bits.denominator)
            probability_bits = count_bits + 3 - 2047 + Fraction(1, 1024)
            saving = (-probability_bits) // 1
            fields = (f"one <= 2^-{saving}  2^48 draws <= 2^-{saving - 48}"
                      if label != "max" else "")
            print(f"  {label}: sigma={a}/{DENOMINATOR}  "
                  f"Psi(2^{width}, B) <= 2^{psi}  {fields}", flush=True)


if __name__ == "__main__":
    main()
