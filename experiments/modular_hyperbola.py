"""Report modular hyperbola points in a balanced rectangle using affine high digits.

The input must be odd. Every integer factor pair 1 < x <= y <= 2*x is found.
The complete run reports work even after an exact pair is found. Supply a small
decimal product to reproduce it, for example 1900014700027. The number of low
residue classes grows exponentially with the binary input length.
"""

import argparse
import json
from dataclasses import asdict, dataclass
from math import isqrt
from statistics import median
from time import perf_counter


@dataclass
class Work:
    low_classes: int = 0
    range_counts: int = 0
    euclidean_steps: int = 0
    modular_hits: int = 0


def floor_sum(length, modulus, slope, intercept, work):
    """Sum floor((slope*i + intercept)/modulus) for 0 <= i < length."""
    total, sign = 0, 1
    while length:
        work.euclidean_steps += 1
        qa, slope = divmod(slope, modulus)
        qb, intercept = divmod(intercept, modulus)
        total += sign * (qa * (length * (length - 1) // 2) + qb * length)
        height = (slope * (length - 1) + intercept) // modulus
        if height == 0:
            break
        # Above level j, indices start at ceil((modulus*j-intercept)/slope).
        total += sign * length * height
        length, modulus, slope, intercept = height, slope, modulus, modulus - intercept + slope - 1
        sign = -sign
    return total


def high_interval(low, high, digit, radix):
    """High digits v for which low <= digit + radix*v < high."""
    return (low - digit + radix - 1) // radix, (high - digit + radix - 1) // radix


def report_progression(slope, intercept, radix, first, stop, low, high, work):
    """Report (v,z) in the rectangle with z=(slope*v+intercept) mod radix."""
    def count(a, b):
        work.range_counts += 1
        initial = intercept + slope * a + radix
        return (floor_sum(b - a, radix, slope, initial - low, work)
                - floor_sum(b - a, radix, slope, initial - high, work))

    if first >= stop or low >= high:
        return
    pending = [(first, stop, count(first, stop))]
    while pending:
        a, b, hits = pending.pop()
        if hits == 0:
            continue
        if hits == b - a:
            for v in range(a, b):
                yield v, (slope * v + intercept) % radix
            continue
        mid = (a + b) // 2
        left_hits = count(a, mid)
        pending.extend([(mid, b, hits - left_hits), (a, mid, left_hits)])


def search(n, radix_bits=None):
    if n < 3 or n % 2 == 0:
        raise ValueError("expected an odd product of at least 3")
    xmin, xmax = max(2, isqrt((n - 1) // 2) + 1), isqrt(n) + 1
    ymin, ymax = isqrt(n - 1) + 1, isqrt(2 * n) + 1
    width = (ymax - 1).bit_length()
    if radix_bits is None:
        radix_bits = (2 * width + 2) // 3
    if not (width + 1) // 2 <= radix_bits <= width:
        raise ValueError("radix_bits must be between ceil(width/2) and width")
    radix = 1 << radix_bits
    pairs = []
    work = Work()
    for u in range(1, radix, 2):
        work.low_classes += 1
        first, stop = high_interval(xmin, xmax, u, radix)
        if first >= stop:
            continue
        inverse = pow(u, -1, radix)
        w = n * inverse % radix
        low, high = high_interval(ymin, ymax, w, radix)
        carry = (n - u * w) // radix
        slope, intercept = -w * inverse % radix, carry * inverse % radix
        for v, z in report_progression(slope, intercept, radix, first, stop, low, high, work):
            work.modular_hits += 1
            x, y = u + radix * v, w + radix * z
            if x * y == n:
                pairs.append([str(x), str(y)])
    trial_odds = xmax // 2 - xmin // 2
    return dict(n=str(n), width=width, radix_bits=radix_bits, pairs=pairs,
                odd_trial_candidates=trial_odds, **asdict(work))


def compare_trial(n, radix_bits, repeats):
    """Compare two complete searches of the same interval, including work after a hit."""
    if repeats <= 0:
        raise ValueError("the timing comparison needs at least one repetition")
    affine_times, trial_times = [], []
    for _ in range(repeats):
        start = perf_counter()
        record = search(n, radix_bits)
        affine_times.append(perf_counter() - start)
        start = perf_counter()
        first = max(2, isqrt((n - 1) // 2) + 1) | 1
        trial = [(x, n // x) for x in range(first, isqrt(n) + 1, 2) if n % x == 0]
        trial_times.append(perf_counter() - start)
        if sorted((int(x), int(y)) for x, y in record["pairs"]) != trial:
            raise AssertionError("affine and trial searches returned different pairs")
    record.update(repetitions=repeats, affine_median_seconds=median(affine_times),
                  trial_median_seconds=median(trial_times))
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--radix-bits", type=int)
    parser.add_argument("--compare-trial", type=int, metavar="REPEATS",
                        help="time repeated complete searches with both algorithms")
    args = parser.parse_args()
    result = (search(args.n, args.radix_bits) if args.compare_trial is None
              else compare_trial(args.n, args.radix_bits, args.compare_trial))
    print(json.dumps(result))
