"""Sweep paired reciprocal brackets using only a balanced product and a public wheel."""
from argparse import ArgumentParser
from math import gcd, isqrt
import json


def farey_brackets(depth):
    """Uniformly bisect [1,2) by the mediant, with ties in the right bracket."""
    if depth < 0:
        raise ValueError("expected nonnegative depth")
    edges = [(1, 1), (2, 1)]
    for _ in range(depth):
        refined = []
        for (a, b), (c, d) in zip(edges, edges[1:]):
            refined.extend([(a, b), (a + c, b + d)])
        edges = [*refined, edges[-1]]
    return list(zip(edges, edges[1:]))


def projections(n, scale, brackets):
    """Pull back M/p (decreasing) and Mp/N (increasing) to integer p."""
    lo, hi = max(scale // 2 + 1, n // scale + 1), isqrt(n)
    first, second = [], []
    for (a, b), (c, d) in reversed(brackets):
        left, right = max(lo, scale * d // c + 1), min(hi, scale * b // a)
        if left <= right:
            first.append((left, right))
    for (a, b), (c, d) in brackets:
        left, right = max(lo, (a * n - 1) // (scale * b) + 1), min(hi, (c * n - 1) // (scale * d))
        if left <= right:
            second.append((left, right))
    return first, second


def sweep(first, second):
    i = j = compared = 0
    ranges = []
    while i < len(first) and j < len(second):
        lo, hi = first[i]
        left, right = second[j]
        compared += 1
        if max(lo, left) <= min(hi, right):
            ranges.append((max(lo, left), min(hi, right)))
        if hi <= right:
            i += 1
        if right <= hi:
            j += 1
    return ranges, compared


def measure(n, depth=8, modulus=24):
    """Count all candidates even when their number is too large to enumerate."""
    if n < 2 or modulus < 1 or gcd(modulus, n) != 1:
        raise ValueError("expected a positive wheel coprime to the input")
    scale = 1 << ((n.bit_length() + 1) // 2)
    brackets = farey_brackets(depth)
    first, second = projections(n, scale, brackets)
    ranges, comparisons = sweep(first, second)
    units = [(a, n * pow(a, -1, modulus) % modulus) for a in range(modulus) if gcd(a, modulus) == 1]
    candidates = inspected = eliminated = largest = 0
    exact = []
    for lo, hi in ranges:
        for a, b in units:
            x = lo + (a - lo) % modulus
            z = hi - (hi - a) % modulus
            if x > z:
                continue
            count = (z - x) // modulus + 1
            candidates += count
            inspected += 1
            low_y = (n + z - 1) // z
            partner = low_y + (b - low_y) % modulus
            if partner > n // x:
                if count != 1:
                    raise AssertionError("a rejection covered two positions on one lane")
                eliminated += count
            elif x == z:
                exact.append(x)
        largest = max(largest, hi - lo + 1)
    return dict(depth=depth, bracket_pairs=len(brackets)**2, nonempty_first=len(first),
                nonempty_second=len(second), sweep_comparisons=comparisons,
                occupied_pairs=len(ranges), largest_interval=largest,
                candidates=candidates, inspected_lanes=inspected, eliminated=eliminated,
                remaining=candidates-eliminated, exact_singletons=exact)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--depth', type=int, default=8)
    parser.add_argument('--modulus', type=int, default=24)
    args = parser.parse_args()
    print(json.dumps(measure(args.n, args.depth, args.modulus), indent=2))


if __name__ == '__main__':
    main()
