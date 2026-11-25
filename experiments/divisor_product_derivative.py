"""Recover an equal-width factor pair from the second digits of two block products.

The product is over all odd b-bit candidate factors, with b inferred from N.
The caller supplies a hard cap on the number of candidates represented by each
product. Batching delegates to the repository's integer-index interpolation.
"""

import argparse
from collections import Counter
import json
from math import gcd, isqrt

from .factorial_progressions import block_products, decimal_convolution


def _setup(n, cap):
    if n < 5 or not n % 2 or cap < 0:
        raise ValueError("expected an odd integer >= 5 and a nonnegative candidate cap")
    bits = (n.bit_length() + 1) // 2
    half = 1 << (bits - 1)
    return half + 1, half // 2, min(half // 2, cap)


def _product(first, count, modulus, work):
    """Multiply count translated odd slots. A failed interpolation falls back directly."""
    if not count:
        return 1
    blocks, width, obstacle = block_products(first, count, 2, [0], modulus,
                                              decimal_convolution, work)
    represented = 0 if obstacle is not None else len(blocks) * width
    product = 1
    if obstacle is None:
        for block in blocks:
            product = product * block % modulus
        work["block_accumulations"] += len(blocks)
    else:
        work["direct_fallbacks"] += 1
    for index in range(represented, count):
        product = product * (first + 2 * index) % modulus
    work["tail_terms"] += count - represented
    return product


def search(n, max_candidates):
    """Return a divisor pair only after integer multiplication checks the split."""
    first, total, count = _setup(n, max_candidates)
    work = Counter()
    modulus = n * n
    initial = _product(first, count, modulus, work)
    common = gcd(initial, n)
    answer = dict(first=str(first), full_candidates=str(total), candidates=count,
                  remaining=str(total-count), modulus_bits=modulus.bit_length(),
                  product_gcd=str(common), digit0=None, digit1=None, factor_sum=None,
                  products=1, factor=None, work=work)
    if common == 1:
        return dict(answer, outcome="coprime_product")
    if common < n:
        return dict(answer, outcome="product_gcd", factor=common)
    shifted = _product(first+n, count, modulus, work)
    c0, c1 = initial//n, shifted//n
    answer.update(products=2, digit0=str(c0), digit1=str(c1))
    if shifted % n or gcd(c0, n) != 1:
        return dict(answer, outcome="noninvertible_digit")
    s = (c1*pow(c0, -1, n)-1) % n
    answer["factor_sum"] = str(s)
    delta = s*s - 4*n
    if delta >= 0:
        root = isqrt(delta)
        small, large = (s-root)//2, (s+root)//2
        if root*root == delta and small > 1 and small*large == n:
            return dict(answer, outcome="digit_sum", factor=small)
    return dict(answer, outcome="inconsistent_sum")


def compare(n, max_candidates):
    """Matched public band and cap, with a smaller-factor prefix as a separate baseline."""
    first, total, count = _setup(n, max_candidates)
    root_count = max(0, (isqrt(n)-first)//2+1)
    prefix_count = min(count, root_count)
    plain = {}
    for name, slots in (("whole_band", count), ("through_sqrt", prefix_count)):
        work = Counter()
        residue = _product(first, slots, n, work)
        plain[name] = dict(candidates=slots, gcd=str(gcd(residue, n)), work=work)
    found, divisions = None, 0
    for index in range(prefix_count):
        candidate = first + 2*index
        divisions += 1
        if n % candidate == 0:
            found = candidate
            break
    return dict(candidates_in_full_band=str(total), digit=search(n, max_candidates),
                trial=dict(divisions=divisions, factor=found), **plain)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--cap", required=True, type=int)
    parser.add_argument("--compare", action="store_true")
    args = parser.parse_args()
    print(json.dumps((compare if args.compare else search)(args.n, args.cap), indent=2))
