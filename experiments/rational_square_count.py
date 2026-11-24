"""An integer lower bound on the number of smooth fractions that are squares."""

import argparse
from collections import Counter
from math import comb

from .smooth_sample_bound import SUBDIVISIONS, prime_bins


def counted_pairs(groups, bits, tuple_size):
    """Count ordered disjoint pairs with matching prime counts in every dyadic band."""
    if tuple_size <= 4 or bits < 0:
        raise ValueError('expected at least five disjoint entries and a nonnegative bit budget')
    counts = [1] + [0] * bits
    for weight, available in sorted(groups.items()):
        updated = counts.copy()
        for k in range(1, min(available // tuple_size, bits // weight) + 1):
            choices = comb(available, k) * comb(available-k, k)
            cost = weight*k
            for used in range(bits-cost+1):
                updated[used+cost] += choices * counts[used]
        counts = updated
    return sum(counts)


def bounded_groups(bins, base_bits, subdivisions):
    """Upper-round log2(p) to safe fractional-bit weights using the sieve bins."""
    groups = Counter()
    for left, size in bins:
        band = left.bit_length()-1
        step = max(1, (1 << band)//SUBDIVISIONS)
        largest = min((1 << base_bits), left+step-1)
        weight = (largest**subdivisions-1).bit_length()
        groups[weight] += size
    return groups


def overlap_lower(groups, bits):
    """Four times a lower bound for coprime ordered pairs with matching signs."""
    counts = [1] + [0]*bits
    for w, m in sorted(groups.items()):
        updated = counts.copy()
        for k in range(1, min(m, bits//w)+1):
            ways = comb(m, k)
            cost = k*w
            for j in range(bits-cost+1):
                updated[j+cost] += ways * counts[j]
        counts = updated
    total = sum(counts)
    overlapping = 0
    for w, m in groups.items():
        if w > bits:
            continue
        # Divide the truncated generating polynomial by (1 + t^w).
        without_one_prime = counts.copy()
        for degree in range(w, bits+1):
            without_one_prime[degree] -= without_one_prime[degree-w]
        containing_one_prime = sum(without_one_prime[:bits-w+1])
        overlapping += m * containing_one_prime**2
    return max(0, total**2-4*overlapping)


def matching_lower(pairs, tuple_size):
    """Balanced four-colour classes minimize the number of agreeing ordered positions."""
    floor, extra = divmod(tuple_size, 4)
    agreeing = (4-extra)*floor*(floor-1) + extra*(floor+1)*floor
    total = tuple_size*(tuple_size-1)
    return (pairs*agreeing + total-1)//total


def certificate(base_bits, bits=1023, tuple_size=12):
    bins = prime_bins(base_bits)
    groups = bounded_groups(bins, base_bits, 1)
    pairs = counted_pairs(groups, bits, tuple_size)
    root_count = 4*matching_lower(pairs, tuple_size)
    # Omitting the smallest primes reduces the number of pairs sharing a factor.
    quarter_groups = bounded_groups(bins, base_bits, 4)
    restricted = {w:m for w,m in quarter_groups.items() if w > 4*4}
    return root_count, overlap_lower(restricted, 4*bits)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-bits', type=int, choices=(16, 24, 32), nargs='+', default=[16, 24, 32])
    args = parser.parse_args()
    for b in args.base_bits:
        clique, coprime = certificate(b)
        counts = (clique.bit_length()-1, coprime.bit_length()-1 if coprime else None)
        print(f'B=2^{b}: unit roots by disjoint tuples / coprime pairs = {counts} '
              f'(lower exponents in base two)', flush=True)
