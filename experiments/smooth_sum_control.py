"""Reconstruct the planted 2,048-bit sum and optionally repeat its bounded selection."""

import argparse
import json
from math import gcd, prod
from pathlib import Path

from scripts.factor import prime_witness, primes_through


def planted_sum():
    unit = 2**1024
    for exponent in range(300, 647):
        odd = 3**exponent
        if odd.bit_length() > 1024:
            break
        total = odd << (1025 - odd.bit_length())
        if 8*unit <= 5*total < 9*unit and gcd(total-1, 5*7*11) == 1:
            return total
    raise ValueError("no sum in the specified band")


def candidate(total, power_of_three, power_of_eleven, power_of_seven):
    minimum = 2**512
    left_order = 3**power_of_three
    left_order <<= 513 - left_order.bit_length()
    right_order = 11**power_of_eleven * 7**power_of_seven
    if right_order >= minimum:
        return None
    while right_order < minimum:
        right_order *= 5

    first = 1 + left_order * ((total-2) * pow(left_order, -1, right_order) % right_order)
    return first, total-first


def select():
    total, unit = planted_sum(), 2**1024
    trial_product = prod(primes_through(1000))
    for j in range(1, 324):
        for ell in range(1, 148):
            for k in range(1, 183):
                pair = candidate(total, j, ell, k)
                if pair is None:
                    break
                p, q = pair
                if not (unit//2 <= p < q < unit and p*q >= unit**2//2 and q-p >= unit//16):
                    continue
                if gcd(p*q, trial_product) == 1 and prime_witness(p) and prime_witness(q):
                    return (j, ell, k), pair
    raise ValueError("no certified pair in the specified ranges")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-search', action='store_true',
                        help='repeat the full construction search before comparing the fixture')
    options = parser.parse_args()
    parameters = (179, 27, 102)
    pair = candidate(planted_sum(), *parameters)
    if options.replay_search and select() != (parameters, pair):
        raise ValueError("the first selected pair changed")
    p, q = pair
    fixture = Path(__file__).resolve().parents[1] / 'benchmarks/two-three-sum.json'
    row = next(row for row in json.loads(fixture.read_text()) if row['id'] == 'two-three-sum-constructed-2048')
    if [str(p), str(q)] != row['factors'] or str(p*q) != row['n']:
        raise ValueError("fixture differs from the construction")
    if not prime_witness(p) or not prime_witness(q):
        raise ValueError("unable to generate both primality witnesses")
    print("Reconstructed both 1,024-bit primes, their 2,048-bit product and both order witnesses.")


if __name__ == '__main__':
    main()
