"""Test the single factor remainder 1 at a dyadic radix chosen from the product's bit length."""

import argparse
from collections import Counter
import json
from math import isqrt

from .quartic_factor_lanes import pairs_in_windows


def search(n):
    if n < 3 or n % 2 == 0:
        raise ValueError('expected an odd integer >= 3')
    bits = n.bit_length()
    # In degree four the uniform strict LLL condition is R^20 > 5^5 * 2^10 * X^12.
    # Replace X² by 2^(bits+1), then choose the smallest sufficient power of two.
    rhs = 5**5 << (10+6*(bits+1))
    exponent = (rhs.bit_length()+19)//20
    radix = 1 << exponent
    bound = isqrt(2*n)
    lo = max(2, isqrt((n-1)//2)+1)
    work = Counter()
    pairs = pairs_in_windows(n, 1, n % radix, radix, bound, [(lo, bound)], work, 2)
    pairs = [[str(x), str(y)] for x, y in sorted(set(pairs))]
    # Burnside for u <-> N/u on the odd residues. At 2^e the fixed points
    # are the square roots of N; for e >= 3 there are zero or four of them.
    reduced = min(radix, 8)
    fixed = reduced//2 if n % reduced == 1 else 0
    total = (radix//2+fixed)//2
    return dict(n=str(n), power=2, unit_residue=True, coordinate_bound=bound,
                radix=radix, total_orbits=total, visited_orbits=1, remaining_orbits=total-1,
                work=dict(work), pairs=pairs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    args = parser.parse_args()
    print(json.dumps(search(args.n), indent=2))
