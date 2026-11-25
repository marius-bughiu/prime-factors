"""Run the rounded degree-six wheel comparison at the public lower quartile."""

import argparse
import json

from .binomial_divisor_window import search as binomial_search
from .quartic_divisor_window import odd_quartile_center


def search(n, first, span, *, depth=3, modulus_limit=97):
    return binomial_search(n, first, span, degree=6, depth=depth, modulus_limit=modulus_limit,
                           centered=True, rounded=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('radius', type=int)
    parser.add_argument('--depth', default=3, type=int)
    parser.add_argument('--modulus-limit', default=97, type=int)
    args = parser.parse_args()
    center = odd_quartile_center(args.n)
    print(json.dumps(search(args.n, center - 2 * args.radius, 2 * args.radius,
                            depth=args.depth, modulus_limit=args.modulus_limit), indent=2))
