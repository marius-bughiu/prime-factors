"""An early false square test on one fixed 28-bit teaching product.

Replay with python3 -m experiments.early_persistent_score_example. The score
order and the prime-power tests use only the product and its public width.
"""

import json
from math import gcd, isqrt, prod

from experiments.local_midpoint_lanes import is_prime, midpoint_lanes, stable_exponent
from experiments.stream_sum_scores import ROWS, bounds, search


def example():
    n = 145684811
    bits = n.bit_length() // 2
    low, high = bounds(n, bits)
    menu = sorted(
        (scale * (s * s - 4 * n), s)
        for residue, scale in ROWS[n % 100]
        for s in range(low + (residue - low) % 100, high + 1, 100)
    )
    factors, work = search(n, bits, weighted=True)
    true_sum = sum(factors)
    prefix = menu[:work.square_tests]
    assert factors == (8999, 16189) and prefix[-1][1] == true_sum

    # A discriminant d=(s/2)²-n and its square multiple 4d are squares at
    # every depth simultaneously or neither is. Work with the smaller d.
    bound = (high // 2) ** 2 - n
    primes = [p for p in range(2, 30) if is_prime(p)]
    survivors = [s for _, s in prefix]
    counts = []
    for p in primes:
        exponent = stable_exponent(p, bound)
        lanes = midpoint_lanes(n, p, exponent)
        survivors = [s for s in survivors if any(
            (s // 2) % lane.modulus == lane.residue for lane in lanes
        )]
        counts.append(len(survivors))
    assert survivors == [24180, true_sum]

    false_sum = survivors[0]
    false_rank = next(i for i, (_, s) in enumerate(prefix, 1) if s == false_sum)
    d = (false_sum // 2) ** 2 - n
    assert 695**2 < d == 483289 < 696**2
    assert gcd(d, prod(primes)) == 1 and d % 8 == 1
    # At odd p the displayed root is a unit, so Hensel lifting supplies a
    # square root at every exponent. At 2, the unit condition is d ≡ 1 mod 8.
    moduli = [8, *primes[1:]]
    roots = [next(x for x in range(m) if (x * x - d) % m == 0) for m in moduli]
    assert d % 31 == 30 and all(x * x % 31 != 30 for x in range(31))
    offset = false_sum // 2 - (isqrt(n) + 1)
    assert 0 <= offset < 2**6 and 2**10 <= true_sum - low
    assert 25 * (false_sum - low + 1) <= 4 * (true_sum - low)
    return {
        "n": str(n), "bounds": [low, high], "menu_count": len(menu),
        "false_sum": false_sum, "false_rank": false_rank,
        "false_score": prefix[false_rank - 1][0], "midpoint_offset": offset,
        "midpoint_discriminant": d, "roots_by_modulus": list(zip(moduli, roots)),
        "first_rejecting_prime": 31, "true_sum": true_sum,
        "true_rank": work.square_tests, "true_score": prefix[-1][0],
        "prefix_survivors_by_prime": list(zip(primes, counts)),
        "surviving_sums_in_order": survivors,
    }


if __name__ == "__main__":
    print(json.dumps(example()))
