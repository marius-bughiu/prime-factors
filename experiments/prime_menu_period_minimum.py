"""Exhaust the prime menus whose joint period fits one fixed toy window.

Replay with `python3 -m experiments.prime_menu_period_minimum`. The certificate
counts guaranteed survivors in any translated midpoint interval of length 2^21.
The two example midpoints illustrate which local tests accept a candidate.
"""

import json
from collections import Counter
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.local_midpoint_lanes import is_prime
from scripts.factor import discover


WIDTH = 2**21
BASE_PERIOD = 128 * 27
PRODUCT = 16637


def menu_census():
    # Removing the compulsory 5 leaves a product budget of 121. Even the
    # smallest three optional primes already exceed it.
    budget = WIDTH // (BASE_PERIOD * 5)
    optional = [p for p in range(7, budget + 1) if is_prime(p)]
    rows = []
    for count in range(len(optional) + 1):
        if prod(optional[:count]) > budget:
            break
        for extra in combinations(optional, count):
            if prod(extra) > budget:
                continue
            regular = (5, *extra)
            period = BASE_PERIOD * prod(regular)
            lanes = 8 * prod((p - 3) // 2 for p in regular)
            periods = WIDTH // period
            rows.append({"regular_primes": regular, "period": period, "lanes": lanes,
                         "complete_periods": periods, "certificate": periods * lanes})

    # Independent coverage check by squarefree auxiliary product, including 1.
    admissible_products = {m for m in range(1, budget + 1)
                           if gcd(m, 30) == 1 and all(m % (p*p) for p in optional if p*p <= m)}
    enumerated_products = {prod(r["regular_primes"]) // 5 for r in rows}
    assert enumerated_products == admissible_products and len(rows) == len(admissible_products)
    return sorted(rows, key=lambda r: (r["certificate"], r["regular_primes"]))


def local_receipt(d, p):
    """Strip an even valuation and test the unit modulo 8 or the odd prime.

    Every displayed odd-prime unit root lifts by Hensel's lemma. At 2 the
    odd unit must be 1 modulo 8. A failed unit test gives a finite obstruction.
    """
    assert d > 0
    v, unit = 0, d
    while unit % p == 0:
        v += 1
        unit //= p
    modulus = 8 if p == 2 else p
    root = next((x for x in range(1, modulus) if x*x % modulus == unit % modulus), None)
    passed = v % 2 == 0 and root is not None
    result = {"prime": p, "valuation": v, "unit_modulus": modulus,
              "unit_residue": unit % modulus, "unit_root": root, "all_powers": passed}
    if not passed:
        obstruction = p**(v + 1) if v % 2 else p**v * modulus
        assert all((x*x - d) % obstruction for x in range(obstruction))
        result["rejecting_modulus"] = obstruction
    return result


def example():
    rows = menu_census()
    minimum = rows[0]["certificate"]
    minimizers = [row for row in rows if row["certificate"] == minimum]
    by_size = Counter(len(row["regular_primes"]) for row in rows)
    assert minimum == 64 and [r["regular_primes"] for r in minimizers] == [(5, 7, 11)]
    assert by_size == {1: 1, 2: 27, 3: 3}
    same_size = [row for row in rows if len(row["regular_primes"]) == 3]
    smaller_menu_minimum = min(row["certificate"] for row in rows if len(row["regular_primes"]) < 3)
    fewer_minimizers = [row for row in rows if len(row["regular_primes"]) < 3
                        and row["certificate"] == smaller_menu_minimum]
    assert [row["certificate"] for row in same_size] == [64, 80, 112]
    assert [(r["regular_primes"], r["certificate"]) for r in fewer_minimizers] == [((5, 61), 232)]

    # The normal bounded factor check is independent of both the menu census
    # and the two post-hit witnesses. Expected factors are used only here.
    factors, unresolved, used = discover(PRODUCT, 1, [])
    assert list(map(str, factors)) == ["127", "131"] and not unresolved and used == 1
    assert prod(factors) == PRODUCT and all(is_prime(p) for p in factors)
    assert all(gcd(PRODUCT, row["period"]) == 1 for row in rows)
    true_midpoint = sum(factors) // 2
    witnesses = []
    for h, accept, reject in [(399, 11, 13), (1089, 13, 11)]:
        d = h*h - PRODUCT
        assert h > true_midpoint and isqrt(d)**2 < d
        receipts = [local_receipt(d, p) for p in [2, 3, 5, 7, 11, 13]]
        assert [r["prime"] for r in receipts if not r["all_powers"]] == [reject]
        witnesses.append({"midpoint": h, "discriminant": d, "sqrt_floor": isqrt(d),
                          "passing_regular_menu": [5, 7, accept], "receipts": receipts})
    return {"window_length": WIDTH, "compulsory_primes": [2, 3, 5],
            "max_product_of_optional_primes": WIDTH // (BASE_PERIOD * 5), "menus_tested": len(rows),
            "counts_by_regular_menu_size": dict(sorted(by_size.items())), "minimizers": minimizers,
            "largest_size_comparison": same_size, "best_fewer_prime_menus": fewer_minimizers,
            "product": str(PRODUCT), "factors": list(map(str, factors)), "max_midpoints": 1,
            "midpoints_used": used, "unresolved": unresolved, "true_midpoint": true_midpoint,
            "post_hit_witnesses": witnesses}


if __name__ == "__main__":
    print(json.dumps(example(), indent=2))
