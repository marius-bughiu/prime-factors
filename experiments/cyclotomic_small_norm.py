"""Read a sum residue when N+5 is a square on the product class 4 modulo 5."""

from itertools import combinations
import json
from math import isqrt

from experiments.cyclotomic_sum_lift import _check_sum, _count, _positions
from scripts.factor import primes_through


def search(n, bits, max_tests):
    """Use N, the common factor width and a discriminant-test limit."""
    if bits < 2 or n % 2 == 0 or max_tests < 0:
        raise ValueError("expected an odd product, factor width >=2 and a nonnegative cap")
    lo, hi = 1 << (bits-1), (1 << bits)-1
    if not lo*lo <= n <= hi*hi:
        raise ValueError("product is outside the promised width")
    work = dict(square_probes=0, root=None, lower=None, upper=None, before=None,
                survivors=None, discriminant_tests=0, unvisited=None, hit_sum=None)
    if n % 5 != 4:
        return None, dict(work, outcome="outside_product_class")
    root = isqrt(n+5)
    work.update(square_probes=1, root=root)
    if root*root != n+5:
        return None, dict(work, outcome="no_square")
    # For x >= 6, (2x-1)^2 < 4N < (2x)^2, saving another root for the bound.
    lower = 2*root if root >= 6 else isqrt(4*n-1)+1
    upper = (hi*hi+n)//hi
    ordinary = _positions(lower, upper, (n+1)%4, 4)
    candidates = _positions(lower, upper, 5*((n+1)%4), 20)
    work.update(lower=lower, upper=upper, before=_count(ordinary),
                survivors=_count(candidates), unvisited=_count(candidates))
    for total in candidates[:max_tests]:
        work["discriminant_tests"] += 1
        work["unvisited"] -= 1
        factor = _check_sum(n, total)
        if factor is not None:
            return factor, dict(work, outcome="sum_square", hit_sum=total)
    return None, dict(work, outcome="test_cap" if work["unvisited"] else "exhausted")


def census():
    primes = [p for p in primes_through(511) if p >= 256]
    counts = dict(primes=len(primes), pairs=0, probes=0, square_witnesses=0, hits=[])
    for p, q in combinations(primes, 2):
        n = p*q
        factor, work = search(n, 9, 100)
        counts["pairs"] += 1
        counts["probes"] += work["square_probes"]
        counts["square_witnesses"] += work["survivors"] is not None
        if factor is not None:
            if factor != p or n//factor != q:
                raise ValueError("incorrect factorization on the census")
            counts["hits"].append(n)
    return counts


if __name__ == "__main__":
    print(json.dumps(census(), indent=2))
