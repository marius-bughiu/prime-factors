"""Batch three exact prime representations using one polynomial on odd coordinates."""
import argparse
import json
from math import gcd, isqrt

from .mixed_ratio_heights import jacobi
from .universal_norm_batch import ceil_sqrt, modular_product
from .wide_modulus import product_tree, values_at


def coordinate_ranges(lower, upper, side, forms, smaller):
    """Return the positive denominator progressions (first, last, stride) inclusive."""
    tmax = side if side % 2 else max(0, side - 1)
    limits = []
    for form in forms:
        if form < 0:
            a = -form
            low = ceil_sqrt(max(0, (lower - tmax * tmax + a - 1) // a))
            high = isqrt(max(0, (upper - 1) // a))
        else:
            low = ceil_sqrt((lower + 2) // 2)
            high = isqrt((upper + tmax * tmax) // 2)
        first, last = max(1, low), min(side, high)
        # Gaussian primes allow an odd first coordinate and an even second.
        # In the three-form cover the two other forms cover residues 3 and 7 mod 8.
        stride = 2 if form == -1 or smaller else 1
        if stride == 2:
            parity = int(form == -2)
            first += (parity - first) % 2
        limits.append((form, first, last, stride))
    return limits


def count_progression(first, last, stride):
    """Exact even for lengths exceeding the machine range of len(range(...))."""
    return max(0, 1 + (last - first) // stride)


def plan(n, max_side, *, balanced=False):
    if n < 3 or n % 2 == 0 or max_side < 0:
        raise ValueError("expected an odd input >=3 and a nonnegative side cap")
    lower = max(3, ceil_sqrt((n + 1) // 2)) if balanced else 3
    options = [(True, isqrt(n), (-1, -2, 2))]
    if balanced:
        options.extend((False, isqrt(2*n), (d,)) for d in (-1, -2, 2) if jacobi(d, n) == -1)
    def cost(option):
        smaller, upper, forms = option
        target = isqrt(upper)
        ranges = coordinate_ranges(lower, upper, target, forms, smaller)
        columns = sum(count_progression(a, b, s) for _, a, b, s in ranges)
        return target > max_side, (target + 1) // 2 + columns
    smaller, upper, forms = min(options, key=cost)
    target = isqrt(upper)
    side = min(max_side, target)
    ranges = coordinate_ranges(lower, upper, side, forms, smaller)
    return lower, upper, target, side, ranges


def search(n, max_side, *, balanced=False):
    """The optional promise is two distinct odd primes p<q<=2p."""
    lower, upper, target, side, ranges = plan(n, max_side, balanced=balanced)
    counts = [count_progression(a, b, s) for _, a, b, s in ranges]
    work = dict(factor=None, outcome="no_split" if side == target else "side_limit",
                factor_lower=str(lower), factor_upper=str(upper), target_side=str(target),
                side=str(side), discriminants=[d for d, *_ in ranges], degree=0,
                planned_evaluations=sum(counts), evaluations=0, forms_tested=0, pair_values_covered=0,
                batch_gcds=0, whole_modulus_batches=0, row_gcds=0, leaf_gcds=0, witness=[])
    if not any(counts) or not side:
        return work
    roots = [u*u % n for u in range(1, side+1, 2)]
    polynomial = product_tree(roots, n)[-1][0]
    work["degree"] = len(roots)
    for (d, first, last, stride), count in zip(ranges, counts):
        if not count:
            continue
        coordinates = range(first, last+1, stride)
        values = values_at(polynomial, [d*v*v % n for v in coordinates], n)
        work["forms_tested"] += 1
        work["evaluations"] += count
        work["pair_values_covered"] += count * len(roots)
        work["batch_gcds"] += 1
        aggregate = gcd(modular_product(values, n), n)
        if aggregate == 1:
            continue
        work["whole_modulus_batches"] += int(aggregate == n)
        for v, value in zip(coordinates, values):
            work["row_gcds"] += 1
            if gcd(value, n) == 1:
                continue
            for u in range(1, side+1, 2):
                leaf = u*u-d*v*v
                work["leaf_gcds"] += 1
                factor = gcd(leaf, n)
                if 1 < factor < n:
                    return dict(work, factor=factor, outcome="norm_divisor",
                                witness=[d, str(u), str(v), str(leaf)])
    return work


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-side", type=int, default=128)
    parser.add_argument("--balanced", action="store_true")
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_side, balanced=args.balanced)))
