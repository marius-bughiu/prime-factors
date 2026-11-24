"""Look for a shared quaternion line in a bounded lexicographic enumeration."""
from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt


def triples(n):
    for a in range(isqrt(n)+1):
        for b in range(isqrt(n-a*a)+1):
            remaining = n-a*a-b*b
            for c in range(isqrt(remaining)+1):
                yield a, b, c, remaining-c*c


def rotate(quaternion, axis):
    # A cyclic permutation of the three imaginary units preserves products.
    return quaternion[:1]+quaternion[1+axis:]+quaternion[1:1+axis]


def chart_rows(chart, element, n):
    """Matrix in the split quaternion algebra defined by u²+v² = -1."""
    u, v = chart
    w, x, y, z = element
    return (((w+u*y-v*z) % n, (-x+v*y+u*z) % n),
            ((x+v*y+u*z) % n, (w-u*y+v*z) % n))


def search(n, max_triples):
    if n < 3 or n % 2 == 0 or max_triples < 0:
        raise ValueError("expected an odd product and a nonnegative triple budget")
    work = dict(outcome="budget", factor=None, triples=0, representations=0,
                chart_gcds=0, finite_labels=0, pair_gcds=0, labels=None)
    # The budget counts tested triples. This reference keeps its integer
    # enumeration and its list of scalar labels bounded separately by N.
    if n > 65535:
        return dict(work, outcome="size_limit")
    chart = None
    slopes = {}
    for a, b, c, remainder in triples(n):
        if work["triples"] == max_triples:
            return work
        work["triples"] += 1
        d = isqrt(remainder)
        if d*d != remainder:
            continue
        element = (a, b, c, d)
        work["representations"] += 1
        if chart is None:
            for axis, coordinate in enumerate(element[1:]):
                work["chart_gcds"] += 1
                common = gcd(a*a+coordinate*coordinate, n)
                if 1 < common < n:
                    return dict(work, outcome="chart_factor", factor=common)
                if common == 1:
                    a, b, c, d = rotate(element, axis)
                    inverse = pow(a*a+b*b, -1, n)
                    chart = ((a*c+b*d)*inverse % n, (a*d-b*c)*inverse % n)
                    break
            if chart is None:
                return dict(work, outcome="singular_seed")
            continue

        for u, v in chart_rows(chart, element, n):
            work["chart_gcds"] += 1
            common = gcd(u, n)
            if 1 < common < n:
                return dict(work, outcome="chart_factor", factor=common)
            if common == n:
                work["chart_gcds"] += 1
                common = gcd(v, n)
                if 1 < common < n:
                    return dict(work, outcome="chart_factor", factor=common)
                if common == 1:
                    break  # Both local lines are at infinity.
                continue
            slope = v*pow(u, -1, n) % n
            work["finite_labels"] += 1
            if slope in slopes:
                break
            for previous in slopes:
                work["pair_gcds"] += 1
                common = gcd(slope-previous, n)
                if 1 < common < n:
                    return dict(work, outcome="collision", factor=common, labels=[previous, slope])
            slopes[slope] = None
            break
    return dict(work, outcome="exhausted")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-triples", type=int, default=1000)
    args = parser.parse_args()
    print(dumps(search(args.n, args.max_triples)))
