"""Bounded first-vector sieve for a balanced product N=pq with p<q<=2p.

All interval anchors, lattice vectors, exceptional budgets and powers come from
N and the public search parameters. The local digit and its translated
quadratic images follow Stănică, https://arxiv.org/html/2611.06580v1#S3.
This direct reference exhausts explicit baby/giant gcd comparisons, including
every repeated power. It uses neither fast multipoint evaluation nor an order
certificate. Reported counts describe these loops.

For a mixed-branch control use 5459 --m 15 --m0 3 --selected 3 5 --compare
--exceptional. For an ordinary exact collision with one tolerated degenerate
prime use 22261 --m 105 --m0 4 --selected 3 5 7 --max-bad 1 --compare.
"""

import argparse
import json
from collections import Counter
from dataclasses import asdict, dataclass
from math import gcd, isqrt, prod

if __package__:
    from .exceptional_weights import search_product, squarefree_primes
else:
    from exceptional_weights import search_product, squarefree_primes


def ceil_ratio(a, b):
    return -(-a // b)


def first_vector(n, m, m0, sigma, anchor, work):
    """Return the coefficients of a shortest vector for the transformed norm."""
    eta = n * pow(sigma, -2, m) % m
    work["lattice_residue_inverses"] += 1

    def transform(pair):
        a, b = pair
        return n*a, m0*(anchor*anchor*b-n*a)

    left, right = (1, eta), (0, m)
    while True:
        x, y = transform(left)
        z, w = transform(right)
        norm = x*x+y*y
        work["gauss_iterations"] += 1
        if norm > z*z+w*w:
            left, right = right, left
            continue
        nearest = (2*(x*z+y*w)+norm) // (2*norm)
        if nearest == 0:
            a, b = left
            return (-a, -b) if a < 0 or (a == 0 and b < 0) else (a, b)
        right = (right[0]-nearest*left[0], right[1]-nearest*left[1])


@dataclass(frozen=True)
class Giant:
    sigma: int
    anchor: int
    upper: int
    a: int
    b: int
    d: int
    bad: int
    offset: int
    shift: int


def make_giant(n, m, m0, selected, squares, radius, sigma, anchor, upper, work):
    a, b = first_vector(n, m, m0, sigma, anchor, work)
    step = m*m
    tau = (a*n*pow(sigma, -1, step)+b*sigma) % step
    work["trace_residue_inverses"] += 1
    center = (a*n+b*anchor*anchor) // (step*anchor)
    offset = step*(center-radius)+tau
    const = (a*n+b*sigma*sigma-tau*sigma) // step
    linear = (b*sigma*sigma-a*n) // m
    shift, period, bad = 0, 1, 0
    for ell in selected:
        work["local_shift_components"] += 1
        if a % ell == 0:
            local = 0
            bad += 1
        else:
            inv = pow(sigma, -1, ell)
            quadratic = a*n*inv**3 % ell
            vertex = (const*inv-center+radius
                      - (linear*inv**2)**2 * pow(4*quadratic, -1, ell)) % ell
            work["local_digit_inverses"] += 2
            local = (int(quadratic not in squares[ell])-vertex) % ell
        shift += period*((local-shift)*pow(period, -1, ell) % ell)
        work["translation_crt_inverses"] += 1
        period *= ell
    return Giant(sigma, anchor, upper, a, b, gcd(gcd(a, b), m), bad, offset, shift)


def setup(n, m, m0, selected, max_bad):
    if n < 5 or m < 1 or m0 < 1 or gcd(n, m) != 1:
        raise ValueError("need N>=5, a positive squarefree m coprime to N, and m0>=1")
    work = Counter()
    primes = squarefree_primes(m, work)
    if len(set(selected)) != len(selected) or any(l == 2 or l not in primes for l in selected):
        raise ValueError("selected entries must be distinct odd prime divisors of m")
    if not 0 <= max_bad <= len(selected):
        raise ValueError("invalid allowance for degenerate selected primes")
    squares = {l: {x*x % l for x in range(l)} for l in selected}
    forbidden = {l: {r for r in range(l) if r not in squares[l] and (r-1) % l in squares[l]
                      and (r-1) % l != 0} for l in selected}
    period = prod(selected)
    residues = [r for r in range(period)
                if sum(r % l in forbidden[l] for l in selected) <= max_bad]
    work.update(local_square_table_entries=sum(selected), local_forbidden_table_entries=sum(selected),
                crt_residues_tested=period, crt_membership_checks=period*len(selected))
    # Lemma 3.3 and two-dimensional Gauss reduction bound the error in
    # units of m² by 2 sqrt(N/(m*m0)^3). One more unit covers rounding.
    radius = isqrt((4*n-1)//(m*m0)**3)+2
    low = isqrt((n-1)//2)+1
    high = isqrt(n)
    units = [s for s in range(1, m+1) if gcd(s, m) == 1]
    work["residue_unit_gcds"] = m
    giants = []
    while low <= high:
        following = ceil_ratio(low*(m0+1), m0)
        work["anchors"] += 1
        for sigma in units:
            giants.append(make_giant(n, m, m0, selected, squares, radius, sigma, low,
                                     min(high, following-1), work))
        low = following
    return giants, radius, period, residues, work


def recover_trace(n, a, b, trace):
    disc = trace*trace-4*a*b*n
    if disc < 0:
        return None
    root = isqrt(disc)
    if root*root != disc:
        return None
    for weight in (a, b):
        if weight:
            for numerator in (trace+root, trace-root):
                x, rem = divmod(numerator, 2*weight)
                if not rem and 1 < x < n and n % x == 0:
                    return min(x, n//x)
    return None


def collision_sweep(n, m, radius, base, exponents, giants, translated):
    step = m*m
    work = Counter()
    alpha = pow(base, step, n)
    babies = [(e, pow(alpha, e, n)) for e in exponents]
    work["baby_powers"] = len(babies)
    work["stride_powers"] = 1
    first = None
    for g in giants:
        shift = g.shift if translated else 0
        # Fuse alpha^shift into the exponent of beta.
        giant = pow(base, g.a*n+g.b-g.offset+step*shift, n)
        work["giant_powers"] += 1
        for exponent, baby in babies:
            work["table_entries_visited"] += 1
            index = exponent-shift
            if not 0 <= index <= 2*radius:
                continue
            divisor = gcd(baby-giant, n)
            work["pair_gcds"] += 1
            if divisor == 1:
                continue
            trace = g.offset+step*index
            if divisor == n:
                work["exact_match_square_tests"] += 1
                factor = recover_trace(n, g.a, g.b, trace)
                kind = "exact"
            else:
                work["proper_collisions"] += 1
                factor = min(divisor, n//divisor)
                kind = "proper_gcd"
            if factor is not None and first is None:
                first = dict(factor=factor, cofactor=n//factor, kind=kind, trace=trace,
                             index=index, baby_exponent=exponent, giant=asdict(g))
    return dict(first=first, work=dict(work))


def exceptional_budgets(n, skipped):
    """Guaranteed public weight and error caps for each positive skipped family."""
    budgets = {}
    fallback = []
    for g in skipped:
        if g.a <= 0 or g.b <= 0:
            fallback.append(g)
            continue
        u, v = g.a//g.d, g.b//g.d
        # u*N/x-v*x is decreasing throughout the anchor interval.
        bound = max(ceil_ratio(abs(u*n-v*x*x), x) for x in (g.anchor, g.upper))
        cap, gap = budgets.get(g.d, (0, 0))
        budgets[g.d] = max(cap, u, v), max(gap, bound)
    return budgets, fallback


def search(n, m, m0, selected, max_bad=0, base=2, compare=False, exceptional=False,
           baby_width=8):
    """Run the complete bounded schedule even after the first verified split."""
    if not 1 <= base < n or gcd(base, n) != 1 or baby_width < 1:
        raise ValueError("need a unit base in [1,N) and a positive baby width")
    giants, radius, period, residues, work = setup(n, m, m0, selected, max_bad)
    kept = [g for g in giants if g.bad <= max_bad]
    skipped = [g for g in giants if g.bad > max_bad]
    upper = 2*radius+period-1
    exponents = sorted(e for r in residues for e in range(r, upper+1, period))
    ordinary = collision_sweep(n, m, radius, base, exponents, kept, True)
    budgets, fallback = exceptional_budgets(n, skipped)
    work["baby_exponents_generated"] = len(exponents)
    work["exceptional_endpoint_bounds"] = 2*(len(skipped)-len(fallback))
    result = dict(radius=radius, period=period, passing_residues=len(residues),
                  sparse_entries=len(exponents), translated_dense_entries=upper+1,
                  unshifted_dense_entries=2*radius+1, kept=len(kept), skipped=len(skipped),
                  bad_histogram=dict(sorted(Counter(g.bad for g in giants).items())),
                  setup_work=dict(work), ordinary=ordinary, exceptional_budgets=budgets,
                  fallback_giants=len(fallback))
    if compare:
        result["dense_retained"] = collision_sweep(n, m, radius, base,
                                                  range(2*radius+1), kept, False)
        result["coarse_all"] = collision_sweep(n, m, radius, base, range(2*radius+1), giants, False)
    if exceptional:
        result["exceptional"] = {d: search_product(n, m, d, cap, gap, baby_width, base)
                                 for d, (cap, gap) in sorted(budgets.items())}
        if fallback:
            result["fallback"] = collision_sweep(n, m, radius, base, range(2*radius+1),
                                                 fallback, False)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--m0", type=int, required=True)
    parser.add_argument("--selected", type=int, nargs="*", default=[])
    parser.add_argument("--max-bad", type=int, default=0)
    parser.add_argument("--base", type=int, default=2)
    parser.add_argument("--baby-width", type=int, default=8)
    parser.add_argument("--compare", action="store_true")
    parser.add_argument("--exceptional", action="store_true")
    print(json.dumps(search(**vars(parser.parse_args())), indent=2))
