"""Bounded reference sweep of normalized exceptional weights.

For N=p*q, m squarefree, r=m/d, test all 1<=u,v<=weight_cap with
gcd(uv,r)=1 and v*p^2=u*N modulo r. The error budget bounds |u*q-v*p|.
The two readouts exhaust the same schedule independently. A proper power gcd
can also split N incidentally at a trace with nonsquare discriminant. The
power readout explicitly compares every valid baby/giant pair and charges it.
This experiment takes d, the cap and the gap budget as public inputs; it does
not find short vectors, certify the order of a base, or establish primality.
"""

import argparse
import json
from collections import Counter
from math import gcd, isqrt


def squarefree_primes(m, work):
    primes = []
    candidate = 2
    while candidate*candidate <= m:
        work["wheel_divisibility_tests"] += 1
        if m % candidate == 0:
            primes.append(candidate)
            m //= candidate
            work["wheel_divisibility_tests"] += 1
            if m % candidate == 0:
                raise ValueError("m must be squarefree")
        candidate = 3 if candidate == 2 else candidate+2
    if m > 1:
        primes.append(m)
    return primes


def root_table(prime):
    table = [[] for _ in range(prime)]
    for x in range(1, prime):
        table[x*x % prime].append(x)
    return table


def crt_roots(n, u, v, tables, work):
    residues = [0]
    modulus = 1
    for prime, table in tables:
        work["local_root_lookups"] += 1
        work["root_inverses"] += 1
        roots = table[u * n * pow(v, -1, prime) % prime]
        if not roots:
            return []
        work["crt_inverses"] += 1
        inverse = pow(modulus, -1, prime)
        residues = [x+modulus*((y-x)*inverse % prime) for x in residues for y in roots]
        work["crt_root_extensions"] += len(residues)
        modulus *= prime
    return residues


def trace_factor(n, u, v, trace):
    discriminant = trace*trace-4*u*v*n
    root = isqrt(discriminant)
    if root*root == discriminant:
        for numerator in (trace-root, trace+root):
            x, rem = divmod(numerator, 2*v)
            if not rem and 1 < x < n and n % x == 0:
                return min(x, n//x)
    return None


def search_product(n, m, d, weight_cap, gap_bound, baby_width=8, base=2):
    if (n < 4 or not 1 <= d <= m or m % d or weight_cap < 1 or gap_bound < 0
            or baby_width < 1 or not 1 <= base < n):
        raise ValueError("invalid product, divisor, cap, gap, baby width or base")
    if gcd(n, m) != 1 or gcd(n, base) != 1:
        raise ValueError("the reference sweep needs m and base coprime to N")
    work = Counter(dict.fromkeys((
        "wheel_divisibility_tests", "local_root_table_entries", "weight_pairs",
        "unit_weight_pairs", "local_root_lookups", "root_inverses", "crt_inverses",
        "crt_root_extensions", "trace_residue_inverses", "unfiltered_traces",
        "roots", "trace_classes", "bound_square_roots", "traces", "giants",
        "base_powers", "baby_multiplications", "giant_powers", "pair_gcds",
        "proper_collisions", "exact_collisions", "direct_square_tests",
        "exact_match_square_tests"), 0))
    r = m//d
    tables = [(p, root_table(p)) for p in squarefree_primes(m, work) if r % p == 0]
    work["local_root_table_entries"] = sum(p-1 for p, _ in tables)
    step = r*r
    alpha = pow(base, step, n)
    work["base_powers"] = 1
    babies = [1]
    for _ in range(1, baby_width):
        babies.append(babies[-1]*alpha % n)
    work["baby_multiplications"] = baby_width-1

    direct = None
    power = None
    for u in range(1, weight_cap+1):
        for v in range(1, weight_cap+1):
            work["weight_pairs"] += 1
            if gcd(u*v, r) != 1:
                continue
            work["unit_weight_pairs"] += 1
            roots = crt_roots(n, u, v, tables, work)
            work["roots"] += len(roots)
            if r > 1:
                classes = {(u*n*pow(x, -1, step)+v*x) % step for x in roots}
                work["trace_residue_inverses"] += len(roots)
            else:
                classes = {0}
            work["trace_classes"] += len(classes)
            four_product = 4*u*v*n
            lower = 1+isqrt(four_product-1)
            upper = isqrt(four_product+gap_bound*gap_bound)
            work["bound_square_roots"] += 2
            work["unfiltered_traces"] += max(0, upper-lower+1)
            for residue in sorted(classes):
                first = lower+(residue-lower) % step
                for start in range(first, upper+1, step*baby_width):
                    work["giants"] += 1
                    giant = pow(base, u*n+v-start, n)
                    work["giant_powers"] += 1
                    slots = min(baby_width, (upper-start)//step+1)
                    for i in range(slots):
                        trace = start+step*i
                        work["traces"] += 1
                        factor = trace_factor(n, u, v, trace)
                        work["direct_square_tests"] += 1
                        if factor is not None and direct is None:
                            direct = dict(factor=factor, cofactor=n//factor, u=u, v=v, trace=trace)
                        g = gcd(babies[i]-giant, n)
                        work["pair_gcds"] += 1
                        if g == 1:
                            continue
                        if g == n:
                            work["exact_collisions"] += 1
                            work["exact_match_square_tests"] += 1
                            g = trace_factor(n, u, v, trace)
                            kind = "exact"
                        else:
                            work["proper_collisions"] += 1
                            g = min(g, n//g)
                            kind = "proper_gcd"
                        if g is not None and 1 < g < n and power is None:
                            power = dict(factor=g, cofactor=n//g, u=u, v=v, trace=trace,
                                         start=start, baby_index=i, kind=kind)
    return dict(r=r, direct=direct, power=power, work=dict(work))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--d", type=int, required=True)
    parser.add_argument("--weight-cap", type=int, required=True)
    parser.add_argument("--gap-bound", type=int, required=True)
    parser.add_argument("--baby-width", type=int, default=8)
    parser.add_argument("--base", type=int, default=2)
    args = parser.parse_args()
    print(json.dumps(search_product(**vars(args)), indent=2))
