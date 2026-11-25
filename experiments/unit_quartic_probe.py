"""Test one dyadic factor remainder with a quartic on the units modulo 3 and 5."""

from collections import Counter
import json
from math import comb, gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from .gap_newton_lanes import dickson_basis, gap_coordinates
from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_factor_lanes import triangular_basis
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
CONTENTS = (1, 1, 6, 6, 360)


def crt_nodes(u, radix):
    dyadic = 8*radix**4
    moduli = (dyadic, 9, 5)
    modulus = dyadic*45
    selectors = [(modulus//m)*pow(modulus//m, -1, m) for m in moduli]
    nodes = []
    for j in range(5):
        residues = (u+radix*j, 1+j+j//2, 1+j+j//4)
        nodes.append(sum(r*s for r, s in zip(residues, selectors)) % modulus)
    return nodes


def unit_basis(n, u, radix):
    """Construct the degree-four trace lattice from its CRT Newton coordinates."""
    factors = [n*n, n, 1, 1, 1]
    nodes = crt_nodes(u, radix)
    modulus = 360*radix**4
    bounds = [modulus//(radix**j*CONTENTS[j]) for j in range(4)]
    columns = []
    # Newton coefficient j of X^k is the complete homogeneous symmetric
    # polynomial of order k-j in nodes 0,...,j. Add one variable at a time.
    homogeneous = [1, 0, 0, 0, 0]
    for j, bound in enumerate(bounds):
        for h in range(1, 5-j):
            homogeneous[h] = (homogeneous[h]+nodes[j]*homogeneous[h-1]) % modulus
        columns.append([0 if k < j else homogeneous[k-j]*factors[k] % bound for k in range(5)])
    return triangular_basis(factors, bounds, columns)


def local_values(full, u, radix):
    def evaluate(point, modulus):
        value = 0
        for coefficient in reversed(full):
            value = (value*point+coefficient) % modulus
        return value
    return dict(dyadic_grid=[evaluate(u+radix*k, 8*radix**4) for k in range(5)],
                units_mod_9=[evaluate(x, 9) for x in (1, 2, 4, 5, 7, 8)],
                units_mod_5=[evaluate(x, 5) for x in (1, 2, 3, 4)])


def probe(n, radix, u=1):
    if n < 3 or gcd(n, 30) != 1 or radix < 8 or radix & (radix-1) or not 0 < u < radix or u % 2 == 0:
        raise ValueError('expected n >= 3 coprime to 30, dyadic radix >= 8 and an odd residue')
    start = perf_counter()
    work = Counter()
    modulus = 360*radix**4
    transform, scales = dickson_basis(n, 2)
    basis = unit_basis(n, u, radix)
    rows = [[v*s for v,s in zip(gap_coordinates(row, transform), scales)] for row in basis]
    reduced, originals = reduced_basis(rows, work, initial_coefficients=basis)
    best = min(range(len(reduced)), key=lambda i: sum(map(abs, reduced[i])))
    trace = originals[best]
    weighted = [a*b for a,b in zip(gap_coordinates(trace, transform), scales)]
    size = sum(map(abs, weighted))
    if weighted != reduced[best] or not any(trace) or size >= modulus:
        raise ArithmeticError('quartic failed the strict weighted trace bound')

    full = [c*n**max(2-j, 0) for j,c in enumerate(trace)]
    checks = local_values(full, u, radix)
    if any(any(values) for values in checks.values()):
        raise ArithmeticError('the raw polynomial failed a local evaluation')
    shifted = [radix**j * sum(comb(i,j)*full[i]*u**(i-j) for i in range(j,5)) for j in range(5)]
    content = gcd(*shifted)
    polynomial = [a//content for a in shifted]

    lower, upper = max(2, isqrt((n-1)//2)+1), isqrt(2*n)
    pairs, hits = set(), []
    for low, high in ((lower, upper), (-upper, -lower)):
        for k in integer_roots(polynomial, -((u-low)//radix), (high-u)//radix, work):
            x = u+radix*k
            hits.append(str(x))
            y, rem = divmod(n, x)
            p, q = sorted((abs(x), abs(y)))
            if rem == 0 and p > 1 and q <= 2*p:
                pairs.add((p, q))
    total_signed = (radix//2 + 4*int(n%8 == 1) + 4*int((-n)%8 == 1))//4
    return dict(n=str(n), radix=str(radix), u=str(u), signed=True, modulus=str(modulus),
                trace_coefficients=list(map(str, trace)), weighted_l1=str(size), local_remainders=checks,
                polynomial_degree=max(i for i,c in enumerate(full) if c), tested_signed_groups=1,
                total_signed_groups=str(total_signed), unchecked_signed_groups=str(total_signed-1),
                candidate_factors=hits, pairs=[[str(p),str(q)] for p,q in sorted(pairs)],
                work=dict(work), search_seconds=perf_counter()-start)


def run():
    cases = json.loads((ROOT/'benchmarks/quartic-factor-lanes.json').read_text())
    # Only the public products enter the computation, including the residue and radix choice.
    products = {r['id']: int(r['n']) for r in cases}
    rows = []
    with TemporaryDirectory() as temp:
        certificate = Path(temp)/'Factorization.lean'
        for name in ('unit-lane-crossed-2048', 'unit-lane-fresh-2048'):
            result = probe(products[name], 1 << 614)
            elapsed = 0.0
            for pair in result['pairs']:
                start = perf_counter()
                certificate.write_text(render_certificate(products[name], [int(p) for p in pair]))
                verify_file(certificate)
                elapsed += perf_counter()-start
            rows.append(dict(source=name, result=result, lean_certificates=len(result['pairs']),
                             verification_seconds=elapsed,
                             remaining_cofactor=None if result['pairs'] else result['n']))
    return dict(degree=4, radix_exponent=614, rows=rows)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
