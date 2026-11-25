"""Compare a single projected quartic parent with its two ordinary quartic children."""

from collections import Counter
import json
from math import comb, gcd, isqrt, prod
from pathlib import Path
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter

from .gap_newton_lanes import dickson_basis, gap_coordinates
from .norm_auxiliary import integer_roots, reduced_basis
from .unit_quartic_probe import local_values, probe as fine_probe, unit_basis
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]


def clear_column(a, b, col):
    """Unimodular two-row operation giving a positive gcd pivot and a zero."""
    x, y = a[col], b[col]
    if not y:
        return (a, b) if x > 0 else ([-v for v in a], b)
    g = gcd(x, y)
    q = y//g
    s = pow(x//g, -1, abs(q))
    t = (g-s*x)//y
    return ([s*i+t*j for i,j in zip(a, b)], [(x//g)*j-q*i for i,j in zip(a, b)])


def projected_basis(n, u, radix):
    modulus = 360*radix**4
    r0, r1, r2, r3, r4 = unit_basis(n, u, radix)
    # Column 2 is the constant trace. Rows 0..2 have zero columns 3 and 4.
    pivot1, left = clear_column(r1, r2, 1)
    pivot0, constant = clear_column(r0, left, 0)
    if any(constant[j] for j in (0, 1, 3, 4)) or abs(constant[2]) != modulus:
        raise ArithmeticError('the removed row did not generate the pure constant axis')
    rows = [pivot0, pivot1, r3, r4]
    columns = [0, 1, 3, 4]
    determinant = prod(row[j] for row,j in zip(rows, columns))
    if determinant * (12960*radix**10) != modulus**4:
        raise ArithmeticError('the projected lattice has the wrong determinant')
    # Center the four projected columns before handing the basis to integer LLL.
    for i, row in enumerate(rows):
        for h in reversed(range(i)):
            col = columns[h]
            denom = rows[h][col]
            q = (row[col]+denom//2)//denom
            row = [a-q*b for a,b in zip(row, rows[h])]
        row[2] %= modulus
        rows[i] = row
    return rows


def primitive_level(trace, n, u, radix, level, modulus):
    # Subtracting level*M changes only the constant coefficient of the trace.
    c = trace.copy()
    c[2] -= level*modulus
    f = [v*n**max(2-j, 0) for j,v in enumerate(c)]
    shifted = [radix**j * sum(comb(i,j)*f[i]*u**(i-j) for i in range(j,5))
               for j in range(5)]
    content = gcd(*shifted)
    if not content:
        raise ArithmeticError('the projected relation was constant')
    return [v//content for v in shifted]


def has_local_root(poly, prime):
    for x in range(prime):
        value = 0
        for c in reversed(poly):
            value = (value*x+c) % prime
        if not value:
            return True
    return False


def projected_relation(n, radix, u, coordinates, scales, work):
    basis = projected_basis(n, u, radix)
    modulus = 360*radix**4
    weighted = [[c*w for c,w in zip(coordinates(row)[1:], scales[1:])] for row in basis]
    reduced, lifts = reduced_basis(weighted, work, initial_coefficients=basis)
    # The shortest of the four returned vectors satisfies the first-vector bound.
    i = min(range(4), key=lambda i: sum(map(abs, reduced[i])))
    trace = lifts[i]
    coords = coordinates(trace)
    if [v*w for v,w in zip(coords[1:], scales[1:])] != reduced[i] or not any(coords[1:]):
        raise ArithmeticError('invalid projected short vector')
    constant = coords[0] % modulus
    trace[2] += constant-coords[0]
    full = [v*n**max(2-j, 0) for j,v in enumerate(trace)]
    if any(any(values) for values in local_values(full, u, radix).values()):
        raise ArithmeticError('invalid unit congruences on the lifted trace')
    spread = sum(map(abs, reduced[i]))
    first, last = -((spread-constant)//modulus), (spread+constant)//modulus
    return trace, full, modulus, constant, spread, first, last


def search(n, radix, u=1):
    if n < 3 or gcd(n, 30) != 1 or radix < 8 or radix & (radix-1) or not 0 < u < radix or u % 2 == 0:
        raise ValueError('expected n coprime to 30, a dyadic radix >= 8 and an odd residue')
    work = Counter()
    transform, scales = dickson_basis(n, 2)
    def coordinates(row):
        return gap_coordinates(row, transform)
    trace, _, modulus, constant, spread, first, last = projected_relation(
        n, radix, u, coordinates, scales, work)
    work['possible_levels'] = max(0, last-first+1)
    work['local_evaluation_checks'] = 15
    lower, upper = max(2, isqrt((n-1)//2)+1), isqrt(2*n)
    hits = set()
    for j in range(first, last+1):
        polynomial = primitive_level(trace, n, u, radix, j, modulus)
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            work['local_root_tests'] += 1
            if not has_local_root(polynomial, p):
                work['levels_rejected_mod_prime'] += 1
                break
        else:
            work['levels_isolated'] += 1
            for low, high in ((lower, upper), (-upper, -lower)):
                for k in integer_roots(polynomial, -((u-low)//radix), (high-u)//radix, work):
                    x = u+radix*k
                    y, rem = divmod(n, x)
                    p, q = sorted((abs(x), abs(y)))
                    work['integer_roots'] += 1
                    if rem == 0 and p > 1 and q <= 2*p:
                        hits.add((p,q))
    return dict(radix=str(radix), u=str(u), rank=4, spread=str(spread), constant=str(constant),
                modulus=str(modulus), trace=list(map(str, trace)), first_level=first, last_level=last,
                pairs=[[str(x),str(y)] for x,y in sorted(hits)], work=dict(work))


def record_budget(result, n):
    radix = int(result['radix'])
    total = (radix//2 + 4*int(n%8 == 1) + 4*int((-n)%8 == 1))//4
    result.update(visited_signed_groups=1, total_signed_groups=str(total), remaining_signed_groups=str(total-1))


def signed_class(n, r, u):
    partner = n*pow(u, -1, r) % r
    return {u % r, (-u) % r, partner, (-partner) % r}


def compare(n, fine_exponent, u, repeats):
    r = 1 << (fine_exponent-1)
    def parent():
        return search(n, r, u)
    def children():
        children_u = [u] if u+r in signed_class(n, 2*r, u) else [u, u+r]
        runs = [fine_probe(n, 2*r, v) for v in children_u]
        pairs = {tuple(pair) for row in runs for pair in row['pairs']}
        return dict(pairs=[list(pair) for pair in sorted(pairs)], rank=5, residues=list(map(str, children_u)),
                    work=dict(sum((Counter(x['work']) for x in runs), Counter())))
    reports, times = {}, {'parent': [], 'children': []}
    for repeat in range(repeats):
        order = [('parent', parent), ('children', children)]
        for name, method in (order if repeat%2==0 else reversed(order)):
            start = perf_counter()
            reports[name] = method()
            times[name].append(perf_counter()-start)
    record_budget(reports['parent'], n)
    if reports['parent']['pairs'] != reports['children']['pairs']:
        raise ArithmeticError('parent and its two children disagree')
    return dict(n=str(n), fine_exponent=fine_exponent, parent_u=str(u), reports=reports, seconds=times,
                median_seconds={k:median(v) for k,v in times.items()})


def run():
    small = [compare(96577, 6, u, 3) for u in range(1, 32, 2)
             if u == min(signed_class(96577, 32, u))]
    products = {row['id']: int(row['n']) for row in
                json.loads((ROOT/'benchmarks/quartic-factor-lanes.json').read_text())}
    full = {name: compare(products[name], 614, 1, 1) for name in
            ('unit-lane-crossed-2048', 'unit-lane-fresh-2048')}
    with TemporaryDirectory() as temp:
        proof = Path(temp)/'Factorization.lean'
        for report in full.values():
            for pair in report['reports']['parent']['pairs']:
                proof.write_text(render_certificate(int(report['n']), list(map(int, pair))))
                verify_file(proof)
            report['lean_certificates'] = len(report['reports']['parent']['pairs'])
            report['remaining_cofactor'] = (None if report['reports']['parent']['pairs'] else report['n'])
        deeper = []
        for name in full:
            n = products[name]
            for exponent in (612, 611, 610):
                start = perf_counter()
                result = search(n, 1 << exponent, 1)
                seconds = perf_counter()-start
                record_budget(result, n)
                for pair in result['pairs']:
                    proof.write_text(render_certificate(n, list(map(int, pair))))
                    verify_file(proof)
                deeper.append(dict(source=name, exponent=exponent, seconds=seconds, result=result,
                                   lean_certificates=len(result['pairs']),
                                   remaining_cofactor=None if result['pairs'] else str(n)))
    return dict(small=small, full_size=full, deeper=deeper)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
