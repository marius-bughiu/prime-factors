"""Check candidate quartic traces on the entire positive factor interval."""

import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from .centered_sum_quartic import centered_coordinates, windows
from .norm_auxiliary import reduced_basis
from .unit_quartic_probe import ROOT, checked_polynomial, factor_roots, unit_basis
from scripts.factor import primes_through, render_certificate, verify_file


def primitive(coefficients):
    """Remove high zeros and divide by positive content, preserving signs."""
    p = list(coefficients)
    while p and p[-1] == 0:
        p.pop()
    if p:
        content = gcd(*p)
        p = [v//content for v in p]
    return p


def negative_remainder(a, b):
    """A positive scalar multiple of minus the rational polynomial remainder."""
    r = list(a)
    leading = b[-1]
    while len(r) >= len(b):
        shift = len(r)-len(b)
        multiple = r[-1] if leading > 0 else -r[-1]
        r = [v*abs(leading) for v in r]
        for i, v in enumerate(b):
            r[shift+i] -= multiple*v
        r = primitive(r)
    return [-v for v in r]


def evaluate(p, x):
    value = 0
    for coefficient in reversed(p):
        value = value*x+coefficient
    return value


def variations(signs):
    nonzero = [v > 0 for v in signs if v]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def positive_on(coefficients, low, high):
    """Strict positivity on a closed real interval, including repeated roots."""
    if low > high:
        raise ValueError('empty interval')
    p = primitive(coefficients)
    if evaluate(p, low) <= 0 or evaluate(p, high) <= 0:
        return False
    if low == high or len(p) == 1:
        return True
    derivative = primitive([i*p[i] for i in range(1, len(p))])
    chain = [p, derivative]
    while True:
        remainder = negative_remainder(chain[-2], chain[-1])
        if not remainder:
            break
        chain.append(remainder)
    return (variations(evaluate(v, low) for v in chain)
            == variations(evaluate(v, high) for v in chain))


def envelope(full, bound, low, high, *, scale=1):
    """Test -bound*x² < scale*F(x) < bound*x² throughout the factor window."""
    signs = []
    for sign in (-1, 1):
        test = [sign*scale*v for v in full]
        test[2] += bound
        signs.append(positive_on(test, low, high))
    return all(signs)


def volume_exponent(n, high):
    k = isqrt(4*n)
    width = high+n//high-k
    cost = 120*width**5*(2*(k+1)+width)
    exponent = 3
    while cost >= (12960*459) << (10*exponent):
        exponent += 1
    return exponent


def probe(n, exponent, u=1):
    low, high, center, sum_center, radius, s = windows(n)
    if exponent < 3 or not 0 < u < 1 << exponent or u % 2 == 0:
        raise ValueError('expected e >= 3 and an odd residue in [1,2^e)')
    start = perf_counter()
    radix = 1 << exponent
    modulus = 360*radix**4
    scales = [1, 2*s, radius, 2*s*s, 2*s*radius]
    basis = unit_basis(n, u, radix)

    def scaled(trace):
        coords = centered_coordinates(trace, n, center, sum_center, s)
        return [v*w for v, w in zip(coords, scales)]

    work = Counter()
    rows, traces = reduced_basis([scaled(v) for v in basis], work, initial_coefficients=basis)
    summary = []
    passing = []
    for index, (row, trace) in enumerate(zip(rows, traces)):
        if not any(trace) or scaled(trace) != row:
            raise ArithmeticError('inconsistent quartic lattice transform')
        full = [trace[0]*n*n, trace[1]*n, *trace[2:]]
        norm = sum(map(abs, row))
        accepted = envelope(full, modulus, low, high)
        summary.append(dict(row=index, l1_permyriad=10000*norm//modulus,
                            l1_pass=norm < modulus, curve_pass=accepted))
        if accepted:
            passing.append((norm, index))
    total = (radix//2 + (4 if n%8 == 1 else 0))//2
    result = dict(exponent=exponent, residue=str(u), rows=summary, total_groups=str(total),
                  unchecked_groups=str(total), status='no certified equation', selected_row=None,
                  candidate_factors=[], pairs=[], remaining_cofactor=str(n))
    if passing:
        norm, index = min(passing)
        trace = traces[index]
        poly, checks = checked_polynomial(n, u, radix, trace)
        pairs, hits = factor_roots(n, u, radix, poly, [(low, high)], work)
        full = [trace[0]*n*n, trace[1]*n, *trace[2:]]
        # Enclose the maximum absolute trace in consecutive parts per thousand.
        below, above = 0, 1000
        while above-below > 1:
            middle = (above+below)//2
            if envelope(full, middle*modulus, low, high, scale=1000):
                above = middle
            else:
                below = middle
        result.update(selected_row=index, weighted_l1=str(norm), curve_permille=[below, above],
                      trace_coefficients=list(map(str, trace)), local_remainders=checks,
                      unchecked_groups=str(total-1), candidate_factors=hits,
                      pairs=[[str(p), str(q)] for p,q in sorted(pairs)],
                      status='factor pair found' if pairs else 'certified empty lane',
                      remaining_cofactor=None if pairs else str(n))
    result.update(work=dict(work), search_seconds=perf_counter()-start)
    return result


def run():
    names = ('unit-lane-crossed-2048', 'unit-lane-fresh-2048')
    inputs = {case['id']: int(case['n']) for case in
              json.loads((ROOT/'benchmarks/quartic-factor-lanes.json').read_text())}
    output = []
    with TemporaryDirectory() as temp:
        path = Path(temp)/'Factorization.lean'
        for name in names:
            n = inputs[name]
            e = volume_exponent(n, windows(n)[1])
            for exponent in (e, e-1):
                result = probe(n, exponent)
                certificates = []
                for pair in result['pairs']:
                    start = perf_counter()
                    proof = render_certificate(n, list(map(int, pair)))
                    path.write_text(proof)
                    verify_file(path)
                    certificates.append(dict(sha256=sha256(proof.encode()).hexdigest(),
                                             seconds=perf_counter()-start))
                output.append(dict(source=name, n=str(n), volume_exponent=e,
                                   result=result, lean_certificates=certificates))
    return output


def small_panel():
    """Compare all positive reciprocal classes on a fixed set of labeled products."""
    primes = [p for p in primes_through(8191) if p >= 4096]
    counts = Counter()
    for p in primes[:9]:
        for q in primes[-9:]:
            n = p*q
            counts['products'] += 1
            for u in range(1, 16, 2):
                if u > n*pow(u, -1, 16)%16:
                    continue
                result = probe(n, 4, u)
                occupied = u in (p%16, q%16)
                original = any(row['l1_pass'] for row in result['rows'])
                curve = result['selected_row'] is not None
                if curve and result['pairs'] != ([[str(p), str(q)]] if occupied else []):
                    raise ArithmeticError('certified result disagrees with the labeled factors')
                counts['groups'] += 1
                counts['occupied'] += occupied
                counts['l1_certified'] += original
                counts['l1_occupied_certified'] += original and occupied
                counts['curve_certified'] += curve
                counts['curve_occupied_certified'] += curve and occupied
    return dict(counts)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--small', action='store_true', help='run the fixed 81-product comparison')
    print(json.dumps(small_panel() if parser.parse_args().small else run(), indent=2))
