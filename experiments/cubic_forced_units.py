"""Two public rows with a square rational product and a square algebraic norm.

Replay the fixed parameter census, public control panel, and sample prime
factor certificates with `python3 -m experiments.cubic_forced_units --check --verify`.
The diagonal subfamily has a separate exact shape test from the product.
"""

import argparse
from collections import Counter
import json
import re
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from .cubic_square_readout import direct_readout, projected_readout
from .cubic_trace_roots import readout
from .cubic_trace_search import characteristic
from .offset_tangent_cover import cube_root


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / 'research/cubic-forced-units.json'
PAIRS = tuple(sorted({(1, 4*i*i) for i in range(1, 9)} | {(1, 9), (4, 9), (4, 25), (9, 16)}))


def is_smooth(value):
    value = abs(value)
    if not value:
        return False
    for p in (2, 3, 5, 7):
        while value % p == 0:
            value //= p
    return value == 1


SHIFTS = tuple(h for a in range(1, 65) if is_smooth(a) for h in (a, -a))


def representatives(r, t):
    """Closest nonzero smooth representative per congruence class, positive on ties."""
    shifts = {}
    for h in SHIFTS:
        shifts.setdefault(h % (r*t), h)
    return shifts


def divisors(value, work, *, squared=False):
    """Divisors of a small public parameter or its square, with trial costs."""
    if value < 1:
        raise ValueError('positive divisor target required')
    powers = []
    p = 2
    while p*p <= value:
        e = 0
        while True:
            work['parameter_divisibility_tests'] += 1
            if value % p:
                break
            value //= p
            e += 1
        if e:
            powers.append((p, e))
        p = 3 if p == 2 else p+2
    if value > 1:
        powers.append((value, 1))
    answers = [1]
    for prime, exponent in powers:
        previous = list(answers)
        for j in range(1, (2 if squared else 1)*exponent + 1):
            answers.extend(d * prime**j for d in previous)
    return sorted(answers)


def irreducible(r, t, h, w, work):
    """A monic cubic is reducible over Q iff an integer k gives product h."""
    if abs(h) < t-r-1:
        # For nonzero k+r and k+t, their product has magnitude at least t-r-1.
        work['irreducible_by_spacing'] += 1
        return True
    for d in divisors(abs(h), work):
        for a in (d, -d):
            work['integer_root_tests'] += 1
            if a * (a+t-r) * (a+w-r) == h:
                return False
    return True


def maximum_w(r, t, h):
    """Use 1 ≤ |u| ≤ h²(t−r)² in the divided quartic equation."""
    size = h*h*(t-r)**2
    return (size**2 + 2*abs(h)*(r+t) + 8*h*h + size) // (4*abs(h))


def positions(r, t, h, work):
    """All integral u and positive w solving the complementary trace quartic."""
    square = h*h*(t-r)**2
    for d in divisors(abs(h)*(t-r), work, squared=True):
        for u in (d, -d):
            work['signed_divisor_tests'] += 1
            numerator = u**4 + 2*h*(r+t)*u*u - 8*h*h*u + square
            w, rem = divmod(numerator, 4*h*u*u)
            if not rem and w > 0:
                yield u, w


def sign_gcds(n, r, t, h, u):
    z = isqrt(r*t)
    if z*z != r*t:
        raise ValueError('the rational side must be a square')
    left = z*(u*u + h*(r+t))
    right = 2*h*(u+r*t)
    minus, plus = left-right, left+right
    if minus*plus != 4*h*u*u*n:
        raise ArithmeticError('signed factor identity failed')
    return [gcd(n, minus), gcd(n, plus)]


def cubic_data(n, r, t, h, w):
    if n != r*t*w-h:
        raise ValueError('wrong specialization for this input')
    return (n, r*t+(r+t)*w, r+t+w), (r*t, r+t, 1)


def readouts(n, r, t, h, w):
    f, beta = cubic_data(n, r, t, h, w)
    z = isqrt(r*t)
    if z*z != r*t:
        raise ValueError('the rational side must be a square')
    # These include the actual bounded quartic isolation on each input.
    abc = characteristic(f, beta)
    if abc[2] != h*h:
        raise ArithmeticError('unexpected algebraic norm')
    original = readout(n, z, *abc)
    projected = projected_readout(n, 0, f, beta, z)
    direct = [direct_readout(n, 0, f, beta, z, wit) for wit in original['witnesses']]
    if bool(original['witnesses']) != bool(projected['signed_traces']):
        raise ArithmeticError('projection changed square status in the cubic field')
    return {
        'rational_square_root': z, 'norm': str(h*h), 'derivative_gcd': gcd(f[1], n),
        'ordinary_traces': list(map(str, original['roots'])),
        'ordinary_gcds': [probe['gcds'] for probe in original['probes']],
        'direct_gcds': [result['gcds'] for result in direct],
        'projected_traces': list(map(str, projected['signed_traces'])),
        'projected_gcds': projected['gcds'],
        'root_nodes': [original['work']['integer_root_nodes'], projected['work']['integer_root_nodes']],
        'quartic_mod5_tests': 10,
    }


def universal(n):
    if n <= 1 or n % 2 == 0:
        raise ValueError('expected an odd integer greater than one')
    h = 1 if n % 4 == 3 else -1
    w = (n+h)//4
    work = Counter()
    traces = [u for u, ww in positions(1, 4, h, work) if ww == w]
    result = readouts(n, 1, 4, h, w)
    if bool(traces) != bool(result['ordinary_traces']):
        raise ArithmeticError('complementary and original quartics disagree')
    return dict(result, h=h, complementary_traces=traces, work=dict(work),
                elementary_gcds=[sign_gcds(n, 1, 4, h, u) for u in traces])


def varied(n):
    if n <= 1 or n % 2 == 0:
        raise ValueError('expected an odd integer greater than one')
    work = Counter()
    hits = []
    for r, t in PAIRS:
        # Build the same small residue map for every input; no case labels.
        work['representative_visits'] += len(SHIFTS)
        h = representatives(r, t).get(-n % (r*t))
        if h is None:
            work['no_representative'] += 1
            continue
        w = (n+h)//(r*t)
        if w < 1 or w > maximum_w(r, t, h):
            work['height_exclusions'] += 1
            continue
        if not irreducible(r, t, h, w, work):
            work['reducible_cubics'] += 1
            continue
        work['irreducible_cubics_scanned'] += 1
        for u, ww in positions(r, t, h, work):
            if ww == w:
                gcds = sign_gcds(n, r, t, h, u)
                work['elementary_gcds'] += 2
                hits.append(dict(r=r, t=t, h=h, w=w, u=u, gcds=gcds, readouts=readouts(n, r, t, h, w)))
    return dict(parameter_pairs=len(PAIRS), work=dict(work), trace_hits=hits)


def diagonal(n):
    """One cube root and one square test recognize the u=H=1, t=4s² family."""
    if n <= 1:
        raise ValueError('positive composite candidate required')
    t = cube_root(4*n-1)+1
    z = isqrt(t)
    s = z//2
    split = []
    if s >= 2 and t == 4*s*s and 16*s**6-4*s*s-1 == n:
        split = [4*s**3-4*s*s+2*s-1, 4*s**3+4*s*s+2*s+1]
        if split[0]*split[1] != n:
            raise ArithmeticError('diagonal polynomial factors failed')
    result = dict(integer_cube_roots=1, integer_square_roots=1, factors=list(map(str, split)))
    if split:
        # Count the positions to this particular representation. Its priority
        # as the first proper hit additionally requires both factors to be prime.
        first = isqrt(n-1)+1
        midpoint = sum(split)//2
        if midpoint-first != 2*s:
            raise ArithmeticError('Fermat midpoint distance failed')
        result['fermat_tests_to_displayed_pair'] = str(midpoint-first+1)
    return result


def exact_menu_support():
    """Invert the public search: enumerate all possible input products for this menu."""
    work = Counter()
    potential, squares, splits, unramified = set(), set(), set(), set()
    for r, t in PAIRS:
        for h in representatives(r, t).values():
            work['parameter_triples'] += 1
            for u, w in positions(r, t, h, work):
                n = r*t*w-h
                if n <= 1 or n % 2 == 0:
                    continue
                potential.add(n)
                if not irreducible(r, t, h, w, work):
                    continue
                squares.add(n)
                work['elementary_gcds'] += 2
                if any(1 < d < n for d in sign_gcds(n, r, t, h, u)):
                    splits.add(n)
                    f, _ = cubic_data(n, r, t, h, w)
                    c, b, a = f
                    disc = a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
                    if gcd(n, 2*r*t*h*u*b*disc) == 1:
                        unramified.add(n)
    return dict(odd_products_with_integral_trace=len(potential), maximum_before_irreducibility=max(potential),
                distinct_square_inputs=len(squares), maximum_square_input=max(squares),
                distinct_elementary_splits=len(splits), maximum_elementary_split=max(splits),
                distinct_unramified_elementary_splits=len(unramified), largest_unramified_split=max(unramified),
                work=dict(work))


def panel():
    archive = json.loads((ROOT/'research/cubic-trace-panel.json').read_text())
    cases = [(case['id'], int(case['n'])) for case in archive['rows']]
    # The varied semiprime was selected after enumerating this finite parameter menu.
    support = exact_menu_support()
    cases.extend([('universal-91', 91), ('varied-semiprime-1883747', 1883747),
                  ('diagonal-s2', 1007)])
    rows = []
    for name, n in cases:
        base = universal(n)
        more = varied(n)
        shape = diagonal(n)
        reported = [base['derivative_gcd'], *map(int, shape['factors'])]
        for pairs in (base['ordinary_gcds'], base['direct_gcds'], base['projected_gcds'], base['elementary_gcds']):
            reported.extend(v for pair in pairs for v in pair)
        for hit in more['trace_hits']:
            reported.extend(hit['gcds'])
            for key in ('ordinary_gcds', 'direct_gcds', 'projected_gcds'):
                reported.extend(v for pair in hit['readouts'][key] for v in pair)
        proper = sorted({g for g in reported if 1 < g < n})
        split = sorted((proper[0], n//proper[0])) if proper else []
        rows.append(dict(id=name, n=str(n), universal=base, varied=more, diagonal=shape,
                         split=list(map(str, split)), remaining_cofactor='1' if split else str(n)))
    # Read only the literal public product from the separately constructed control.
    proof = ROOT/'benchmarks/controls/CubicForcedControl.lean'
    match = re.search(r'^abbrev publicProduct : ℕ := (\d+)$', proof.read_text(), re.MULTILINE)
    if match is None:
        raise ValueError('missing decimal public product in the controlled example')
    control = match.group(1)
    controlled = dict(n=control, search=diagonal(int(control)), prime_proof=str(proof.relative_to(ROOT)))
    return dict(pairs=[list(pair) for pair in PAIRS], diagonal_full_size=controlled,
                shift_bound=64, shift_primes=[2,3,5,7],
                representative_order='least absolute value, positive on ties', census=support, rows=rows)


def verify(report):
    from scripts.factor import render_certificate, verify_file
    with TemporaryDirectory() as directory:
        proof = Path(directory)/'CheckedFactor.lean'
        for row in report['rows']:
            if row['split']:
                proof.write_text(render_certificate(int(row['n']), list(map(int, row['split']))))
                verify_file(proof)
        control = report['diagonal_full_size']
        n = int(control['n'])
        p, q = map(int, control['search']['factors'])
        theorem = 'PrimeFactors.Generated.cubicForcedPanel'
        proof.write_text((ROOT/control['prime_proof']).read_text() + f"""

theorem {theorem} : PrimeFactors.CubicForcedParameters.decode {n}=some ({p},{q}) ∧
    PrimeFactors.ExactFactorization {n} [{p},{q}] := PrimeFactors.CubicForcedControl.control_checks
#print axioms {theorem}
""")
        verify_file(proof, theorem)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    report = panel()
    if args.check and json.loads(ARCHIVE.read_text()) != report:
        raise ValueError('stored forced-unit panel differs from the public replay')
    if args.verify:
        verify(report)
    if args.write:
        ARCHIVE.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report['census'], indent=2))


if __name__ == '__main__':
    main()
