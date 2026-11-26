"""Compare product-chosen cubic bases at the row collection stage.

For s=2^i*3^j near the real cube root, m=s-t makes t+m smooth.
Each proposed m gets its own monic polynomial. Only rows belonging to the
same polynomial can contribute to a dependency in that number field.

Replay with python3 -m experiments.cubic_smooth_bases --check.
"""

import argparse
from collections import Counter
import json
from itertools import count
from pathlib import Path

from .cubic_trace_search import OFFSETS, POINTS, PRIMES, cube_root, evaluate, smooth_parity

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'research/cubic-smooth-bases.json'
SHIFTS = (0, 1, -1, 2, -2)
CERT_PRIMES = tuple(p for p in PRIMES if p <= 97)


def balanced_polynomial(n, m):
    if n < 2 or m < 2:
        raise ValueError('the input and base must each be at least 2')
    quotient = n - m**3
    digits = []
    for _ in range(2):
        centered = (quotient + m//2) % m - m//2
        digits.append(centered)
        quotient = (quotient-centered)//m
    f = (*digits, quotient)
    if evaluate(f, m) != n:
        raise ArithmeticError('balanced polynomial does not take the prescribed value')
    return f


def certificate(f, work):
    for p in CERT_PRIMES:
        work['certificate_primes'] += 1
        for x in range(p):
            work['certificate_evaluations'] += 1
            if evaluate(f, x) % p == 0:
                break
        else:
            return p
    return None


def smooth_values(n, j_max):
    """Exact band and ordering by distance from the real cube root."""
    if n < 2 or j_max < 0:
        raise ValueError('expected n>=2 and a nonnegative ternary exponent limit')
    floor = cube_root(n)
    nearest = floor + int(8*n > (2*floor+1)**3)
    values = []
    for j in range(j_max+1):
        s = 3**j
        while s**3 <= 8*n:
            if n <= 8*s**3:
                values.append(s)
            s *= 2
    # If two integers are equidistant from nearest, use the side of the
    # actual root. At a perfect cube small-to-large resolves exact ties.
    above = nearest**3 < n
    return sorted(values, key=lambda s: (abs(s-nearest), -s if above else s))


def candidate_bases(values):
    menu = {}
    for s in values:
        for t in SHIFTS:
            if s-t >= 2:
                menu.setdefault(s-t, []).append(t)
    return menu


def conventional(n, tags):
    """Assign the same tagged rows to the same number of distinct cube-root offsets."""
    floor = cube_root(n)
    offsets = ((k+1)//2 * (1 if k % 2 else -1) for k in count())
    eligible = (floor+offset for offset in offsets if floor+offset >= 2)
    return {m: shifts for shifts, m in zip(tags, eligible)}


def metrics():
    return {k: 0 for k in ('visited', 'rational_smooth', 'norm_smooth', 'joint')}


def update(stat, rational_ok, norm_ok):
    stat['visited'] += 1
    stat['rational_smooth'] += int(rational_ok)
    stat['norm_smooth'] += int(norm_ok)
    stat['joint'] += int(rational_ok and norm_ok)


def run_arm(n, bases, first_only=False):
    work = Counter({k: 0 for k in ('bases_tried', 'certificate_primes', 'certificate_evaluations',
                                  'certified_bases', 'trial_prime_visits', 'exact_prime_divisions')})
    all_rows, small, designated = metrics(), metrics(), metrics()
    tagged_bits, all_bits, floors = [], [], []
    first = None
    max_per_base = active = 0
    for m, tags in bases.items():
        work['bases_tried'] += 1
        f = balanced_polynomial(n, m)
        witness = certificate(f, work)
        if witness is None:
            continue
        work['certified_bases'] += 1
        count = 0
        c0, c1, c2 = f
        for a, b in POINTS:
            rational = a+b*m
            norm = a**3 - c2*a*a*b + c1*a*b*b - c0*b**3
            rational_ok = smooth_parity(rational, work) is not None
            norm_ok = smooth_parity(norm, work) is not None
            update(all_rows, rational_ok, norm_ok)
            all_bits.append(abs(norm).bit_length())
            count += int(rational_ok and norm_ok)
            if b == 1 and a in SHIFTS:
                update(small, rational_ok, norm_ok)
                if a in tags:
                    update(designated, rational_ok, norm_ok)
                    if rational <= 0 or (norm+n) % rational:
                        raise ArithmeticError('tagged row fails cubic divisibility')
                    residue = n % rational
                    floors.append(min(residue, rational-residue).bit_length())
                    tagged_bits.append(abs(norm).bit_length())
                    if first is None and rational_ok and norm_ok:
                        first = {'m': str(m), 't': a, 's': str(rational), 'norm': str(norm),
                                 'coefficients': list(map(str, f)), 'irreducibility_prime': witness}
        active += int(count > 0)
        max_per_base = max(max_per_base, count)
        if first_only:
            break

    def span(items):
        return [min(items), max(items)] if items else []

    return {'bases_offered': len(bases), 'work': dict(work), 'all_rows': all_rows,
            'five_small_shifts': small, 'designated_rows': designated,
            'bases_with_joint_rows': active, 'most_joint_rows_in_one_field': max_per_base,
            'all_norm_bits': span(all_bits), 'designated_norm_bits': span(tagged_bits),
            'designated_minimum_residue_bits': span(floors), 'first_designated_joint': first}


def dyadic_witness(n, s):
    """Recover the unique signed power-of-five exponent modulo s, without expanding 5**e."""
    if n % 2 == 0 or n < 1 or s < 4 or s & (s-1):
        raise ValueError('expected positive odd n and a dyadic modulus at least 4')
    residue = (-n) % s
    sign = 1 if residue % 4 == 1 else -1
    target = sign*residue % s
    exponent, current, power, multiplications = 0, 1, 5, 0
    steps = s.bit_length()-3
    for j in range(steps):
        # 5^(2^j) differs from 1 at its first nonzero bit j+2.
        if (target-current) & (1 << (j+2)):
            current = current*power % s
            exponent += 1 << j
            multiplications += 1
        power = power*power % s
    if current != target or (sign*pow(5, exponent, s)+n) % s:
        raise ArithmeticError('dyadic smooth norm failed modular validation')
    return {'base_power_of_two': s.bit_length()-1, 'sign': sign, 'exponent': str(exponent),
            'exponent_bits': exponent.bit_length(), 'norm_bits_lower_bound': str(2*exponent+1),
            'lift_steps_and_squarings': steps, 'extra_modular_multiplications': multiplications,
            'verification_powers': 1}


def compare(n):
    if n < 8:
        raise ValueError('the comparison requires n>=8')
    floor = cube_root(n)
    original = {floor+offset: [] for offset in OFFSETS if floor+offset >= 2}
    report = {'n': str(n), 'original_first_certified': run_arm(n, original, first_only=True)}
    for name, cap in (('dyadic', 0), ('two_three', 12)):
        values = smooth_values(n, cap)
        bases = candidate_bases(values)
        report[name] = {'smooth_values': len(values), 'adaptive': run_arm(n, bases),
                        'matched_offsets': run_arm(n, conventional(n, bases.values()))}
    if n % 2:
        report['unbounded_dyadic_witnesses'] = [dyadic_witness(n, s) for s in smooth_values(n, 0) if s >= 4]
    return report


def panel():
    # The previously published fixture supplies only IDs and public products.
    inputs = json.loads((ROOT/'research/cubic-trace-panel.json').read_text())['rows']
    selected = [r for r in inputs if r['id'].startswith(('holdout-', 'arbitrary-divisor-window-'))]
    return {'bound': 127, 'certificate_prime_limit': 97, 'max_power_of_three': 12,
            'shifts': list(SHIFTS), 'primitive_rows_per_base': len(POINTS),
            'inputs': [dict(id=r['id'], **compare(int(r['n']))) for r in selected]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = panel()
    if args.check:
        if result != json.loads(REPORT.read_text()):
            raise SystemExit('smooth cubic base panel differs from the recorded result')
        print(f"Verified {len(result['inputs'])} product-only row collection comparisons.")
    else:
        print(json.dumps(result, indent=2))
