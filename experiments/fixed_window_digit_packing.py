"""Find the least separating cyclotomic radix for a fixed public window and wheel.

Run as python3 -m experiments.fixed_window_digit_packing [--check]. The theorem
FixedWindowDigitPacking.threshold supplies the period compression. Candidate sums
are reconstructed from the product and common factor width. No digit is supplied
and no factor is used to choose the table, starting index or radix.
"""

import argparse
import json
from math import gcd
from pathlib import Path

from experiments.intermediate_totient_rows import product_band
from experiments.predecessor_square import factor_from_sum

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'research/fixed-window-digit-packing.json'
FIXTURE = ROOT / 'benchmarks/intermediate-totient-rows.json'
WORKED_FIXTURE = ROOT / 'benchmarks/fixed-window-digit-packing.json'


def allowed(n, m):
    """Solve x*y=n mod m for each x using one linear congruence."""
    sums = set()
    for x in range(m):
        d = gcd(x, m)
        if n % d:
            continue
        modulus = m//d
        y = (n//d)*pow(x//d, -1, modulus) % modulus
        sums.update((x+j) % m for j in range(y, m, modulus))
    return sums


def phases(mask):
    """Earliest simultaneous local hit in each displacement class."""
    t = len(mask)
    survivors = [i for i, keep in enumerate(mask) if keep]
    return [next((i for i in survivors if mask[(i+delta) % t]), None)
            for delta in range(t)]


def ceiling(x, y):
    return -((-x)//y)


def minimum(first, count, weight):
    """An exact lower cutoff on P for each fixed shift class, followed by one lift."""
    t = len(first)
    floors = []
    for v in range(t):
        floor = 1
        for h in range(1, t//gcd(t, v)+1):
            i = first[(h*v) % t]
            if i is not None:
                floor = max(floor, ceiling(count-i, h))
        floors.append(floor)

    step = weight*t
    best = None
    for r in range(1, step+1):
        d = gcd(weight, r)
        p0 = r//d
        jumps = max(0, ceiling(floors[p0 % t]-p0, step//d))
        radix = r + jumps*step
        if best is None or radix < best:
            best = radix
    return best


def collision(mask, count, weight, radix):
    """Find a concrete pair, or certify absence by the finite periodic test."""
    t = len(mask)
    p = radix//gcd(weight, radix)
    for h in range(1, min(t//gcd(t, p), (count-1)//p)+1):
        jump = p*h
        for i in range(min(t, count-jump)):
            if mask[i] and mask[(i+jump) % t]:
                return i, i+jump
    return None


def check_minimum(mask, count, weight, best, *, every_start=False):
    """Check the winner and a starting phase and failing pair per smaller radix lane."""
    t = len(mask)
    first_for_gap = {}
    if every_start:
        # Form every ordered survivor pair, independently of the threshold table.
        residues = [i for i in range(t) if mask[i]]
        for i in residues:
            for j in residues:
                first_for_gap.setdefault((j-i) % t, i)

    def witness(radix):
        if not every_start:
            pair = collision(mask, count, weight, radix)
            return None if pair is None else (0, *pair)
        p = radix//gcd(radix, weight)
        stop = min((count-1)//p, t//gcd(t, p))
        for h in range(1, stop+1):
            start = first_for_gap.get((h*p) % t)
            if start is not None:
                return start, 0, h*p
        return None

    if witness(best) is not None:
        raise ArithmeticError('reported radix has a collision')
    step = weight*t
    checks = 0
    for r in range(1, min(step, best-1)+1):
        previous = (best-1)-((best-1-r) % step)
        pair = witness(previous)
        if pair is None:
            raise ArithmeticError(f'smaller separating radix {previous}')
        start, i, j = pair
        if not (0 <= start < t and 0 <= i < j < count and mask[(start+i) % t] and mask[(start+j) % t]
                and (weight*i-weight*j) % previous == 0):
            raise ArithmeticError('invalid colliding indices')
        checks += 1
    return checks


def index_window(n, bits, m):
    """Construct one period of the public local test, starting at the actual lower index."""
    if n < 3 or n % 2 == 0 or bits < 2 or m < 1:
        raise ValueError('expected an odd product, common width of at least two and positive modulus')
    lo, hi = product_band(n, bits)
    w = 4*(1+(n % 4 == 3))*(3 if n % 3 == 2 else 1)
    start = (n+w-hi)//w
    count = max(0, (n-lo)//w+1-start)
    t = m//gcd(m, w)
    sums = allowed(n, m)
    mask = [(n+1-w*(start+i)) % m in sums for i in range(t)]
    return w, start, count, mask


def scan_singleton(n, bits, m):
    """Return a factor and measured work for the public singleton test."""
    w, start, count, mask = index_window(n, bits, m)
    period = len(mask)
    entries = sum(mask)
    survivors = count//period*entries + sum(mask[:count % period])
    work = dict(modulus=m, forced_stride=w, candidate_positions=count, local_x_residues=m,
                table_entries=period, admissible_table_entries=entries, survivors=survivors,
                boundary_square_roots=1, discriminant_square_tests=0, sum=None)
    if survivors != 1:
        return None, work
    offset = next(i for i in range(min(count, period)) if mask[i])
    total = n+1-w*(start+offset)
    work.update(sum=str(total), discriminant_square_tests=1)
    p = factor_from_sum(n, total)
    if p is None or p.bit_length() != bits or (n//p).bit_length() != bits:
        return None, work
    return p, work


def recover_singleton(n, bits, m):
    """Recover factors only when exactly one candidate sum passes, without a digit."""
    p, work = scan_singleton(n, bits, m)
    if p is None:
        return None
    return int(work['sum']), [str(p), str(n//p)]


def measurements(n, bits, m):
    w, start, count, mask = index_window(n, bits, m)
    g, t = w//2, len(mask)
    first = phases(mask)
    actual = minimum(first, count, g)
    every = minimum([0 if i is not None else None for i in first], count, g)
    witness_count = check_minimum(mask, count, g, actual)
    uniform_witnesses = check_minimum(mask, count, g, every, every_start=True)
    size = (count//t)*sum(mask)+sum(mask[:count % t])
    out = dict(modulus=m, forced_stride=w, index_period=t, checked_minimality_witnesses=witness_count,
               checked_uniform_minimality_witnesses=uniform_witnesses,
               candidate_positions=str(count), local_survivors=str(size),
               least_radix=str(actual), least_uniform_radix=str(every),
               radix_difference=every-actual, squared_radix_bits=(actual**2-1).bit_length(),
               uniform_squared_radix_bits=(every**2-1).bit_length())
    if count <= 100:
        indices = [i for i in range(count) if mask[i % t]]
        out['survivor_offsets'] = indices
        out['candidate_sums'] = [n+1-w*(start+i) for i in indices]
        out['digits_at_minimum'] = [(g*(start+i)) % actual for i in indices]
    return out


def direct(mask, count, weight, *, every_start=False):
    """Explicit survivor lists for one window or for every possible starting phase."""
    starts = range(len(mask)) if every_start else (0,)
    lists = [[i for i in range(count) if mask[(start+i) % len(mask)]] for start in starts]
    for m in range(1, weight*(count+1)+1):
        if all(len({(weight*i) % m for i in indices}) == len(indices) for indices in lists):
            return m
    raise ArithmeticError('expected a separating radix')


def validate():
    checked = 0
    for t in range(1, 8):
        for code in range(1 << t):
            mask = [bool(code & (1 << i)) for i in range(t)]
            first = phases(mask)
            uniform_first = [0 if i is not None else None for i in first]
            for count in (1, t, 2*t+3):
                for weight in (2, 4, 6, 12):
                    if minimum(first, count, weight) != direct(mask, count, weight):
                        raise ArithmeticError((mask, count, weight))
                    if minimum(uniform_first, count, weight) != direct(mask, count, weight, every_start=True):
                        raise ArithmeticError(('all starts', mask, count, weight))
                    checked += 1
    return checked


def panel():
    fixture = json.loads(FIXTURE.read_text())
    inputs = [('worked-7294033', 7294033, 12)]
    for label in ('fresh', 'crossed'):
        row = next(r for r in fixture if r['id'] == f'intermediate-totient-{label}-2048')
        inputs.append((label, int(row['n']), row['factor_bits']))
    cases = []
    for label, n, bits in inputs:
        lo, hi = product_band(n, bits)
        wheels = [measurements(n, bits, m) for m in (35, 63, 315)]
        w = wheels[0]['forced_stride']
        cases.append(dict(id=label, n=str(n), factor_bits=bits,
                          lower_deficit_inclusive=str(lo), upper_deficit_exclusive=str(hi),
                          first_absolute_index=str((n+w-hi)//w), wheels=wheels))
    return dict(description='Exact least positive radix for the specified modulus and window. '
                'The uniformly separating comparator uses the same modulus and all starting '
                'phases of the candidate-index progression. Bit lengths price the largest residue '
                'M²−1 (zero bits at M=1). Neither estimate computes a digit.',
                small_oracle_cases=validate(), cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = json.dumps(panel(), indent=2)+'\n'
    if args.check:
        if DATA.read_text() != data:
            raise SystemExit('stored fixed-window panel differs')
        for case in json.loads(WORKED_FIXTURE.read_text()):
            recovered = recover_singleton(int(case['n']), case['factor_bits'], case['modulus'])
            if recovered is None or recovered != (int(case['checks']['sum']), case['factors']):
                raise SystemExit(f'fixed-window recovery failed for {case["id"]}')
        print('Verified the panel, bounded oracle and product-only factor recovery.')
    else:
        DATA.write_text(data)


if __name__ == '__main__':
    main()
