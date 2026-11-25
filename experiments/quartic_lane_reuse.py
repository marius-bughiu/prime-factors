"""Check how many full dyadic remainder classes a single fixed quartic covers."""
import json
from collections import Counter
from math import comb
from pathlib import Path

from .gap_newton_lanes import dickson_basis, gap_coordinates
from .projected_quartic_levels import projected_relation, signed_class

ROOT = Path(__file__).resolve().parents[1]


def possible_centers(leading, radix, u):
    """The two-lane divisibility theorem bounds the common residue prefix."""
    if not leading:
        return range(1, radix, 2)
    content = (abs(leading) & -abs(leading)).bit_length()-1
    free_bits = min(radix.bit_length()-2, max(0, (content-2)//2))
    step = radix >> free_bits
    return range(u % step, radix, step)


def on_lane(full, radix, u):
    """Five exact evaluations determine divisibility for every integer in the lane."""
    modulus = 8*radix**4
    for j in range(5):
        x = u+radix*j
        value = 0
        for coefficient in reversed(full):
            value = value*x+coefficient
        if value % modulus:
            return False
    return True


def excludes_all_other_points(full, radix, u):
    """Apply the translated coefficient criterion for an individual root."""
    leading = full[-1]
    if not leading:
        return False
    content = abs(leading) & -abs(leading)
    half = radix//2
    shifted = [sum(full[j]*comb(j, i)*u**(j-i) for j in range(i, 5)) for i in range(4)]
    return (8*radix**4 % (2*content*half**4) == 0
            and all(value % (2*content*half**(4-i)) == 0 for i, value in enumerate(shifted)))


def large_controls():
    controls = json.loads((ROOT/'research/projected-level-sieve.json').read_text())['controls']
    results = []
    for recorded in controls:
        row = recorded['result']
        n, radix, u = int(row['n']), int(row['radix']), int(row['u'])
        full = [int(v)*n**max(2-i, 0) for i, v in enumerate(row['trace'])]
        candidates = possible_centers(full[-1], radix, u)
        assert len(candidates) == 1 and on_lane(full, radix, u)
        assert excludes_all_other_points(full, radix, u)
        results.append([recorded['source'], radix.bit_length()-1,
                        (abs(full[-1]) & -abs(full[-1])).bit_length()-1])
    return results


def small_holdout():
    samples = json.loads((ROOT/'research/quartic-lane-holdout.json').read_text())['rows']
    totals = {}
    for radix in (32, 64):
        counts = Counter()
        for sample in samples:
            n = int(sample['n'])
            basis, scales = dickson_basis(n, 2)
            for u in range(1, radix, 2):
                if u != min(signed_class(n, radix, u)):
                    continue
                _, full, *_ = projected_relation(n, radix, u, lambda w: gap_coordinates(w, basis),
                                                 scales, Counter())
                candidates = possible_centers(full[-1], radix, u)
                covered = {v for v in candidates if on_lane(full, radix, v)}
                exhaustive = {v for v in range(1, radix, 2) if on_lane(full, radix, v)}
                assert u in covered and covered == exhaustive
                extra = {min(signed_class(n, radix, v)) for v in covered} - {u}
                counts['queries'] += 1
                counts['degree_below_four'] += int(full[-1] == 0)
                counts['multiple_centers'] += int(len(covered) > 1)
                counts['extra_orbits'] += len(extra)
        totals[radix] = counts
    return totals


if __name__ == '__main__':
    print(json.dumps({'large': large_controls(), 'holdout': small_holdout()}, indent=2))
