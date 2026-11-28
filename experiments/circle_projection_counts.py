"""Exact small circle censuses and optimal decisions from anonymous repeats."""

import json
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.mixed_ratio_heights import jacobi
from scripts.factor import render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/circle-projection-counts.json'


def census(n, target):
    """Inspect just n and the target. A table of all squared residues counts every lift."""
    squares = Counter(y*y % n for y in range(n))
    levels = Counter()
    marks = 0
    marked_points = 0
    first = None
    for x in range(n):
        difference = (target - x*x) % n
        lifts = squares[difference]
        levels[lifts] += 1
        divisor = gcd(difference, n)
        if divisor != 1:
            marks += 1
            marked_points += lifts
            if first is None and divisor != n:
                first = {'x': x, 'gcd': str(divisor)}
    two = levels[2]
    total = sum(degree*count for degree, count in levels.items())
    symbol = jacobi(target, n)
    row = dict(product=str(n), target=target, jacobi=symbol, circle_points=total,
               x_by_number_of_lifts={str(k): levels[k] for k in (0, 1, 2, 4)},
               equal_x_ordered_pairs=sum(k*k*v for k,v in levels.items()),
               marked_residues=marks, marked_points=marked_points, first_proper_gcd=first)
    if n <= 77:
        direct = Counter(sum((x*x + y*y - target) % n == 0 for y in range(n)) for x in range(n))
        if levels != direct:
            raise ArithmeticError('square table disagrees with direct point enumeration')
    if target == 1:
        collisions = row['equal_x_ordered_pairs']
        if collisions % 4:
            raise ArithmeticError('nonintegral normalized collision count')
        value = collisions // 4
        divisor = None
        if n % 4 == 3:
            divisor = (n-value)//2
        elif value != n:
            prime_sum = (n+4-value)//2
            discriminant = prime_sum**2-4*n
            gap = isqrt(discriminant)
            if gap*gap != discriminant:
                raise ArithmeticError('invalid recovered prime sum')
            divisor = (prime_sum-gap)//2
        if divisor is not None:
            if not 1 < divisor < n or n % divisor:
                raise ArithmeticError('invalid collision count readout')
            row['factors_from_collision_count'] = [str(p) for p in sorted((divisor,n//divisor))]
    if symbol == -1:
        recovered = marks // 2
        if (marks != 2*recovered or not 1 < recovered < n or n % recovered or
                abs(two-recovered) != 1 or marked_points != 2*two):
            raise ArithmeticError('mixed-target count failed its factor and projection identities')
        row['factors_from_mark_count'] = [str(p) for p in sorted((recovered, n//recovered))]
    return row


def words_by_distinct(size, draws):
    """Number of words in each occupancy class. A fresh letter has size-k choices."""
    counts = [1]
    for _ in range(draws):
        after = [0] * (len(counts) + 1)
        for k, count in enumerate(counts):
            after[k] += k*count
            after[k+1] += (size-k)*count
        counts = after
    if sum(counts) != size**draws:
        raise ArithmeticError('occupancy recurrence lost probability mass')
    return counts


def decision(smaller, larger, draws):
    left = words_by_distinct(smaller, draws)
    right = words_by_distinct(larger, draws)
    left_total = smaller**draws
    right_total = larger**draws
    diffs = [r*left_total - l*right_total for l, r in zip(left, right)]
    distance = Fraction(sum(max(0, d) for d in diffs), left_total*right_total)
    positive = [k for k, d in enumerate(diffs) if d > 0]
    if positive and positive != list(range(positive[0], min(draws, larger)+1)):
        raise ArithmeticError('the optimal decision was not a threshold on distinct labels')
    return distance, positive[0] if positive else None


def blind_control():
    """Independently enumerate actual words and discard all information except equality."""
    def hist(size):
        out = Counter()
        for word in product(range(size), repeat=4):
            names = {a:i for i,a in enumerate(dict.fromkeys(word))}
            out[tuple(names[a] for a in word)] += 1
        return out
    left, right = hist(3), hist(4)
    tv = sum(abs(Fraction(left[h], 3**4)-Fraction(right[h], 4**4))
             for h in left.keys() | right.keys()) / 2
    if tv != decision(3,4,4)[0]:
        raise ArithmeticError('anonymous transcripts disagree with occupied-class recurrence')
    return str(tv)


def study():
    targets = [(77, t) for t in (1, 2, 3, 6)] + [(15, 1), (65, 1), (1189, 1), (1147, 1)]
    circles = [census(n, t) for n,t in targets]
    small, large = (r['circle_points'] for r in circles[-2:])
    decisions = []
    for t in (2, 16, 64, 160, 280, 560):
        gap, threshold = decision(small, large, t)
        best = (1+gap)/2
        decisions.append(dict(draws=t, choose_larger_from_distinct=threshold,
                              optimal_correct_parts_per_million=int(best*10**6),
                              tv_parts_per_million=int(gap*10**6)))
    return {'circles': circles, 'blinded_sizes': [small, large],
            'four_draw_brute_force_tv_for_3_and_4': blind_control(),
            'two_draw_tv': str(decision(small, large, 2)[0]), 'blinded_decisions': decisions}


def main():
    observed = study()
    if observed != json.loads(FIXTURE.read_text()):
        raise SystemExit('circle or blind observation census differs from its reviewed fixture')
    with TemporaryDirectory() as tmp:
        for row in observed['circles']:
            for key in ('factors_from_mark_count', 'factors_from_collision_count'):
                if key not in row:
                    continue
                n = int(row['product'])
                path = Path(tmp) / f"CircleCount{n}Target{row['target']}.lean"
                path.write_text(render_certificate(n, list(map(int, row[key]))))
                verify_file(path)
    print(json.dumps(observed))


if __name__ == '__main__':
    main()
