"""Find the least span of a four-unit-coefficient identity in measured Jacobi moments."""

from collections import defaultdict
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-four-width.json'
PROJECTION_ROWS = 4


def read_factors(n, total):
    discriminant = total*total - 4*n
    if discriminant < 0:
        return None
    gap = isqrt(discriminant)
    if gap*gap != discriminant or (total-gap) % 2:
        return None
    small, large = (total-gap)//2, (total+gap)//2
    if 1 < small <= large and small*large == n:
        return [small, large]
    return None


def near_ratio_square(n):
    """One independent square test for a pair satisfying 3p−2q = 1 or −1."""
    target = 24*n + 1
    root = isqrt(target)
    if root*root == target:
        for sign in (1, -1):
            if (root+sign) % 6 == 0 and (root-sign) % 4 == 0:
                small, large = (root+sign)//6, (root-sign)//4
                if 1 < small <= large and small*large == n:
                    return dict(square=True, root=root, sign=sign, factors=[small, large])
    return dict(square=root*root == target, root=root, sign=None, factors=None)


def even_moments(n, count):
    signs = [jacobi(t*t-4, n) for t in range(n)]
    squares = [t*t % n for t in range(n)]
    terms = signs
    moments = []
    for _ in range(count):
        terms = [square*term % n for square, term in zip(squares, terms)]
        moments.append(sum(terms) % n)
    return moments


def coefficient_columns(n, cap, moments):
    """Eliminate the constant coefficient using the equation at starting position zero."""
    inverse = pow(moments[0], -1, n)
    columns = []
    for offset in range(cap+1):
        column = [(moments[start+offset] - inverse*moments[offset]*moments[start]) % n
                  for start in range(1, n)]
        columns.append(column)
    return inverse, columns


def minimum_width(n, cap):
    """Search spans in ascending order; the input is a product of distinct primes above seven."""
    if n < 11 or n % 2 == 0 or cap < 3:
        raise ValueError('expected an odd semiprime and a span cap of at least three')
    moments = even_moments(n, n+cap)
    inverse, columns = coefficient_columns(n, cap, moments)
    tables = {}
    for offset in range(1, cap):
        table = defaultdict(list)
        for coefficient in range(1, n):
            key = tuple(coefficient*entry % n for entry in columns[offset][:PROJECTION_ROWS])
            table[key].append(coefficient)
        tables[offset] = table

    work = dict(jacobi_signs=n, measured_even_moments=len(moments),
                weighted_term_updates=n*len(moments), support_triples=0, hash_lookups=0,
                key_matches=0, full_candidate_checks=0, coefficient_gcds=0,
                table_coefficients=(cap-1)*(n-1), first_proper_gcd=None)
    for span in range(3, cap+1):
        target = columns[span]
        for first, second in combinations(range(1, span), 2):
            work['support_triples'] += 1
            for a in range(1, n):
                key = tuple((-y-a*x) % n for x, y in
                            zip(columns[first][:PROJECTION_ROWS], target[:PROJECTION_ROWS]))
                work['hash_lookups'] += 1
                for b in tables[second].get(key, ()):
                    work['key_matches'] += 1
                    constant = -(moments[span] + a*moments[first] + b*moments[second])*inverse % n
                    if not constant:
                        continue
                    work['full_candidate_checks'] += 1
                    if any((y+a*x+b*z) % n for x, z, y in zip(columns[first], columns[second], target)):
                        continue
                    for coefficient in (constant, a, b):
                        work['coefficient_gcds'] += 1
                        divisor = gcd(coefficient, n)
                        if divisor != 1:
                            if work['first_proper_gcd'] is None:
                                work['first_proper_gcd'] = dict(span=span, coefficient=coefficient,
                                                                factor=divisor)
                            break
                    else:
                        totals = [2*span+2]
                        if span % 2 == 0:
                            totals.append(5*span//2+2)
                        pairs = [pair for total in totals if (pair := read_factors(n, total)) is not None]
                        return dict(n=n, span=span, offsets=[0, first, second, span],
                                    coefficients=[constant, a, b, 1], sum_candidates=totals,
                                    factors=pairs, **work)
    return dict(n=n, span=None, factors=[], **work)


def main():
    panel = json.loads(FIXTURE.read_text())
    cap = panel['span_cap']
    for case in panel['cases']:
        n = int(case['n'])
        measured = minimum_width(n, cap)
        square = near_ratio_square(n)
        p, q = map(int, case['factors'])
        a, b = (p-1)//2, (q-1)//2
        assert 4 < a < b < 2*a and p*q == n
        expected_span = 2*a if 2*b == 3*a else a+b
        assert measured['span'] == case['span'] == expected_span
        assert measured['factors'] == [[p, q]]
        assert measured['first_proper_gcd']['factor'] == q
        assert measured['first_proper_gcd']['span'] == case['first_gcd_span'] < measured['span']
        assert square['sign'] == case['square_sign']
        assert square['factors'] == ([p, q] if case['square_sign'] is not None else None)
        print(json.dumps(dict(**measured, square_comparison=square)))


if __name__ == '__main__':
    main()
