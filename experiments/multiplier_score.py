"""Certify the full primitive-norm score distribution on a finite CRT sign space."""

from argparse import ArgumentParser
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import isqrt, lcm, prod

from .sieve_forecast import primes_through


def unit_log_bounds(x):
    """Rational bounds for log(x), 1 <= x <= 2, from the atanh series."""
    y = (x - 1) / (x + 1)
    power = y
    total = F(0)
    for j in range(18):
        total += 2 * power / (2*j + 1)
        power *= y*y
    return total, total + 2*power / (37*(1-y*y))


def log_bounds(n):
    """Enclose log(n) at a common fixed-point scale after range reduction."""
    e = n.bit_length() - 1
    a, b = unit_log_bounds(F(2))
    c, d = unit_log_bounds(F(n, 2**e))
    return e*a + c, e*b + d


SCALE = 2**48


def weighted(logs, weight):
    a, b = (weight*t*SCALE for t in logs)
    lo, hi = (a, b) if weight >= 0 else (b, a)
    return lo.numerator//lo.denominator, -((-hi.numerator)//hi.denominator)


def dyadic(residue):
    return F({1: 4, 3: 1, 5: 2, 7: 1}[residue % 8], 3)


def signed_symbol(m, p):
    sign = pow(m, (p-1)//2, p)
    return -1 if sign == p-1 else sign


def finite_menu(cutoff=31, max_multiplier=63):
    if cutoff < 2 or max_multiplier < 1:
        raise ValueError('need a positive multiplier bound and cutoff at least two')
    primes = [p for p in primes_through(cutoff) if p != 2]
    choices = [m for m in range(1, max_multiplier+1, 2)
               if all(m % (d*d) for d in range(3, isqrt(m)+1, 2))]
    tables = {}
    logs = {p: log_bounds(p) for p in (2, *primes)}
    for m in choices:
        penalty = weighted(log_bounds(m), F(-1, 2))
        starts = []
        for u in (1, 3, 5, 7):
            a, b = weighted(logs[2], dyadic(m*u))
            starts.append((penalty[0]+a, penalty[1]+b))
        columns = []
        for p in primes:
            k = signed_symbol(m, p)
            if k == 0:
                val = weighted(logs[p], F(1, p+1))
                columns.append((val, val))
            else:
                split = weighted(logs[p], F(2*p, p*p-1))
                columns.append((split, (0, 0)) if k == -1 else ((0, 0), split))
        tables[m] = starts, columns

    winners = Counter()
    lower_total = upper_total = lower_max = upper_max = 0
    for word in product((0, 1), repeat=len(primes)):
        partial = {}
        for m, (_, columns) in tables.items():
            values = [column[bit] for column, bit in zip(columns, word)]
            partial[m] = sum(a for a, _ in values), sum(b for _, b in values)
        for i in range(4):
            scores = {}
            for m, (a, b) in partial.items():
                c, d = tables[m][0][i]
                scores[m] = a+c, b+d
            winner = max(scores, key=lambda m: scores[m][0])
            competitors = [upper for m, (_, upper) in scores.items() if m != winner]
            if competitors and scores[winner][0] <= max(competitors):
                raise ArithmeticError('increase the precision to certify this comparison')
            winners[winner] += 1
            lo, hi = scores[winner]
            gain_low = max(0, lo-scores[1][1])
            gain_high = 0 if winner == 1 else hi-scores[1][0]
            lower_total += gain_low
            upper_total += gain_high
            lower_max = max(lower_max, gain_low)
            upper_max = max(upper_max, gain_high)
    words = sum(winners.values())
    log2_low, log2_high = logs[2]
    return dict(words=words, candidate_count=len(choices), winners=dict(sorted(winners.items())),
                mean_bits=(F(lower_total, words*SCALE)/log2_high, F(upper_total, words*SCALE)/log2_low),
                max_bits=(F(lower_max, SCALE)/log2_high, F(upper_max, SCALE)/log2_low))


def half_scores(columns):
    """Index local score sums by the sign bits of this half word."""
    totals = [0]
    for absent, present in columns:
        totals = [x + absent for x in totals] + [x + present for x in totals]
    return totals


def quantized_menu(cutoff=97, max_multiplier=63):
    """Count winners for the exact floor(256 log2) rule used in the holdout."""
    if cutoff < 2 or max_multiplier < 1:
        raise ValueError('need a positive multiplier bound and cutoff at least two')
    primes = [p for p in primes_through(cutoff) if p != 2]
    choices = [m for m in range(1, max_multiplier+1, 2)
               if all(m % (d*d) for d in range(3, isqrt(m)+1, 2))]
    denominator = lcm(2, 3, *(p*p-1 for p in primes))
    split = len(primes)//2
    lefts, rights, offsets, coefficients = {}, {}, {}, {}
    for m in choices:
        weight = (m**256).bit_length()-1
        offsets[m] = [int(dyadic(m*u)*256*denominator)-weight*(denominator//2)
                      for u in (1,3,5,7)]
        columns = []
        for p in primes:
            weight = (p**256).bit_length()-1
            symbol = signed_symbol(m, p)
            if symbol == 0:
                v = weight*(denominator//(p+1))
                columns.append((v, v))
            else:
                v = 2*p*weight*(denominator//(p*p-1))
                columns.append((v, 0) if symbol == -1 else (0, v))
        lefts[m] = half_scores(columns[:split])
        rights[m] = half_scores(columns[split:])
        coefficients[m] = [v-u for u, v in columns[split:]]

    size = len(rights[1])
    every_right = (1 << size)-1
    right_bits = [sum(1 << j for j in range(size) if (j >> i) & 1)
                  for i in range(len(primes)-split)]
    popcount = getattr(int, 'bit_count', lambda n: bin(n).count('1'))
    winners = Counter()
    total_gain = 0
    for m in choices:
        masks = [[every_right]*len(lefts[m]) for _ in range(4)]
        for rival in choices:
            if rival == m:
                continue
            # One sorted list answers every left half and dyadic residue.
            order = sorted((v-u, i) for i, (v, u) in enumerate(zip(rights[m], rights[rival])))
            values = [v for v, _ in order]
            lower = [0]
            for _, i in order:
                lower.append(lower[-1] | (1 << i))
            loser_count = bisect_left if m < rival else bisect_right
            differences = [v-u for v, u in zip(lefts[m], lefts[rival])]
            for u, row in enumerate(masks):
                threshold = offsets[rival][u] - offsets[m][u]
                for i, d in enumerate(differences):
                    if row[i]:
                        row[i] &= ~lower[loser_count(values, threshold-d)]

        # Sum the winning advantage by counting signs under each surviving mask.
        for u, row in enumerate(masks):
            intercept = offsets[m][u]-offsets[1][u] + rights[m][0]-rights[1][0]
            for i, mask in enumerate(row):
                if not mask:
                    continue
                n = popcount(mask)
                winners[m] += n
                total_gain += n*(intercept+lefts[m][i]-lefts[1][i])
                for a, b, ones in zip(coefficients[m], coefficients[1], right_bits):
                    total_gain += (a-b)*popcount(mask & ones)
    words = 4 * 2**len(primes)
    if sum(winners.values()) != words:
        raise ArithmeticError('winning masks do not partition the sign words')
    return dict(words=words, candidate_count=len(choices), winners=dict(sorted(winners.items())),
                mean_bits=F(total_gain, words*256*denominator))


def variance_certificate():
    """Bound the sum of squared odd-prime weights, including the infinite tail."""
    bound = 8192
    total = 0
    for p in primes_through(bound):
        if p != 2:
            _, high = weighted(log_bounds(p), F(p, p*p-1))
            total += high*high
    _, log_bound = log_bounds(bound)
    tail = F(bound**2, bound**2-1)**2 * (log_bound**2 + 2*log_bound + 2) / bound
    variance = F(total, SCALE**2) + tail
    assert variance < F(69, 100)
    log_mgf = log_bounds(27)[1] - log_bounds(10)[0] + F(9, 2)*variance
    assert log_mgf < 6*log_bounds(2)[0]
    return variance


def all_split_certificate():
    """Verify the cap on all-split multipliers and the finite prime-population bound."""
    primes = [p for p in primes_through(727) if p != 2]
    assert len(primes) == 128
    max_odd = sum(F(2*p, p*p-1) * log_bounds(p)[1] for p in primes)
    log_two_lower, _ = log_bounds(2)
    # 1 bit is the greatest possible dyadic improvement.
    assert max_odd / log_two_lower < F(29, 2)
    X = 2**1023
    modulus = prod(primes)
    phi = prod(p-1 for p in primes)
    inflation = F(1511,1000)*710/F(22,100)**2 * (1+F(modulus,X))*F(phi,modulus)
    bound = inflation * F(2**30, 2**128)
    assert bound < F(1, 2**86)
    return bound


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int)
    parser.add_argument('--quantized', action='store_true', help='use the holdout score and a split sign table')
    parser.add_argument('--max-multiplier', type=int, default=63)
    args = parser.parse_args()
    if args.quantized:
        results = quantized_menu(97 if args.cutoff is None else args.cutoff, args.max_multiplier)
        print('Sign words:', results['words'], 'candidates:', results['candidate_count'])
        print('Winning multiplier -> sign word count:', results['winners'])
        print('Mean bits:', results['mean_bits'], float(results['mean_bits']))
        raise SystemExit(0)
    results = finite_menu(31 if args.cutoff is None else args.cutoff, args.max_multiplier)
    print('Sign words:', results['words'], 'candidates:', results['candidate_count'])
    print('Winning multiplier -> sign word count:', results['winners'])
    for stat in ('mean_bits', 'max_bits'):
        lo, hi = results[stat]
        print(stat, float(lo), float(hi))
    print('Infinite variance sum, upper bound:', float(variance_certificate()))
    print('Full-size all-split probability, upper bound:', float(all_split_certificate()))
