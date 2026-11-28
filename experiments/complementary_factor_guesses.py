"""Enumerate all small unit pairs and compare sum labels with complementary factor orbits."""

from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd

if __package__:
    from .joint_sum_guess_counts import mean_rank
else:
    from joint_sum_guess_counts import mean_rank


def compare(modulus):
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    totals = [Fraction(0) for _ in range(4)]
    for n in units:
        sums = Counter()
        orbits = Counter()
        for a in units:
            b = n * pow(a, -1, modulus) % modulus
            sums[(a + b) % modulus] += 1
            orbits[tuple(sorted((a, b)))] += 1
        for offset, labels in ((0, sums), (2, orbits)):
            _, _, best = mean_rank(Counter(labels.values()))
            totals[offset] += best
            totals[offset + 1] += Fraction(len(labels) + 1, 2)
    conditional_means = tuple(value / len(units) for value in totals)
    _, _, optimal, random = conditional_means
    kernel = sum(a * a % modulus == 1 for a in units)
    expected_saving = Fraction(len(units) - kernel, 4 * len(units))
    if random - optimal != expected_saving:
        raise AssertionError('Orbit ranks disagree with the finite-group calculation')
    return conditional_means


def with_supplied_sum(modulus):
    """Average over all ordered pairs, revealing their true sum remainder first."""
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    pooled = Fraction(0)
    for n in units:
        fibers = defaultdict(Counter)
        fixed = 0
        for a in units:
            b = n * pow(a, -1, modulus) % modulus
            fibers[(a + b) % modulus][tuple(sorted((a, b)))] += 1
            fixed += a == b
        weighted_cost = Fraction(0)
        second = 0
        for orbits in fibers.values():
            _, pairs, best = mean_rank(Counter(orbits.values()))
            weighted_cost += pairs * best
            second += pairs**2
        actual = weighted_cost / len(units)
        if modulus % 2 and actual != Fraction(1, 2) + Fraction(second + fixed, 4 * len(units)):
            raise AssertionError('Post-clue mean disagrees with the sum-weight formula')
        pooled += actual
    return pooled / len(units)


def merge_two_sums(modulus, product, first, second):
    """Find both optimal mean ranks directly and compare their difference to the formula."""
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    separate = defaultdict(Counter)
    merged = defaultdict(Counter)
    for a in units:
        b = product * pow(a, -1, modulus) % modulus
        pair = tuple(sorted((a, b)))
        label = (a + b) % modulus
        separate[label][pair] += 1
        merged[first if label == second else label][pair] += 1

    def average(groups):
        total = Fraction(0)
        for pairs in groups.values():
            _, mass, best = mean_rank(Counter(pairs.values()))
            total += mass * best
        return total / len(units)

    left, right = separate[first], separate[second]
    single_left = sum(a == b for a, b in left)
    single_right = sum(a == b for a, b in right)
    penalty = Fraction(sum(left.values()) * sum(right.values()) + single_left * single_right,
                       2 * len(units))
    full, compressed = average(separate), average(merged)
    if compressed - full != penalty:
        raise AssertionError('Merging the sum reports disagrees with the predicted cost')
    return full, compressed


def advised_pair(modulus, p, q, bits):
    """Give a helper the hidden pair and check its position in the selected list."""
    product = p * q % modulus
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    pairs = {tuple(sorted((a, product * pow(a, -1, modulus) % modulus))) for a in units}
    order = sorted(pairs, key=lambda pair: (pair[0] == pair[1], pair))
    target = tuple(sorted((p % modulus, q % modulus)))
    index = order.index(target)
    size = 2**bits
    message = index % size
    selected = order[message::size]
    guesses = selected.index(target) + 1
    if guesses != index // size + 1:
        raise AssertionError('Filtered position disagrees with the rank formula')
    return index + 1, message, guesses


if __name__ == '__main__':
    for m in (25, 175):
        sum_opt, sum_random, orbit_opt, orbit_random = compare(m)
        print(f'{m=}: sum best={sum_opt} random={sum_random}; '
              f'factor orbit best={orbit_opt} random={orbit_random} saved={orbit_random-orbit_opt}; '
              f'with the true sum supplied={with_supplied_sum(m)}')
    original, message, guesses = advised_pair(25, 701, 751, 2)
    print(f'701 × 751 modulo 25: original rank={original}, '
          f'two-bit message={message:02b}, advised rank={guesses}')
    full, compressed = merge_two_sums(25, 1, 2, 23)
    print(f'Product 1 modulo 25, reporting sums 2 and 23 together: '
          f'full mean={full}, compressed mean={compressed}')
