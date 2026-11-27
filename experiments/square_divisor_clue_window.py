"""Compare disclosed clues and public sum remainders on one preselected 20-bit prime pair."""

import json
from collections import Counter
from math import isqrt, lcm, prod
from pathlib import Path
from random import Random

from experiments.small_factorization import factor_small
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/square-divisor-clue-window.json'
SEED = 20261127
BITS = 20
SIGNS = ('--', '++', '-+', '+-')


def draw_pair():
    primes = [p for p in primes_through(2**BITS-1) if p.bit_length() == BITS]
    # No rejection by product width or by any property of the drawn neighbors.
    p, q = sorted(Random(SEED).sample(primes, 2))
    return len(primes), p, q


def disclosed_clues(p, q):
    """Use the known factors to disclose the maximal square divisor on each side."""
    exponents = {label: Counter(factor_small(value)) for label, value in
                 (('p-', p-1), ('p+', p+1), ('q-', q-1), ('q+', q+1))}
    roots = {}
    for signs in SIGNS:
        powers = exponents['p'+signs[0]] + exponents['q'+signs[1]]
        roots[signs] = prod(prime**(power//2) for prime, power in powers.items())
    factorizations = {label: [list(pair) for pair in sorted(powers.items())]
                      for label, powers in exponents.items()}
    return roots, factorizations


def sum_progression(n, factor_bits):
    low, high = isqrt(4*n-1)+1, isqrt(9*n//2)
    if factor_bits is not None:
        smallest, largest = 2**(factor_bits-1), 2**factor_bits-1
        high = min(high, smallest+n//smallest, largest+n//largest)
    first = low + (n+1-low) % 4
    return low, high, range(first, high+1, 4)


def count_from_clues(n, roots, *, factor_bits=None):
    """Use the public product, four labelled roots and optional advertised width."""
    low, high, mod4_sums = sum_progression(n, factor_bits)
    moduli = {signs: root**2 for signs, root in roots.items()}
    linear_sums = [s for s in mod4_sums
                   if (s-n-1) % moduli['--'] == 0 and (s+n+1) % moduli['++'] == 0]
    gap_center_squared = (n-1)**2
    survivors = []
    exact = []
    for s in linear_sums:
        discriminant = s*s-4*n
        if any((discriminant-gap_center_squared) % moduli[signs] for signs in ('-+', '+-')):
            continue
        survivors.append(s)
        gap = isqrt(discriminant)
        if gap*gap == discriminant:
            exact.append(s)
    return dict(low=low, high=high, all_integers=high-low+1, mod_four_residue=(n+1)%4,
                mod_four_sums=len(mod4_sums), both_sum_congruences=len(linear_sums),
                all_four_congruences=len(survivors), square_discriminants=len(exact),
                exact_sums=exact), set(survivors)


def public_remainders(n, factor_bits):
    """Replay the thirteen small-prime checks in the Lean control."""
    _, _, candidates = sum_progression(n, factor_bits)
    stages = [len(candidates)]
    primes = [prime for prime in primes_through(43) if prime != 2]
    for prime in primes:
        squares = {x*x % prime for x in range(prime)}
        allowed = {s for s in range(prime) if (s*s-4*n) % prime in squares}
        candidates = [s for s in candidates if s % prime in allowed]
        stages.append(len(candidates))
    pairs = []
    for s in candidates:
        gap = isqrt(s*s-4*n)
        if gap*gap == s*s-4*n:
            pairs.append([str((s-gap)//2), str((s+gap)//2)])
    return dict(primes=primes, stage_counts=stages, residue_lookups=sum(stages[:-1]),
                surviving_sums=candidates, recovered_pairs=pairs)


def retrospective(true_sum, public, survivors, roots):
    """The actual sum is used here to identify a subset of the public survivors."""
    joint = lcm(4, *(y*y for y in roots.values()))
    low, high = public['low'], public['high']
    first = low + (true_sum-low) % joint
    points = range(first, high+1, joint)
    assert true_sum in points and all(s in survivors for s in points)
    return dict(joint_modulus=joint, true_sum_residue=true_sum % joint, true_class_sums=len(points))


def measure():
    population, p, q = draw_pair()
    n = p*q
    roots, factorizations = disclosed_clues(p, q)
    public, survivors = count_from_clues(n, roots)
    exact_width, _ = count_from_clues(n, roots, factor_bits=BITS)
    comparison = retrospective(p+q, public, survivors, roots)
    assert public['exact_sums'] == exact_width['exact_sums'] == [p+q]
    return dict(prime_bits=BITS, seed=SEED, prime_population=population,
                factors=[str(p), str(q)], n=str(n), product_bits=n.bit_length(),
                neighbor_factorizations=factorizations, largest_square_roots=roots,
                public_counts=public, width_counts=exact_width, retrospective=comparison,
                public_remainders=public_remainders(n, BITS))


def main():
    measured = measure()
    expected = json.loads(FIXTURE.read_text())['expected']
    assert measured == expected, (measured, expected)
    print(json.dumps(measured))


if __name__ == '__main__':
    main()
