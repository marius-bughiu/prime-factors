"""Compare the first MPQS polynomial for k=1 and k=3 on two fixed public blocks.

Reproduce the data with `python3 -m experiments.multiplier_block_moments --check`.
"""

import argparse
from itertools import combinations_with_replacement
import json
from math import fsum, gcd, log2
from pathlib import Path

from .polynomial_relations import local_roots_table, polynomials, primes_through


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'benchmarks' / 'arbitrary-divisor-window.json'
OUTPUT = ROOT / 'research' / 'multiplier-block-moments.json'
CONTROL_IDS = ('arbitrary-divisor-window-fresh-2048', 'arbitrary-divisor-window-crossed-2048')
SCALE = 256


def first_polynomial(n, k, primes, radius):
    radicand = k * n
    base = []
    for p in primes:
        roots = (0,) if radicand % p == 0 else local_roots_table(p)[radicand % p]
        if roots:
            base.append((1 << len(base), p, roots))
    work = {'coefficient_prime_tests': 0}
    rows = polynomials(radicand, 'square', primes[-1], radius, 1, base, work, original=n)
    row = next(rows, None)
    if row is None:
        raise ValueError(f'no square polynomial for k={k}: {work["outcome"]}')
    a, b, _, _ = row
    c, remainder = divmod(b * b - radicand, a)
    if remainder:
        raise ArithmeticError('invalid MPQS polynomial')
    return a, b, c


def residue_lanes(poly, primes, radius, max_power):
    """List one (relative root, prime power, weight) per root at each level."""
    a, b, c = poly
    linear = 2 * (b - a * radius)
    constant = (a * radius - 2 * b) * radius + c
    lanes = []
    checks = 0
    for p in primes:
        weight = (p**SCALE).bit_length() - 1
        q = p
        while q <= max_power:
            qa, qb, qc = a % q, linear % q, constant % q
            for r in range(q):
                if ((qa * r + qb) * r + qc) % q == 0:
                    lanes.append((r, q, weight))
            checks += q
            q *= p
    return lanes, checks


def lane_count(r, modulus, width):
    turns, tail = divmod(width, modulus)
    return turns + int(r < tail)


def intersection_count(left, right, width):
    """One generalized CRT, including incompatible or nested prime powers."""
    a, p, _ = left
    b, q, _ = right
    g = gcd(p, q)
    difference = b - a
    if difference % g:
        return 0
    reduced = q // g
    digit = (difference // g * pow(p // g, -1, reduced)) % reduced
    return lane_count(a + p * digit, p * reduced, width)


def moments(lanes, width):
    first = sum(w * lane_count(r, m, width) for r, m, w in lanes)
    second = 0
    for i, j in combinations_with_replacement(range(len(lanes)), 2):
        left, right = lanes[i], lanes[j]
        symmetry = 1 if i == j else 2
        second += symmetry * left[2] * right[2] * intersection_count(left, right, width)
    return first, second


def direct_divisions(poly, primes, radius, max_power):
    """Independently evaluate at every signed site and divide by actual primes."""
    a, b, c = poly
    weights = {p: (p**SCALE).bit_length() - 1 for p in primes}
    scores, values = [], []
    smooth = 0
    for x in range(-radius, radius + 1):
        value = abs(a * x * x + 2 * b * x + c)
        if not value:
            raise ValueError('the logarithmic price requires nonzero polynomial values')
        values.append(value)
        cofactor, gain = value, 0
        for p in primes:
            power = 1
            while cofactor % p == 0:
                cofactor //= p
                power *= p
                if power <= max_power:
                    gain += weights[p]
        scores.append(gain)
        smooth += int(cofactor == 1)
    return values, scores, smooth


def compare(n, *, k=3, radius=512, prime_bound=97, max_power=4096):
    if n <= 1 or k < 1 or not k % 2 or gcd(n, k) != 1:
        raise ValueError('expected n>1 and a positive odd multiplier coprime to n')
    if radius < 1 or prime_bound < 2 or max_power < 2:
        raise ValueError('expected a positive radius and cutoffs at least two')
    primes = primes_through(prime_bound)
    width = 2 * radius + 1
    all_lanes, samples, runs = [], [], []
    for multiplier, sign in ((1, -1), (k, 1)):
        poly = first_polynomial(n, multiplier, primes, radius)
        roots, checks = residue_lanes(poly, primes, radius, max_power)
        all_lanes.extend((r, m, sign * w) for r, m, w in roots)
        values, scores, smooth = direct_divisions(poly, primes, radius, max_power)
        samples.append((values, scores))
        runs.append({'multiplier': multiplier, 'root_lanes': len(roots),
                     'residues_tested': checks, 'smooth_rows': smooth})
    first, second = moments(all_lanes, width)
    (baseline_values, baseline_scores), (new_values, new_scores) = samples
    gain = [new - old for new, old in zip(new_scores, baseline_scores)]
    if (first, second) != (sum(gain), sum(delta**2 for delta in gain)):
        raise ArithmeticError('CRT moments differ from direct prime valuations')

    # With the common denominator SCALE, both strict price comparisons are integers.
    # The classical price is half log2(k), while actual prices use |Qk(x)| / |Q1(x)|.
    k_power = k ** (SCALE // 2)
    classical_wins = sum(delta >= 0 and (1 << max(0, delta)) > k_power for delta in gain)
    actual_wins = sum((new**SCALE << max(0, -delta)) < (old**SCALE << max(0, delta))
                      for old, new, delta in zip(baseline_values, new_values, gain))
    mean_price = fsum(log2(new) - log2(old) for old, new in zip(baseline_values, new_values)) / width
    raw_mean = first / (width * SCALE)
    return {
        'input_bits': n.bit_length(), 'compared': runs, 'direct_positions_per_polynomial': width,
        'pairwise_crt_checks': len(all_lanes) * (len(all_lanes) + 1) // 2,
        'gain_sum': first, 'squared_gain_sum': second,
        'classical_price_wins': classical_wins, 'actual_price_wins': actual_wins,
        'mean_classical_price_bits': round(log2(k) / 2, 8),
        'mean_actual_price_bits': round(mean_price, 8),
        'net_mean_classical_bits': round(raw_mean - log2(k) / 2, 8),
        'net_mean_actual_bits': round(raw_mean - mean_price, 8),
    }


def fixed_controls():
    products = {case['id']: int(case['n']) for case in json.loads(INPUT.read_text()) if case['id'] in CONTROL_IDS}
    return {
        'source': str(INPUT.relative_to(ROOT)), 'radius': 512, 'prime_bound': 97,
        'prime_power_bound': 4096, 'weight_scale': SCALE,
        'controls': [{'id': name, **compare(products[name])} for name in CONTROL_IDS],
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='regenerate and compare the recorded results')
    args = parser.parse_args()
    recorded = fixed_controls()
    if args.check:
        if json.loads(OUTPUT.read_text()) != recorded:
            raise SystemExit('the registered controls differ from the recorded result')
        print('Verified both control blocks and their direct valuation checks.')
    else:
        print(json.dumps(recorded, indent=2))
