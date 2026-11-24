"""Measure one midpoint per lifted root on prime pairs X <= p < q <= 2X.

Run, for example, python3 experiments/gap_coverage.py 4000 --band 15.
The default uses all pairs. --sample K uses K pairs uniformly without replacement.
The searches receive only the product and public budgets. Prime-pair information
checks their results afterwards. Each search is compared with consecutive Fermat
tests at its maximum cap and at the exact number of square tests it used per N.
"""

import argparse
import json
from dataclasses import dataclass
from itertools import combinations
from math import isqrt
from random import Random
from time import perf_counter

if __package__:
    from .gap_stride import search as fixed_five_search
else:
    from gap_stride import search as fixed_five_search


def primes_through(limit):
    flags = bytearray([1]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if flags[p]]


@dataclass
class Run:
    factor: int = 0
    squares: int = 0
    powers: int = 0
    inversions: int = 0
    lift_trials: int = 0


def square_factor(n, h):
    d = h * h - n
    g = isqrt(d)
    return h - g if g * g == d else 0


def fermat(n, cap):
    first = isqrt(n - 1) + 1
    for i in range(cap):
        factor = square_factor(n, first + i)
        if factor > 1:
            return Run(factor, i + 1)
    return Run(squares=cap)


def fixed(n, exponent):
    found = fixed_five_search(n, exponent, 1)
    return Run(found["factor"] or 0, found["square_tests"], lift_trials=found["lift_tests"])


def band(n, primes):
    """All supplied primes must be 3 mod 4 and coprime to n."""
    first = isqrt(n - 1) + 1
    run = Run()
    for ell in primes:
        s = pow(n, (ell + 1) // 4, ell)
        run.powers += 1
        if s * s % ell != n % ell:
            continue
        # One lifted root gives its negative as the other root modulo ell².
        run.inversions += 1
        run.lift_trials += 1
        digit = (n - s * s) // ell * pow(2 * s, -1, ell) % ell
        root = s + ell * digit
        modulus = ell * ell
        for offset in sorted(((root - first) % modulus, (-root - first) % modulus)):
            run.squares += 1
            factor = square_factor(n, first + offset)
            if factor > 1:
                run.factor = factor
                return run
    return run


def compare(pairs, method, cap, strides, fermat_multiple):
    trials = hits = squares = powers = inversions = lifts = failures_squares = 0
    fermat_hits = fermat_squares = matched_hits = matched_squares = 0
    beyond_fermat = fermat_only = 0
    method_time = fermat_time = 0.0
    for p, q in pairs:
        trials += 1
        n = p * q
        start = perf_counter()
        run = method(n)
        method_time += perf_counter() - start
        start = perf_counter()
        plain = fermat(n, fermat_multiple * cap)
        fermat_time += perf_counter() - start

        distance = (p + q) // 2 - (isqrt(n - 1) + 1)
        half_gap = (q - p) // 2
        covered = any(half_gap % m == 0 and distance < m * m for m in strides)
        if run.squares > cap or run.factor != (p if covered else 0):
            raise AssertionError((n, run, distance, "lifted-root coverage"))
        if plain.factor != (p if distance < fermat_multiple * cap else 0):
            raise AssertionError((n, plain, distance, "Fermat coverage"))
        hits += bool(run.factor)
        squares += run.squares
        powers += run.powers
        inversions += run.inversions
        lifts += run.lift_trials
        failures_squares += 0 if run.factor else run.squares
        fermat_hits += bool(plain.factor)
        fermat_squares += plain.squares
        beyond_fermat += bool(run.factor and not plain.factor)
        fermat_only += bool(plain.factor and not run.factor)
        # Reuse the consecutive scan already performed at the larger cap.
        matched_hits += bool(plain.factor and plain.squares <= run.squares)
        matched_squares += min(plain.squares, run.squares)
    return dict(square_cap=cap, fermat_cap=fermat_multiple * cap,
                hits=hits, misses=trials - hits, squares=squares,
                squares_on_misses=failures_squares, modular_powers=powers,
                modular_inverses=inversions, lift_trials=lifts,
                fermat_hits=fermat_hits, fermat_squares=fermat_squares,
                lifted_only=beyond_fermat, fermat_only=fermat_only,
                matched_fermat_hits=matched_hits, matched_fermat_squares=matched_squares,
                search_seconds=round(method_time, 4), fermat_seconds=round(fermat_time, 4))


def prime_pairs(primes, ranks):
    if ranks is None:
        yield from combinations(primes, 2)
        return
    for rank in ranks:
        # The j-th group contains pairs (0,j), ..., (j-1,j).
        j = (1 + isqrt(1 + 8 * rank)) // 2
        i = rank - j * (j - 1) // 2
        yield primes[i], primes[j]


def measure(x, y, sample=None, seed=20261124, fermat_multiple=1):
    if x < 16 or y < 2 or y * y >= x:
        raise ValueError("expected X >= 16 and 2 <= Y < sqrt(X)")
    if fermat_multiple < 1:
        raise ValueError("the Fermat comparison budget multiplier must be positive")
    primes = primes_through(2 * x)
    band_primes = [p for p in primes if y <= p <= 2 * y and p % 4 == 3]
    if not band_primes:
        raise ValueError("the indicated band contains no primes that are 3 modulo 4")
    five_powers = [1]
    while 5 * five_powers[-1] <= x // 2:
        five_powers.append(5 * five_powers[-1])
    target_primes = [p for p in primes if p >= x]
    count = len(target_primes) * (len(target_primes) - 1) // 2
    if sample is not None and not 1 <= sample <= count:
        raise ValueError("sample size must be between one and the total number of pairs")
    ranks = None if sample is None else Random(seed).sample(range(count), sample)
    exponent = len(five_powers) - 1
    fixed_cost = compare(prime_pairs(target_primes, ranks), lambda n: fixed(n, exponent),
                         1 + 2 * exponent, five_powers, fermat_multiple)
    band_cost = compare(prime_pairs(target_primes, ranks), lambda n: band(n, band_primes),
                        2 * len(band_primes), band_primes, fermat_multiple)
    return dict(x=x, y=y, primes=len(target_primes), population=count,
                pairs=count if sample is None else sample, seed=None if sample is None else seed,
                five_max_exponent=exponent, band_primes=band_primes,
                fixed_five=fixed_cost, prime_band=band_cost)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("x", type=int)
    parser.add_argument("--band", required=True, type=int, metavar="Y")
    parser.add_argument("--sample", type=int, help="number of pairs to sample without replacement")
    parser.add_argument("--seed", type=int, default=20261124)
    parser.add_argument("--fermat-multiple", type=int, default=1,
                        help="scale the consecutive scan budget to compare measured costs")
    args = parser.parse_args()
    print(json.dumps(measure(args.x, args.band, args.sample, args.seed, args.fermat_multiple), indent=2))
