"""Compare returning to a signed odd power with the ordinary reduced squaring orbit."""
import argparse
from functools import lru_cache
from itertools import combinations
import json
from math import gcd
from pathlib import Path

from experiments.mixed_ratio_heights import jacobi


ROOT = Path(__file__).resolve().parents[1]


@lru_cache(maxsize=None)
def prime_divisors(n):
    result = []
    trial = 2
    while trial * trial <= n:
        if n % trial == 0:
            result.append(trial)
            while n % trial == 0:
                n //= trial
        trial = 3 if trial == 2 else trial + 2
    if n > 1:
        result.append(n)
    return tuple(result)


@lru_cache(maxsize=None)
def order(a, n):
    """Factor small, known proof-side moduli only. The unit group modulo 1 has order 1."""
    if gcd(a, n) != 1:
        raise ValueError("multiplicative order requires a unit")
    phi = n
    for prime in prime_divisors(n):
        phi = phi // prime * (prime - 1)
    result = phi
    for prime in prime_divisors(phi):
        while result % prime == 0 and pow(a, result // prime, n) == 1:
            result //= prime
    return result


def orbit(n, base, budget, signed):
    """Use only n, the base and the budget. Each iteration squares once."""
    exponent = n - 1
    if signed:
        exponent //= exponent & -exponent
    initial = pow(base, exponent, n)
    state = initial
    for j in range(1, budget + 1):
        state = state * state % n
        minus = gcd(state - initial, n)
        plus = gcd(state + initial, n) if signed else 1
        if 1 < minus < n or 1 < plus < n:
            return j, minus, plus
    return None


def compare_public(n, base, budget):
    """Run both public searches under identical caps and record all work."""
    if n <= 1 or n % 2 == 0 or budget < 0 or jacobi(base, n) != -1:
        raise ValueError("expected an odd product, negative-Jacobi base, and nonnegative budget")
    work = dict(base=base, budget=budget, jacobi_tests=1)
    for name, signed in (("signed", True), ("ordinary", False)):
        hit = orbit(n, base, budget, signed)
        steps = hit[0] if hit else budget
        factors = sorted({str(g) for g in hit[1:] if 1 < g < n}, key=int) if hit else []
        work[name] = dict(setup_powers=1, squarings=steps, gcds=steps*(2 if signed else 1),
                          first=steps if hit else None, divisors=factors)
    return work


def local_diagnostic(p, q, base):
    exponent = p * q - 1
    residues = [pow(base, exponent, prime) for prime in (p, q)]
    orders = [order(a, prime) for a, prime in zip(residues, (p, q))]
    periods = [order(2 % r, r) for r in orders]
    if gcd(*orders) != 1:
        raise ArithmeticError("the reduced local orders must be coprime")
    return orders, periods


def expected(periods, budget, signed):
    first = min(periods)
    return first if first <= budget and (signed or periods[0] != periods[1]) else None


def check(p, q, base, budget):
    n = p * q
    orders, periods = local_diagnostic(p, q, base)
    results = {}
    for name, signed in (("ordinary", False), ("signed", True)):
        result = orbit(n, base, budget, signed)
        index = result[0] if result else None
        if index != expected(periods, budget, signed):
            raise ArithmeticError(f"local period mismatch for {n}, {base}, {name}")
        if result and any(n % g for g in result[1:]):
            raise ArithmeticError("invalid gcd")
        results[name] = result
    return orders, periods, results


def selected(p, q, budget):
    n = p * q
    base = next(a for a in range(2, n) if jacobi(a, n) == -1)
    orders, periods, results = check(p, q, base, budget)
    return dict(n=str(n), primes=[str(p), str(q)], base=base, budget=budget,
                local_orders=orders, return_periods=periods, gcd_results=results,
                remaining_after_budget=[] if results["signed"] else [str(n)])


def report():
    primes = [p for p in range(67, 128, 4) if prime_divisors(p) == (p,)]
    budget = 64
    rows = dict(units=0, signed_splits=0, ordinary_splits=0, equal_periods=0,
                equal_periods_with_two_nontrivial_orders=0, max_first_signed=0,
                ordinary_squarings=0, signed_squarings=0, ordinary_gcds=0, signed_gcds=0)
    for p, q in combinations(primes, 2):
        n = p * q
        for base in range(1, n):
            if jacobi(base, n) != -1:
                continue
            orders, periods, results = check(p, q, base, budget)
            rows["units"] += 1
            rows["signed_splits"] += results["signed"] is not None
            rows["ordinary_splits"] += results["ordinary"] is not None
            equal = periods[0] == periods[1]
            rows["equal_periods"] += equal
            rows["equal_periods_with_two_nontrivial_orders"] += equal and min(orders) > 1
            rows["max_first_signed"] = max(rows["max_first_signed"], results["signed"][0])
            for name, gcds in (("signed", 2), ("ordinary", 1)):
                steps = results[name][0] if results[name] else budget
                rows[f"{name}_squarings"] += steps
                rows[f"{name}_gcds"] += gcds * steps
    return dict(
        panel=dict(primes=primes, pairs=len(primes)*(len(primes)-1)//2,
                   budget_per_base=budget, **rows),
        equal_period_example=selected(71, 79, budget),
        long_period_example=selected(2_000_004_719, 2_000_026_079, budget),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(report(), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
