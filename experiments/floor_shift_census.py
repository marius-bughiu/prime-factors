"""Measure a one-guess change to square-test order on complete small populations."""

import json
from collections import Counter
from itertools import combinations
from math import isqrt
from pathlib import Path

from experiments.cyclotomic_root_readings import SQUARE_RESIDUES, midpoint_scan
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/floor-shift-census.json"


def proposed_midpoint(n, root, cap):
    """Choose a midpoint from the product alone and apply the baseline filters."""
    remainder = n - root * root
    if remainder % 2 == 1 or remainder == 0:
        return None
    two_part = remainder & -remainder
    midpoint = root + two_part // 2
    if midpoint >= cap or midpoint % 2 != (n + 1) // 2 % 2:
        return None
    delta = midpoint * midpoint - n
    if delta % 256 not in SQUARE_RESIDUES[256]:
        return None
    return midpoint


def census(width):
    if width not in range(9, 15):
        raise ValueError("census widths are 9 through 14")
    cap = 1 << width
    primes = [p for p in primes_through(cap - 1) if p >= cap // 2]
    counts = Counter(dict.fromkeys((
        "pairs", "any_exact_shift", "baseline_tests", "priority_tests", "hits",
        "hits_after_first_baseline_test", "wrong_guesses_after_true_midpoint",
        "saved_on_hits", "priority_discriminant_tests",
    ), 0))
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * width:
            continue
        root = isqrt(n)
        pair, baseline_tests, _ = midpoint_scan(n, root, cap, 2, True)
        if pair != (p, q):
            raise ArithmeticError("baseline recovered a different pair")
        guess = proposed_midpoint(n, root, cap)
        true_midpoint = (p + q) // 2
        counts["pairs"] += 1
        counts["any_exact_shift"] += (n - root * root) % (p + q - 2 * root) == 0
        counts["baseline_tests"] += baseline_tests
        if guess is None:
            counts["priority_tests"] += baseline_tests
            continue
        counts["priority_discriminant_tests"] += 1
        counts["priority_tests"] += 1
        delta = guess * guess - n
        gap = isqrt(delta)
        if gap * gap == delta:
            if (guess - gap, guess + gap) != pair:
                raise ArithmeticError("product-only guess recovered a different pair")
            counts["hits"] += 1
            counts["hits_after_first_baseline_test"] += baseline_tests > 1
            counts["saved_on_hits"] += baseline_tests - 1
        else:
            # Resume the original search, avoiding a second test of the rejected guess.
            found, remaining, _ = midpoint_scan(n, root, cap, 2, True, already_tested=guess)
            if found != pair:
                raise ArithmeticError("fallback recovered a different pair")
            counts["priority_tests"] += remaining
            counts["wrong_guesses_after_true_midpoint"] += guess > true_midpoint
    return {"bits_per_prime": width, **counts}


def main():
    rows = [census(width) for width in range(9, 15)]
    if rows != json.loads(FIXTURE.read_text()):
        raise SystemExit("floor-shift census differs from the reviewed counts")
    for row in rows:
        print(json.dumps(row))


if __name__ == "__main__":
    main()
