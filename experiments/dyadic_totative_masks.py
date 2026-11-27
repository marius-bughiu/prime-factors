"""Evaluate dyadic factorial coefficients with a hard cap on the row size."""

import argparse
import json
from itertools import combinations
from math import comb, gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "benchmarks" / "dyadic-totative-masks.json"


def search(n, max_row):
    """Use just n and the budget, under the equal-width odd-prime hypothesis."""
    if n <= 1 or n % 2 == 0 or max_row < 0:
        raise ValueError("n must be odd and greater than one, and max_row nonnegative")
    width = (n.bit_length() + 1) // 2
    rows = []
    for j in range(width - 2, 0, -1):
        row = n >> j
        if row > max_row:
            return {"rows": rows, "factors": [], "remaining": [str(n)],
                    "stopped_before": j, "next_row_bits": row.bit_length()}
        half = row // 2
        coefficient = comb(2 * half, half)
        if row % 2:
            coefficient *= row
        divisor = gcd(coefficient, n)
        rows.append({"index": j, "row": row, "coefficient_bits": coefficient.bit_length(),
                     "gcd": str(divisor)})
        if 1 < divisor < n:
            return {"rows": rows, "factors": sorted([str(divisor), str(n // divisor)], key=int),
                    "remaining": [], "stopped_before": None, "next_row_bits": None}
    return {"rows": rows, "factors": [], "remaining": [str(n)],
            "stopped_before": None, "next_row_bits": None}


def check_contrasts(n, p, q):
    """Independent test for the small cases after the product-only search."""
    def units(endpoint):
        return sum(gcd(i, n) == 1 for i in range(1, endpoint + 1))

    checked = 0
    for j in range(1, q.bit_length() + 1):
        row = n >> j
        actual = 2 * units(row // 2) + (row % 2) - units(row)
        expected = ((p >> j) & 1) + ((q >> j) & 1)
        if actual != expected:
            raise AssertionError((j, actual, expected))
        checked += 1
    return checked


def fixtures():
    results = []
    for case in json.loads(FIXTURES.read_text()):
        n = int(case["n"])
        result = search(n, case["max_row"])
        expected = {**case["checks"], "factors": case["factors"], "remaining": case["remaining"]}
        if result != expected:
            raise AssertionError((case["id"], result, expected))
        audited = 0
        if case["expected_small_contrasts"]:
            p, q = map(int, result["factors"])
            audited = check_contrasts(n, p, q)
        if audited != case["expected_small_contrasts"]:
            raise AssertionError((case["id"], audited, case["expected_small_contrasts"]))
        results.append({"id": case["id"], **result, "contrasts_checked": audited})
    return results


def small_census(max_row):
    """Check every distinct equal-width prime pair of widths six through nine."""
    result = []
    for width in range(6, 10):
        primes = [p for p in range(2 ** (width - 1) + 1, 2 ** width, 2)
                  if all(p % d for d in range(3, isqrt(p) + 1, 2))]
        pairs = splits = evaluations = 0
        for p, q in combinations(primes, 2):
            pairs += 1
            found = search(p * q, max_row)
            evaluations += len(found["rows"])
            if found["factors"]:
                if found["factors"] != [str(p), str(q)]:
                    raise AssertionError((p, q, found))
                splits += 1
        result.append({"width": width, "pairs": pairs, "split": splits,
                       "unresolved": pairs - splits, "coefficients_evaluated": evaluations})
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("n", nargs="?", type=int)
    selection.add_argument("--fixtures", action="store_true")
    selection.add_argument("--small-census", action="store_true")
    parser.add_argument("--max-row", type=int, default=4096)
    args = parser.parse_args()
    if args.fixtures:
        report = fixtures()
    elif args.small_census:
        report = small_census(args.max_row)
    else:
        report = search(args.n, args.max_row)
    print(json.dumps(report, indent=2))
