"""Compare lifted candidates with every floor-side center on bounded prime products."""

import json
from collections import Counter
from itertools import combinations
from math import isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.cyclotomic_root_readings import SQUARE_RESIDUES, midpoint_scan
from scripts.factor import primes_through, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/dyadic-center-compression.json"
CONTROLS = ((138953, 9), (141217, 9), (37001, 8), (134271337, 14))


def lifted_centers(n, width):
    """Generate (exponent, center) for feasible prime sums, using only N and the width."""
    if not 7 <= width <= 14 or n.bit_length() != 2 * width or n % 2 == 0:
        raise ValueError("expected an odd educational product of the requested width")
    root = isqrt(n)
    if root * root == n:
        raise ValueError("the square-free controls require a nonsquare")
    lifts = 0
    centers = []
    if n % 4 == 3 and root % 2 == 1:
        centers.append((1, root))
    elif n % 8 == 5:
        centers.append((2, root if root % 2 else root - 1))
    elif n % 8 == 1:
        unit = 1
        for bits in range(3, width + 1):
            correction = ((n - unit * unit) // (1 << bits)) * (1 << (bits - 1))
            unit = (unit + correction) % (1 << (bits + 1))
            lifts += 1
        if (unit * unit - n) % (1 << (width + 1)):
            raise ArithmeticError("inexact lifted root")
        for exponent in range(3, width + 1):
            power = 1 << exponent
            shifted = unit + power // 2
            for residue in (shifted, -shifted):
                distance = (root - residue) % power
                if distance <= root and 2 * distance < power:
                    centers.append((exponent, root - distance))
    return [[j, s] for j, s in centers if s + (1 << (j - 1)) < (1 << width)], lifts


def exhaustive_centers(n, width):
    """Independent oracle for the full admissible list, including unsuccessful guesses."""
    root = isqrt(n)
    centers = []
    for center in range(root + 1):
        remainder = n - center * center
        power = remainder & -remainder
        candidate_sum = 2 * center + power
        if power > 1 and 2 * root < candidate_sum < (2 << width):
            centers.append([power.bit_length() - 1, center])
    return sorted(centers)


def measure(n, width):
    centers, lifts = lifted_centers(n, width)
    root = isqrt(n)
    if width <= 10 and sorted(centers) != exhaustive_centers(n, width):
        raise ArithmeticError("the compressed list differs from exhaustive enumeration")
    midpoints = set()
    for exponent, center in centers:
        remainder = n - center * center
        if (remainder & -remainder) != (1 << exponent):
            raise ArithmeticError("candidate does not give the advertised reading")
        midpoints.add(center + (1 << (exponent - 1)))
    parity = (n + 1) // 2 % 2
    budget = sorted(m for m in midpoints
                    if m % 2 == parity and (m * m - n) % 256 in SQUARE_RESIDUES[256])
    tests = 0
    recovered = None
    for m in budget:
        tests += 1
        delta = m * m - n
        gap = isqrt(delta)
        if gap * gap == delta and m - gap > 1:
            if (m - gap) * (m + gap) != n:
                raise ArithmeticError("invalid factorization")
            recovered = (m - gap, m + gap)
            break
    baseline_pair, baseline_tests, _ = midpoint_scan(n, root, 1 << width, 2, True)
    # This reference uses the known sum only after both searches. For each
    # exponent it gives the only possible center that could recover this pair.
    true_midpoint = sum(baseline_pair) // 2
    expected_hit = False
    for exponent in range(1, width + 1):
        center = true_midpoint - (1 << (exponent - 1))
        if 0 <= center <= root:
            remainder = n - center * center
            if (remainder & -remainder) == (1 << exponent):
                expected_hit = True
                break
    if (recovered is not None) != expected_hit or (recovered and recovered != baseline_pair):
        raise ArithmeticError("the reading disagrees with the independent success check")
    root_remainder = n - root * root
    floor_hit = 2 * root + (root_remainder & -root_remainder) == 2 * true_midpoint
    return {
        "lifts": lifts, "centers": centers, "midpoints": sorted(midpoints),
        "square_test_budget": budget, "tests_to_stop": tests, "recovered": recovered,
        "baseline_pair": baseline_pair, "baseline_tests": baseline_tests,
        "floor_only_hit": floor_hit,
    }


def census(width):
    primes = [p for p in primes_through((1 << width) - 1) if p >= 1 << (width - 1)]
    counts = Counter(dict.fromkeys((
        "products", "root_lifts", "generated_centers", "different_midpoints",
        "planned_exact_tests", "performed_exact_tests", "hits", "floor_only_hits",
        "baseline_hits_at_same_budget", "compressed_only", "baseline_only",
        "baseline_performed_at_same_budget",
    ), 0))
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * width:
            continue
        row = measure(n, width)
        if row["baseline_pair"] != (p, q):
            raise ArithmeticError("baseline disagrees with the sieve")
        budget = len(row["square_test_budget"])
        baseline_hit = row["baseline_tests"] <= budget
        found = row["recovered"] is not None
        counts["products"] += 1
        counts["root_lifts"] += row["lifts"]
        counts["generated_centers"] += len(row["centers"])
        counts["different_midpoints"] += len(row["midpoints"])
        counts["planned_exact_tests"] += budget
        counts["performed_exact_tests"] += row["tests_to_stop"]
        counts["hits"] += found
        counts["floor_only_hits"] += row["floor_only_hit"]
        counts["baseline_hits_at_same_budget"] += baseline_hit
        counts["baseline_performed_at_same_budget"] += min(row["baseline_tests"], budget)
        counts["compressed_only"] += found and not baseline_hit
        counts["baseline_only"] += baseline_hit and not found
    return {"factor_bits": width, **counts}


def study():
    controls = []
    for n, width in CONTROLS:
        row = measure(n, width)
        for key in ("baseline_pair", "recovered"):
            if row[key]:
                row[key] = [str(p) for p in row[key]]
        controls.append({"product": str(n), **row})
    return {"controls": controls, "populations": [census(w) for w in range(7, 15)]}


def main():
    observed = study()
    if observed != json.loads(FIXTURE.read_text()):
        raise SystemExit("dyadic center comparison differs from the reviewed fixture")
    with TemporaryDirectory() as tmp:
        for row in observed["controls"]:
            if row["recovered"]:
                path = Path(tmp) / f"DyadicCenter{row['product']}.lean"
                path.write_text(render_certificate(int(row["product"]), [int(p) for p in row["recovered"]]))
                verify_file(path)
    print(json.dumps(observed))


if __name__ == "__main__":
    main()
