"""Time the two modulo-256 policies on the fixed 14-bit square-remainder cohort.

Run python3 -m experiments.time_gaussian_square_gate from the repository root.
The inputs, operation counts and recovered pairs are checked outside the timing.
"""

import argparse
import json
import platform
import sys
from itertools import combinations
from math import isqrt
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.cyclotomic_root_readings import (
    FIXTURE, GATE_MODULI, SQUARE_RESIDUES, midpoint_scan, test_remainder,
)
from experiments.grouped_offset_sweep import is_prime


WIDTH = 14
LIMIT = 1 << WIDTH
BASELINE = "mod256"
SWITCHED = "switched_8_or_16_mod256"
MIDPOINT_SQUARES = SQUARE_RESIDUES[256]
GATE_TABLES = tuple((modulus, SQUARE_RESIDUES[modulus]) for modulus in GATE_MODULI)


def accepts(n, root):
    if n % 4 != 1:
        return False
    remainder = n - root * root
    for modulus, squares in GATE_TABLES:
        if remainder % modulus not in squares:
            return False
    gap = isqrt(remainder)
    return gap * gap == remainder


def factor_control(n, switched):
    root = isqrt(n)
    stride = 2
    if switched and accepts(n, root):
        stride = 16 if n % 8 == 5 else 8
    first = root + 1
    first += ((n + 1) // 2 - first) % stride
    for midpoint in range(first, LIMIT, stride):
        delta = midpoint * midpoint - n
        if delta % 256 in MIDPOINT_SQUARES:
            gap = isqrt(delta)
            if gap * gap == delta and midpoint - gap > 1:
                return midpoint - gap, midpoint + gap
    raise ArithmeticError(f"missing pair in the fixed 14-bit cohort: {n}")


def prepare():
    """Warm both implementations and verify all factors and reference counts."""
    primes = [p for p in range(LIMIT // 2, LIMIT) if is_prime(p)]
    products = []
    sum_p = sum_q = passes = gate_tests = 0
    scan_tests = {BASELINE: 0, SWITCHED: 0}
    scan_lookups = {BASELINE: 0, SWITCHED: 0}
    gate_lookups = 0
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * WIDTH:
            continue
        products.append(n)
        sum_p += p
        sum_q += q
        root = isqrt(n)
        passed, tests, lookups = test_remainder(n, root, True)
        if accepts(n, root) != passed:
            raise AssertionError(f"gate disagreed on {n}")
        passes += passed
        gate_tests += tests
        gate_lookups += sum(lookups.values())
        for label, switched in ((BASELINE, False), (SWITCHED, True)):
            stride = (16 if n % 8 == 5 else 8) if switched and passed else 2
            pair, exact, lookups = midpoint_scan(n, root, LIMIT, stride, True)
            if pair != (p, q) or factor_control(n, switched) != pair:
                raise AssertionError(f"{label} disagreed on {n}")
            scan_tests[label] += exact
            scan_lookups[label] += lookups
    expected = json.loads(FIXTURE.read_text())["square_remainder_holdout_14"]
    if (len(products), passes, gate_tests, gate_lookups) != (
        expected["pairs"], expected["accepted"], expected["screened_gate_square_tests"],
        expected["sum_of_gate_lookups"],
    ):
        raise AssertionError("cohort or gate counts differ from the reference fixture")
    for label in scan_tests:
        row = expected["midpoint_scans"][label]
        if (scan_tests[label], scan_lookups[label]) != (row["exact_square_tests"], row["mod256_lookups"]):
            raise AssertionError(f"{label} work differs from the reference fixture")
    return products, (sum_p, sum_q)


def timed(products, switched, expected):
    elapsed_start = perf_counter_ns()
    cpu_start = process_time_ns()
    sum_p = sum_q = 0
    for n in products:
        p, q = factor_control(n, switched)
        sum_p += p
        sum_q += q
    cpu = process_time_ns() - cpu_start
    elapsed = perf_counter_ns() - elapsed_start
    if (sum_p, sum_q) != expected:
        raise AssertionError("timed scan disagreed with verified factor checksums")
    return {"cpu_s": cpu / 1e9, "elapsed_s": elapsed / 1e9}


def summary(values):
    return {"median": median(values), "min": min(values), "max": max(values)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, choices=range(1, 12), default=5,
                        help="number of full paired trials after the full-cohort warmup (default 5)")
    args = parser.parse_args()
    products, checksum = prepare()
    trials = []
    for index in range(args.trials):
        order = (BASELINE, SWITCHED) if index % 2 == 0 else (SWITCHED, BASELINE)
        trials.append({label: timed(products, label == SWITCHED, checksum) for label in order})
    metrics = ("cpu_s", "elapsed_s")
    print(json.dumps({
        "python": sys.version, "implementation": platform.python_implementation(),
        "architecture": platform.machine(), "os": platform.system(), "os_release": platform.release(),
        "factor_bits": WIDTH, "products": len(products), "factor_sums_checksum": checksum,
        "warmup": "one full run of each policy plus untimed reference verification",
        "paired_trials": trials,
        "seconds": {label: {metric: summary([trial[label][metric] for trial in trials])
                            for metric in metrics} for label in (BASELINE, SWITCHED)},
        "paired_percent_change_switched_vs_baseline": {
            metric: summary([100 * (t[SWITCHED][metric] / t[BASELINE][metric] - 1) for t in trials])
            for metric in metrics},
    }, indent=2))


if __name__ == "__main__":
    main()
