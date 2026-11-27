"""Compare square checks and centered reciprocal powers on fixed, public product-only inputs."""
import argparse
import json
from collections import defaultdict
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from experiments.rectangular_root_windows import bounds, interval, multiplier_ratio


def measure(n=154421, bits=9, base=2):
    if n.bit_length() > 24 or n < 9 or n % 2 != 1 or gcd(base, n) != 1:
        raise ValueError("the example accepts odd moduli of at most 24 bits and a unit base")
    gaps, coordinates, common = schedule(n, bits, None, None)
    center = n // 2
    gap_keys = {}
    for gap in gaps:
        right = pow(base, center * gap, n)
        gap_keys[gap] = right, (right + pow(right, -1, n)) % n
    matches, left_entries = [], []
    for _, _, c, s, gap in coordinates:
        a, b = (c - gap) // 2, (c + gap) // 2
        left = pow(base, s - (center + 1) * c, n)
        key = (left + pow(left, -1, n)) % n
        left_entries.append((a, b, s, left, key))
        right, right_key = gap_keys[gap]
        if key == right_key:
            matches.append({"weights": [a, b], "sum": s, "x_power": left,
                            "y_power": right, "trace": key, "gcd": gcd(left - right, n),
                            "right_precheck": gcd(right * right - 1, n)})
    by_trace = defaultdict(list)
    for gap, (right, key) in gap_keys.items():
        by_trace[key].append((gap, right))
    across_all_gaps = [
        {"weights": [a, b], "sum": s, "matched_gap": gap, "gcd": gcd(left - right, n)}
        for a, b, s, left, key in left_entries for gap, right in by_trace.get(key, ())
    ]
    return {"n": n, "factor_bits": bits, "base": base, "assignments": common["assignments"],
            "right_gaps": gaps, "coordinates": len(coordinates),
            "distinct_left_indices": len({(c, s) for _, _, c, s, _ in coordinates}), "own_gap_matches": matches,
            "all_gap_matches": across_all_gaps}



ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "benchmarks/weighted-global-trace.json"


def schedule(n, bits, limit, per_row):
    """The same assignments and coordinates for all three methods."""
    if n < 9 or n % 2 == 0 or any(x is not None and x < 0 for x in (limit, per_row)):
        raise ValueError("expected an odd product and nonnegative budgets")
    bmax, hmax, kmax = bounds(n, 1)
    excess = multiplier_ratio(n, hmax, bits)
    end = kmax if limit is None else min(kmax, limit)
    gaps, coordinates, intervals = set(), [], {}
    assignments = trials = omitted = 0
    for multiplier in (1, 4):
        step = 2 if multiplier == 1 else 1
        for a in range(1, isqrt(end // multiplier) + 1, step):
            first = a if multiplier == 1 else a + 1
            last = min(end // (multiplier * a), (1024 + excess) * a // 1024)
            for b in range(first, last + 1, 2):
                trials += 1
                if gcd(a, b) != 1:
                    continue
                assignments += 1
                gaps.add(b - a)
                k = multiplier * a * b
                if k not in intervals:
                    intervals[k] = interval(n, 1, k, bmax, hmax)
                lo, hi = intervals[k]
                stop = hi + 1 if per_row is None else min(hi + 1, lo + per_row)
                omitted += max(0, hi + 1 - stop)
                for y in range(lo, stop):
                    s = 2 * y if multiplier == 1 else y
                    coordinates.append((k, y, a + b, s, b - a))
    setup = dict(weight_gcds=trials, assignments=assignments, intervals=len(intervals),
                 gap_entries=len(gaps), coordinate_visits=len(coordinates),
                 omitted_coordinates_below_limit=str(omitted), full_multiplier_limit=str(kmax),
                 whole_range=end == kmax and omitted == 0)
    return sorted(gaps), coordinates, setup


def gcd_counts():
    return {"one": 0, "whole": 0, "proper": 0}


def record_gcd(value, n, counts, divisors):
    g = gcd(value, n)
    if g == 1:
        counts["one"] += 1
    elif g == n:
        counts["whole"] += 1
    else:
        counts["proper"] += 1
        divisors.add(g)
    return g


def row_squares(n, coordinates):
    start = process_time_ns()
    rows = dict.fromkeys((k, y) for k, y, _, _, _ in coordinates)
    prepared = process_time_ns()
    divisors = set()
    readouts = gcd_counts()
    squares = 0
    for k, y in rows:
        value = y * y - k * n
        x = isqrt(value)
        if x * x == value:
            squares += 1
            record_gcd(y - x, n, readouts, divisors)
            record_gcd(y + x, n, readouts, divisors)
    end = process_time_ns()
    return (dict(square_tests=len(rows), exact_squares=squares, readouts=readouts,
                 divisors=[str(d) for d in sorted(divisors)]),
            dict(setup=prepared - start, scan=end - prepared))


def trace_search(n, base, gaps, coordinates, all_gaps):
    start = process_time_ns()
    if gcd(base, n) != 1:
        raise ValueError("the selected base must be a unit")
    inverse_base = pow(base, -1, n)
    h = n // 2
    by_gap, by_trace = {}, defaultdict(list)
    divisors = set()
    prechecks, readouts = gcd_counts(), gcd_counts()
    for gap in gaps:
        right = pow(base, h * gap, n)
        trace = (right + pow(right, -1, n)) % n
        record_gcd(right * right - 1, n, prechecks, divisors)
        by_gap[gap] = (right, trace)
        if all_gaps:
            by_trace[trace].append((gap, right))
    setup_divisors = sorted(divisors)
    prepared = process_time_ns()
    different_gap_hits = 0
    first_off_gap_factor = None
    for k, y, c, s, own_gap in coordinates:
        power = s - (h + 1) * c
        left = pow(inverse_base if power < 0 else base, abs(power), n)
        trace = (left + pow(left, -1, n)) % n
        if all_gaps:
            hits = by_trace.get(trace, ())
        else:
            right, right_trace = by_gap[own_gap]
            hits = ((own_gap, right),) if trace == right_trace else ()
        for gap, right in hits:
            different_gap_hits += gap != own_gap
            divisor = record_gcd(left - right, n, readouts, divisors)
            if gap != own_gap and 1 < divisor < n and first_off_gap_factor is None:
                first_off_gap_factor = dict(row=k, y=str(y), weights=[(c-own_gap)//2, (c+own_gap)//2],
                                            sum=str(s), matched_gap=gap, left=str(left),
                                            right=str(right), trace=str(trace), gcd=str(divisor))
    end = process_time_ns()
    return (dict(setup_powers=len(gaps), setup_inversions=1 + len(gaps),
                 setup_base_gcds=1, prechecks=prechecks,
                 setup_divisors=[str(d) for d in setup_divisors],
                 hashed_right_entries=len(gaps) if all_gaps else 0,
                 scan_powers=len(coordinates), scan_inversions=len(coordinates),
                 lookups=len(coordinates), different_gap_hits=different_gap_hits,
                 first_off_gap_factor=first_off_gap_factor,
                 readouts=readouts, divisors=[str(d) for d in sorted(divisors)]),
            dict(setup=prepared - start, scan=end - prepared))


def compare(n, bits, base, multiplier_limit, per_row, rotation=0):
    start = process_time_ns()
    gaps, coordinates, common = schedule(n, bits, multiplier_limit, per_row)
    times = {"common_setup": process_time_ns() - start}
    report = {"common": common}
    methods = ["square", "own", "global"]
    for name in methods[rotation % 3:] + methods[:rotation % 3]:
        if name == "square":
            result, timing = row_squares(n, coordinates)
        else:
            result, timing = trace_search(n, base, gaps, coordinates, name == "global")
        report[name] = result
        times[name] = timing
    return report, times


def run_fixture(case):
    return compare(int(case["n"]), case["factor_bits"], case["base"],
                   case["multiplier_limit"], case["per_row"])[0]


def check_fixture(case, report):
    if case["checks"] != report:
        raise ArithmeticError(f"search output changed for {case['id']}")
    n = int(case["n"])
    divisors = report["global"]["divisors"]
    pair = sorted((int(divisors[0]), n // int(divisors[0]))) if divisors else []
    expected_status = "complete" if pair else "partial"
    if (case["status"] != expected_status or case["factors"] != [str(p) for p in pair]
            or case["remaining"] != ([] if pair else [str(n)])):
        raise ArithmeticError(f"incorrect outcome for {case['id']}")
    for name in ("square", "own", "global"):
        if any(not 1 < int(d) < n or n % int(d) for d in report[name]["divisors"]):
            raise ArithmeticError("invalid reported divisor")


def panel(verify=False, repeats=1):
    from experiments.split_prime_holdout import certificate
    if repeats < 1:
        raise ValueError("expected a positive repeat count")
    output = []
    for case in json.loads(FIXTURE.read_text()):
        times = []
        for run in range(repeats):
            report, elapsed = compare(int(case["n"]), case["factor_bits"], case["base"],
                                      case["multiplier_limit"], case["per_row"], run)
            check_fixture(case, report)
            times.append(elapsed)
        row = {"id": case["id"], "work": report, "cpu_ns": times}
        if verify:
            found = {int(d) for method in ("square", "own", "global")
                     for d in report[method]["divisors"]}
            n = int(case["n"])
            pairs = {tuple(sorted((p, n // p))) for p in found}
            row["factor_certificates"] = [certificate(n, pair) for pair in sorted(pairs)]
        output.append(row)
    return output


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--panel", action="store_true", help="run the fixed same-input benchmark")
    cli.add_argument("--verify", action="store_true", help="Lean-check every recovered pair")
    cli.add_argument("--repeats", type=int, default=1, help="rotate method order across timing repeats")
    args = cli.parse_args()
    report = panel(args.verify, args.repeats) if args.panel or args.verify else measure()
    print(json.dumps(report, indent=2))
