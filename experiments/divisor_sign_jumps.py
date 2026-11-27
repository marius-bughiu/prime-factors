"""Stream the positive divisor residues from a public negative square modulo N."""

import argparse
from bisect import bisect_left
import itertools
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.mixed_ratio_heights import jacobi
from experiments.reciprocal_anchor import collect_anchors
from experiments.reciprocal_fermat_holdout import BUDGET, MAX_TABLE_PERIOD, SEED, WHEEL
from experiments.split_prime_holdout import BLOCK, certificate, interval_primes
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "research/divisor-sign-jumps.json"
INPUT = ROOT / "research/reciprocal-fermat-holdout.json"
LARGE = ROOT / "research/many-character-windows.json"
METHODS = ("wheel60", "prime_sieve", "sign_table")
ORDERS = tuple(itertools.permutations(METHODS))
FOLLOWUP = METHODS + ("lazy_blocks", "interval_choice")
SAMPLES = 6


def wheel_rows():
    return [x for x in range(WHEEL) if gcd(x, WHEEL) == 1]


def positive_residues(d):
    """At d = 3 mod 4 the two signs at x and -x are opposite, or both zero."""
    if d % 4 != 3:
        raise ValueError("opposite signs require d = 3 mod 4")
    positive = []
    for x in range(1, (d + 1) // 2):
        sign = jacobi(x, d)
        if sign:
            positive.append(x if sign == 1 else d - x)
    return positive


def crt_rows(d, positive, wheel):
    inverse = pow(WHEEL, -1, d)
    return sorted(w + WHEEL * ((x - w) * inverse % d) for x in positive for w in wheel)


def stream(lo, hi, period, rows):
    base, offset = divmod(lo, period)
    base *= period
    first = bisect_left(rows, offset)
    while base <= hi:
        for i in range(first, len(rows)):
            x = base + rows[i]
            if x > hi:
                return
            yield x
        first = 0
        base += period


def lazy_stream(lo, hi, d, positive, wheel, counts, phases):
    """Only materialize the translated wheel for a phase reached by the scan."""
    wheel_lookup = [i in wheel for i in range(WHEEL)]
    cached = {}
    base = lo - lo % d
    while base <= hi:
        phase = base % WHEEL
        if phase not in cached:
            timer = process_time_ns()
            rows = [r for r in positive if wheel_lookup[(r + phase) % WHEEL]]
            cached[phase] = rows
            counts["phase_tables"] += 1
            counts["wheel_membership_tests"] += len(positive)
            counts["phase_table_rows"] += len(rows)
            phases["lazy_table"] += process_time_ns() - timer
        rows = cached[phase]
        counts["visited_blocks"] += 1
        for index in range(bisect_left(rows, lo - base), len(rows)):
            x = base + rows[index]
            if x > hi:
                return
            yield x
        base += d


def wheel_size(lo, hi, wheel):
    return sum((hi - w) // WHEEL - (lo - 1 - w) // WHEEL for w in wheel)


def search(n, bits, method):
    """Input to each timed search is limited to N, common prime width, and method."""
    started = process_time_ns()
    limit = (1 << bits) - 1
    lo, hi = max(1 << (bits - 1), (n - 1) // limit + 1), isqrt(n)
    if gcd(n, WHEEL) != 1 or not 5 < lo <= hi:
        raise ValueError("expected an odd prime pair above 5 in the public interval")
    phases = dict(anchor=0, jacobi_table=0, crt_sort=0, scan=0)
    counts = dict(jacobi_calls=0, positive_classes=0, crt_rows=0, trial_divisions=0,
                  sieve_segments=0)
    public = dict(lower=lo, upper=hi)
    pair = None
    candidates = None
    if method == "prime_sieve":
        candidates = interval_primes(lo, hi)
        public["route"] = "segmented_primes"
    else:
        rows, period = wheel_rows(), WHEEL
        public["route"] = "wheel60"
        if method in ("sign_table", "lazy_blocks", "interval_choice"):
            if method != "sign_table":
                counts.update(phase_tables=0, visited_blocks=0, wheel_membership_tests=0,
                              phase_table_rows=0)
                phases["lazy_table"] = 0
            stats = {}
            timer = process_time_ns()
            anchors = collect_anchors(n, BUDGET, WHEEL, 1, negative_only=True, stats=stats)
            phases["anchor"] = process_time_ns() - timer
            public["cf"] = stats
            if not anchors:
                public["route"] = "no_anchor_fallback"
            elif "setup_factor" in anchors[0]:
                f = anchors[0]["setup_factor"]
                if not 1 < f < n or n % f:
                    raise ArithmeticError("invalid setup factor")
                pair = sorted((f, n // f))
                public["route"] = "setup_gcd"
            else:
                anchor = anchors[0]
                d = anchor["period"]
                public["anchor"] = anchor
                if method == "interval_choice":
                    public["wheel_interval_size"] = wheel_size(lo, hi, rows)
                if d > MAX_TABLE_PERIOD:
                    public["route"] = "oversize_fallback"
                elif method == "interval_choice" and 4 * ((d - 1) // 2) > public["wheel_interval_size"]:
                    public["route"] = "interval_fallback"
                else:
                    timer = process_time_ns()
                    positive = positive_residues(d)
                    if method != "sign_table":
                        positive.sort()
                    phases["jacobi_table"] = process_time_ns() - timer
                    counts.update(jacobi_calls=(d - 1) // 2, positive_classes=len(positive))
                    if method == "sign_table":
                        timer = process_time_ns()
                        rows = crt_rows(d, positive, rows)
                        phases["crt_sort"] = process_time_ns() - timer
                        period *= d
                        counts["crt_rows"] = len(rows)
                        public["route"] = "sign_table"
                    else:
                        candidates = lazy_stream(lo, hi, d, positive, rows, counts, phases)
                        public["route"] = "lazy_blocks"
        elif method != "wheel60":
            raise ValueError(method)
        if candidates is None:
            candidates = stream(lo, hi, period, rows)
    if pair is None:
        timer = process_time_ns()
        for divisions, x in enumerate(candidates, start=1):
            if n % x == 0:
                pair = [x, n // x]
                counts["trial_divisions"] = divisions
                if method == "prime_sieve":
                    counts["sieve_segments"] = 1 + (x - lo) // BLOCK
                break
        phases["scan"] = process_time_ns() - timer - phases.get("lazy_table", 0)
    if pair is None or pair[0] * pair[1] != n or not lo <= pair[0] <= hi:
        raise ArithmeticError(f"{method} failed to split input in the interval")
    phases["other"] = process_time_ns() - started - sum(phases.values())
    return dict(**public, pair=[str(x) for x in pair], **counts), phases


def full_size_prices():
    priced = []
    for row in json.loads(LARGE.read_text()):
        n = int(row["n"])
        d = int(row["moduli"][0])
        witness = int(row["negative_roots"][0])
        if (d != min(map(int, row["moduli"])) or d % 4 != 3 or gcd(d, n * WHEEL) != 1
                or (witness**2 + d) % n or not 0 < d <= 2**1366):
            raise ArithmeticError("recorded minimum or public root failed verification")
        # quotientBudget_wheel_ratio: d < 13 * phi(d). Every sorted CRT row
        # corresponds to a wheel unit and a positive class, hence 8 * phi(d).
        min_rows = 8 * (d // 13 + 1)
        row_bytes = ((WHEEL * d - 1).bit_length() + 7) // 8
        priced.append(dict(id=row["id"], cf_budget=row["cf_steps"], step=row["anchor_steps"][0],
                           d=str(d), d_bits=d.bit_length(), root_verified=True,
                           jacobi_calls=str((d - 1) // 2), crt_rows_lower=str(min_rows),
                           packed_bytes_per_row=row_bytes, packed_table_bytes_lower=str(row_bytes * min_rows)))
    return priced


def check_small_tables():
    wheel = wheel_rows()
    for d in (7, 11, 119, 343):  # Prime, composite, and repeated prime-power moduli.
        rows = crt_rows(d, positive_residues(d), wheel)
        expected = [x for x in range(WHEEL * d) if gcd(x, WHEEL) == 1 and jacobi(x, d) == 1]
        if rows != expected:
            raise ArithmeticError("CRT construction disagrees with exhaustive divisor signs")
        lo, hi = 2 * WHEEL * d - 13, 3 * WHEEL * d + 7
        if list(stream(lo, hi, WHEEL * d, rows)) != [
            x for x in range(lo, hi + 1) if gcd(x, WHEEL) == 1 and jacobi(x, d) == 1
        ]:
            raise ArithmeticError("ascending stream disagrees across period boundaries")
        counts = dict(phase_tables=0, visited_blocks=0, wheel_membership_tests=0,
                      phase_table_rows=0)
        lazy = lazy_stream(lo, hi, d, sorted(positive_residues(d)), wheel, counts, {"lazy_table": 0})
        if list(lazy) != list(stream(lo, hi, WHEEL * d, rows)):
            raise ArithmeticError("lazy and eager candidates disagree across period boundaries")


def holdouts(per_width=SAMPLES):
    source = json.loads(INPUT.read_text())
    if source["seed"] != SEED.decode():
        raise ArithmeticError("the published holdout seed changed")
    for bits in (20, 24):
        public = sorted((r["sample"], int(r["n"])) for r in source["cases"] if r["bits"] == bits)
        if len(public) < per_width or len({n for _, n in public}) != len(public):
            raise ArithmeticError("expected distinct holdout products")
        for sample, n in public[:per_width]:
            yield bits, sample, n


def run_cases(repeats, *, followup=False):
    cases, measurements = [], []
    methods = FOLLOWUP if followup else METHODS
    orders = tuple(methods[i:] + methods[:i] for i in range(len(methods))) if followup else ORDERS
    for index, (bits, sample, n) in enumerate(holdouts(2 * SAMPLES if followup else SAMPLES)):
        work = {}
        timings = {m: [] for m in methods}
        for rep in range(repeats):
            for method in orders[(rep + index) % len(orders)]:
                primes_through.cache_clear()
                cpu, wall = process_time_ns(), perf_counter_ns()
                outcome, phases = search(n, bits, method)
                phases["cpu"] = process_time_ns() - cpu
                phases["wall"] = perf_counter_ns() - wall
                timings[method].append(phases)
                if method in work and outcome != work[method]:
                    raise ArithmeticError("work counts changed between timed runs")
                work[method] = outcome
        pair = work["wheel60"]["pair"]
        if any(work[m]["pair"] != pair for m in methods):
            raise ArithmeticError("methods disagree on the two factors")
        if followup:
            if work["sign_table"]["trial_divisions"] != work["lazy_blocks"]["trial_divisions"]:
                raise ArithmeticError("lazy and eager searches visited different numbers of candidates")
            if work["interval_choice"]["route"] in ("interval_fallback", "lazy_blocks"):
                comparison = "wheel60" if work["interval_choice"]["route"] == "interval_fallback" else "lazy_blocks"
                if work["interval_choice"]["trial_divisions"] != work[comparison]["trial_divisions"]:
                    raise ArithmeticError("public selector disagrees with the chosen stream")
        for method in methods:
            work[method]["median_ns"] = {
                k: int(median(t[k] for t in timings[method])) for k in timings[method][0]
            }
        cases.append(dict(bits=bits, sample=sample, n=str(n), methods=work,
                          certificate_sha256=certificate(n, pair)))
        measurements.append(timings)
    return cases, measurements


def summarize(cases, measurements, methods=METHODS):
    result = {}
    for bits in (20, 24):
        subset = [(row, times) for row, times in zip(cases, measurements) if row["bits"] == bits]
        width = {}
        for method in methods:
            counts = {k: sum(row["methods"][method][k] for row, _ in subset)
                      for k in ("trial_divisions", "jacobi_calls", "crt_rows", "sieve_segments",
                                "phase_tables", "phase_table_rows", "wheel_membership_tests")
                      if k in subset[0][0]["methods"][method]}
            phases = {}
            for key in subset[0][1][method][0]:
                runs = zip(*(times[method] for _, times in subset))
                phases[key] = int(median(sum(run[key] for run in batch) for batch in runs))
            width[method] = dict(**counts, median_six_product_ns=phases)
        width["sign_faster_cpu_than"] = {
            m: sum(row["methods"]["sign_table"]["median_ns"]["cpu"] < row["methods"][m]["median_ns"]["cpu"]
                   for row, _ in subset) for m in ("wheel60", "prime_sieve")
        }
        for name in ("lazy_blocks", "interval_choice"):
            if name in methods:
                width[name]["faster_cpu_than"] = {
                    m: sum(row["methods"][name]["median_ns"]["cpu"] < row["methods"][m]["median_ns"]["cpu"]
                           for row, _ in subset) for m in methods if m != name
                }
        result[str(bits)] = width
    return result


def followup_report(check):
    cases, times = run_cases(1 if check else len(FOLLOWUP), followup=True)
    totals = {}
    for name, after in (("development", False), ("validation", True)):
        subset = [(r, t) for i, (r, t) in enumerate(zip(cases, times)) if (i % (2 * SAMPLES) >= SAMPLES) == after]
        totals[name] = summarize([r for r, _ in subset], [t for _, t in subset], FOLLOWUP)
    return dict(selection="Development: first six per width used to motivate cheaper setup. Validation: next six per width, labels 6–11, retained after the rules were frozen.",
                methods="Sorted positive residues modulo d are intersected with the wheel in each consecutive d-wide block. Cache a translated list only on its first visit among the 60 possible phases. Scan candidates in exactly the same order as the original CRT table.",
                selector="The interval_choice rule spends the same CF setup. With C the exact number of wheel positions in the public interval, it builds the lazy table only when 4*((d-1)//2) <= C and d meets the cap. C/4 is an equal-operation forecast from testing half the interval and saving half its divisions; no guarantee or fitted timing coefficient.",
                timing="All five methods rerun per product in five cyclic orders. Each method occupies each timing position once. Positive-residue sorting is included in jacobi_table; phase list construction is charged to lazy_table, exclusively of scan.",
                splits=totals, cases=cases)


def without_times(cases):
    for row in cases:
        for method in row["methods"].values():
            del method["median_ns"]
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write the timed report")
    mode.add_argument("--write-followup", action="store_true", help="update only the follow-up measurements in the saved report")
    mode.add_argument("--check", action="store_true", help="verify the saved counts and certificates")
    args = parser.parse_args()
    check_small_tables()
    if args.write_followup:
        saved = json.loads(RESULT.read_text())
        saved["followup"] = followup_report(False)
        RESULT.write_text(json.dumps(saved, indent=2) + "\n")
        return
    cases, times = run_cases(1 if args.check else len(ORDERS))
    prices = full_size_prices()
    if args.check:
        saved = json.loads(RESULT.read_text())
        replay = followup_report(True)
        if (without_times(cases) != without_times(saved["cases"]) or prices != saved["full_size_prices"]
                or without_times(replay["cases"]) != without_times(saved["followup"]["cases"])):
            raise ArithmeticError("saved work or certificate differs from the replay")
        print("Verified 24 distinct prime factorizations, eager/lazy stream counts, and both full-size prices.")
        return
    report = dict(input_source=str(INPUT.relative_to(ROOT)), seed=SEED.decode(),
                  selection="First six products by sample at each width, first two independently drawn distinct primes per sample. Searches read only N and width.",
                  wheel=WHEEL, cf_budget=BUDGET, max_table_period=MAX_TABLE_PERIOD, prime_sieve_block=BLOCK,
                  sign_table="Smallest eligible d from the fixed CF budget. Evaluate (x/d) once for 1 <= x <= (d-1)/2, select x or -x on opposite nonzero signs. Sort the CRT product with the 16 wheel classes; no Jacobi during scanning.",
                  timing="Six repetitions in all method orders per product. Cold cached base-prime lists each time. Total CPU and wall include input bounds, setup and streaming to the first factor; segmented base sieving and crossing off are inside scan. Other phase covers bounds, wheel and bookkeeping; total also includes return and local cleanup. Excludes interpreter startup, holdout loading and Lean verification.",
                  machine=dict(os=platform.system(), architecture=platform.machine(), python=platform.python_version()),
                  cases=cases, width_totals=summarize(cases, times),
                  full_size_source=str(LARGE.relative_to(ROOT)),
                  full_size_pricing="Minimum eligible d in the published 2^20-step CF search. Verify its root with N. Counts price the explicit positive-unit loop and sorted 60d-period table; no full-size table was built. Its 8*phi(d) rows exceed 8*d/13 by quotientBudget_wheel_ratio. Bytes assume packed, fixed-width residues with no list/sort overhead; this is specific to materializing that table.",
                  full_size_prices=prices, followup=followup_report(False))
    content = json.dumps(report, indent=2) + "\n"
    if args.write:
        RESULT.write_text(content)
    else:
        print(content, end="")


if __name__ == "__main__":
    main()
