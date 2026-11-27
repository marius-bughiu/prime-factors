"""Compare prime trial division with Jacobi filters on the same ordered primes."""

import argparse
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.mixed_ratio_heights import jacobi
from experiments.reciprocal_anchor import collect_anchors
from experiments.reciprocal_fermat_holdout import SEED, inputs
from scripts.factor import primes_through, render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
BUDGET = 256
METHODS = (0, 1, 2, 4, 8)
BLOCK = 32768
REPORT = ROOT / "research/split-prime-holdout.json"


def interval_primes(lo, hi):
    """Segment the inclusive physical interval, streaming its primes in order."""
    lo = max(lo, 2)
    if lo > hi:
        return
    base = primes_through(isqrt(hi))
    for start in range(lo, hi + 1, BLOCK):
        stop = min(start + BLOCK, hi + 1)
        flags = bytearray([1]) * (stop - start)
        for p in base:
            first = max(p*p, ((start + p - 1) // p)*p)
            if first < stop:
                flags[first-start::p] = bytes(1 + (stop-1-first)//p)
        for offset, prime in enumerate(flags):
            if prime:
                yield start + offset


def elapsed(start):
    cpu, wall = start
    return dict(cpu_ns=process_time_ns() - cpu, wall_ns=perf_counter_ns() - wall)


def scan(n, bits, requested):
    """Every method is given only the product and factor width."""
    primes_through.cache_clear()
    started = process_time_ns(), perf_counter_ns()
    limit = 2**bits - 1
    lo, hi = max(2**(bits-1), (n-1)//limit+1), isqrt(n)
    steps = dict(cf_steps=0)
    anchors = []
    if requested:
        anchors = collect_anchors(n, BUDGET, count=requested, negative_only=True, stats=steps)
    setup = elapsed(started)
    if anchors and "setup_factor" in anchors[0]:
        factor = anchors[0]["setup_factor"]
        pair = sorted((factor, n//factor))
        return dict(
            moduli=[], cf_steps=steps["cf_steps"], status="setup_split",
            pair=[str(p) for p in pair], first=[0, 0, 0], full=None,
        ), dict(setup=setup, first=setup, full=None)

    moduli = [a["period"] for a in anchors]
    status = "complete" if len(moduli) == requested else "fewer_anchors"
    visited = symbols = divisions = 0
    first_work = first_time = pair = None
    for p in interval_primes(lo, hi):
        visited += 1
        for d in moduli:
            symbols += 1
            if jacobi(p, d) != 1:
                break
        else:
            divisions += 1
            if n % p == 0 and first_work is None:
                pair = [str(p), str(n//p)]
                first_work = [visited, symbols, divisions]
                first_time = elapsed(started)
    complete = elapsed(started)
    if first_work is None:
        raise ArithmeticError("the physical prime interval failed to recover a split")
    return dict(
        moduli=moduli, cf_steps=steps["cf_steps"], status=status, pair=pair,
        first=first_work, full=[visited, symbols, divisions],
    ), dict(setup=setup, first=first_time, full=complete)


def certificate(n, pair):
    text = render_certificate(n, [int(p) for p in pair])
    path = ROOT / "build/split-prime-holdout" / f"Factor{n}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    verify_file(path)
    return sha256(text.encode()).hexdigest()


def experiment(bits, repetitions):
    sample, expected = inputs(bits)[0]
    n = expected[0] * expected[1]
    baseline = {}
    timings = {str(k): [] for k in METHODS}
    for rep in range(repetitions):
        order = METHODS[rep:] + METHODS[:rep]
        for k in order:
            key = str(k)
            result, duration = scan(n, bits, k)
            if result["pair"] != [str(p) for p in expected]:
                raise ArithmeticError(f"factorization mismatch at {bits} bits with {k} filters")
            if key in baseline and result != baseline[key]:
                raise ArithmeticError("the amount of mathematical work changed between timing repeats")
            baseline[key] = result
            timings[key].append(duration)
    direct = baseline["0"]
    for search in baseline.values():
        if search["status"] != "setup_split" and (
            search["first"][0] != direct["first"][0] or search["full"][0] != direct["full"][0]
        ):
            raise ArithmeticError("a filter changed the visited-prime stream")
    for key, runs in timings.items():
        baseline[key]["median_times"] = {
            phase: {name: int(median(run[phase][name] for run in runs)) for name in ("cpu_ns", "wall_ns")}
            for phase in ("setup", "first", "full") if runs[0][phase] is not None
        }
    return dict(
        bits=bits, sample=sample, n=str(n), lower=max(2**(bits-1), (n-1)//(2**bits-1)+1),
        upper=isqrt(n), methods=baseline, certificate_sha256=certificate(n, direct["pair"]),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--output", type=Path, help="write the full freshly timed report")
    modes.add_argument("--check", action="store_true", help="replay the counts and prime certificates")
    args = parser.parse_args()
    repeats = 1 if args.check else len(METHODS)
    cases = [experiment(bits, repeats) for bits in (20, 24)]
    if args.check:
        saved = json.loads(REPORT.read_text())["cases"]
        for row in cases + saved:
            for method in row["methods"].values():
                method.pop("median_times")
        if cases != saved:
            raise ArithmeticError("replayed results differ from the frozen experiment")
        print("Verified two complete prime censuses and two Lean prime factorizations.")
        return
    result = dict(
        seed=SEED.decode(), selection="first existing sample at each factor width",
        cf_budget=BUDGET, sieve_block_integers=BLOCK, repetitions=repeats,
        timing="median from method entry; cold base-prime cache, anchor setup and segmented sieve included; input generation and Lean verification excluded",
        work_columns=["visited_primes", "jacobi_evaluations", "trial_divisions"],
        platform=dict(python=platform.python_version(), machine=platform.machine(), os=platform.system()),
        cases=cases,
    )
    content = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(content)
    else:
        print(content, end="")


if __name__ == "__main__":
    main()
