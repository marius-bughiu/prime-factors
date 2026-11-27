"""Compare complete quotient sweeps on pre-existing product lists."""

import json
import platform
import argparse
import sys
from pathlib import Path
from statistics import median
from time import process_time

if __package__:
    from .quotient_search import Strip, search as tangent, wheel_lattices
    from .secant_quotient_cells import ParallelStrip, plan, safe_width, search as secant, secant_lattices, sweep
else:
    from quotient_search import Strip, search as tangent, wheel_lattices
    from secant_quotient_cells import ParallelStrip, plan, safe_width, search as secant, secant_lattices, sweep


ROOT = Path(__file__).resolve().parents[1]
COUNTERS = ("blocks", "initial_strip_points", "euclidean_steps", "moment_states", "quadratic_solves")
METHODS = {"tangent": lambda n: tangent(n, wheel=210),
           "equal_area": secant, "maximum_width": lambda n: secant(n, max_width=True)}


def compare(inputs, repetitions=5):
    results = {}
    timings = {name: [] for name in METHODS}
    names = list(METHODS)
    for repetition in range(repetitions):
        for name in names[repetition % 3:] + names[:repetition % 3]:
            start = process_time()
            rows = [METHODS[name](n) for n, _ in inputs]
            timings[name].append(process_time()-start)
            for row, (_, expected) in zip(rows, inputs):
                if row["pairs"] != expected:
                    raise ArithmeticError(f"wrong factor pairs in {name} on {row['n']}")
            results[name] = {key: sum(r[key] for r in rows) for key in COUNTERS}
            results[name]["widths"] = [r["width"] for r in rows]
    for name, result in results.items():
        result["cpu_seconds"] = timings[name]
        result["median_cpu_seconds"] = median(timings[name])
    return {"products": [str(n) for n, _ in inputs], "methods": results}


def fresh_window():
    fixture = json.loads((ROOT / "benchmarks/endpoint-offset-product.json").read_text())
    n = int(next(row["n"] for row in fixture if row["id"] == "endpoint-offset-fresh-2048"))
    low, high, _, wheel, _ = plan(n, 210)
    length = high-low+1
    baseline_width = safe_width(n, low, length, wheel, 1)
    start = (low+high)//2
    stop = min(high, start+4*baseline_width-1)
    # The old moment recurrence uses Python recursion for Euclidean steps.
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 8*n.bit_length()))
    data = {"n": str(n), "wheel": wheel, "start": str(start), "stop": str(stop), "methods": {}}
    for name, coef, shape, lattices in [("tangent", 1, Strip, wheel_lattices),
                                        ("equal_area", 4, ParallelStrip, secant_lattices),
                                        ("maximum_width", 8, ParallelStrip, secant_lattices)]:
        width = safe_width(n, low, length, wheel, coef)
        before = process_time()
        row = sweep(n, start, stop, width, lattices(n, wheel), shape)
        row["cpu_seconds"] = process_time()-before
        row["full_band_planned_cells"] = str(row["residue_classes"]*((length+width-1)//width))
        del row["n"]
        data["methods"][name] = row
    # Use the separately certified factors only to cross-check the completed search.
    control = json.loads((ROOT / "research/certified-control.json").read_text())
    p, q = sorted(int(chain[-1]["prime"]) for chain in control["chains"].values())
    if p*q != n:
        raise ArithmeticError("certified control does not match the tested product")
    expected = [[str(p), str(q)]] if start <= p <= stop else []
    for row in data["methods"].values():
        if row["pairs"] != expected:
            raise ArithmeticError("matched bounded interval missed an expected result")
    data["smaller_prime_in_window"] = bool(expected)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fresh-window", action="store_true",
                        help="run four baseline widths on the 2048-bit fresh control")
    if parser.parse_args().fresh_window:
        print(json.dumps(fresh_window(), indent=2))
        return
    data = {"wheel": 210, "repetitions": 5, "python": platform.python_version(),
            "platform": platform.platform(), "groups": {}}
    fixture = json.loads((ROOT / "benchmarks/quotient-search.json").read_text())[0]
    inputs = [(int(fixture["n"]), [fixture["factors"]])]
    data["groups"]["published_41_bit"] = compare(inputs)
    for file, key in [("quartic-lane-holdout", "expected_factors"), ("midpoint-weight-holdout", "factors")]:
        source = json.loads((ROOT / f"research/{file}.json").read_text())
        data["groups"][file] = compare([(int(r["n"]), [r[key]]) for r in source["rows"]])
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
