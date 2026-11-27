"""Order the unit-reduced signed norm curves using their exact complete block counts."""

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.mixed_ratio_heights import jacobi
from experiments.phase_interval import cube_radius
from experiments.signed_norm_arcs import axes, charts, integer_arc, point_scan, possible, unit_multiplier
from experiments.split_prime_holdout import certificate


ROOT = Path(__file__).resolve().parents[1]
TARGET = (0, -1, 2, -2, 3, -3, 6, -6)
POLICIES = ("original", "sorted", "cheapest_line", "round_robin")
LINES = tuple(t for t in combinations(range(1, 8), 3) if t[0] ^ t[1] ^ t[2] == 0)


@dataclass
class Curve:
    mask: int
    d: int
    m: int
    feasible: bool
    charts: list
    blocks: int
    positions: int


def prepare(n, mask):
    d = TARGET[mask]
    m = unit_multiplier(n, d)
    feasible = all(m*n % q in possible(d, q) for q in (16, 3))
    records = []
    positions = blocks = 0
    if feasible:
        for hyperbolic, a, b, swapped, last in charts(n, d, m, Counter(), "unit"):
            width = max(1, cube_radius(8*isqrt(b*abs(m)*n)//a))
            records.append((hyperbolic, a, b, swapped, last, width))
            positions += last
            blocks += (last+width-1)//width
    return Curve(mask, d, m, feasible, records, blocks, positions)


def eligible(n):
    keys = [mask for mask in range(1, 8) if jacobi(TARGET[mask], n) == 1]
    if len(keys) not in (3, 7):
        raise ValueError("expected public product coprime to 6")
    return keys


def cheapest_eligible_line(costs):
    """Accept a public cost for each eligible signed mask and return three masks."""
    return min((line for line in LINES if all(mask in costs for mask in line)),
               key=lambda line: (sum(costs[mask] for mask in line), line))


def plan(n, policy):
    keys = eligible(n)
    available = keys[:3] if policy in ("original", "sorted") else keys
    curves = {k: prepare(n, k) for k in available}
    if policy == "original":
        return list(curves.values())
    if policy == "sorted":
        line = keys[:3]
    elif policy in ("cheapest_line", "round_robin"):
        line = cheapest_eligible_line({k: c.blocks for k, c in curves.items()})
    else:
        raise ValueError(policy)
    return sorted((curves[k] for k in line), key=lambda c: (c.blocks, c.mask))


def blocks(n, c, counts):
    for hyperbolic, a, b, swapped, last, width in c.charts:
        for lo in range(1, last+1, width):
            hi = min(last, lo+width-1)
            points = []
            for u, z in integer_arc(abs(c.m)*n, a, b, lo, hi, counts, hyperbolic=hyperbolic):
                if hyperbolic or not swapped or a*u*u != b*z*z:
                    points.append((z, u) if swapped else (u, z))
            yield points


def accept(n, c, points, remembered):
    for x, y in points:
        if x*x-c.d*y*y != c.m*n:
            raise ArithmeticError("point missed the configured curve")
        g = gcd(y, n)
        if g == 1:
            r = x*pow(y, -1, n) % n
            if (r*r-c.d) % n:
                raise ArithmeticError("root check failed")
            first = remembered.setdefault(c.mask, r)
            g = gcd(r-first, n)
        if 1 < g < n:
            return dict(factor=str(g), d=c.d, m=c.m, point=[str(x), str(y)])
    return None


def search(n, policy, cap=None):
    curves = plan(n, policy)
    counts, remembered = Counter(), {}
    streams = deque((c, blocks(n, c, counts)) for c in curves)
    used = Counter()
    hit = None
    for c in curves:
        if c.feasible:
            hit = accept(n, c, axes(n, c.d, c.m, counts, "unit"), remembered)
            if hit:
                break
    charged = 0
    while streams and not hit and (cap is None or charged < cap):
        c, stream = streams[0]
        points = next(stream, None)
        if points is None:
            streams.popleft()
            continue
        charged += 1
        used[c.mask] += 1
        hit = accept(n, c, points, remembered)
        if policy == "round_robin":
            streams.rotate(-1)
    return dict(order=[c.mask for c in curves], targets=[c.d for c in curves],
                complete_blocks=sum(c.blocks for c in curves), blocks=charged,
                blocks_per_mask={str(k): v for k, v in sorted(used.items())},
                line_tests=counts["line_tests"], hit=hit)


def individually(n):
    """Run each curve to its first split (or exhaustion) with the existing reference walker."""
    results = {}
    for mask in eligible(n):
        c = prepare(n, mask)
        work, roots, hit = Counter(), {}, None
        for point in point_scan(n, c.d, c.m, "integer_arcs", work, domain="unit"):
            hit = accept(n, c, [point], roots)
            if hit:
                break
        first = work["blocks"] if hit else None
        if first is None and work["blocks"] != c.blocks or first is not None and first > c.blocks:
            raise ArithmeticError("whole curve cost disagrees with existing chart walker")
        results[str(mask)] = dict(target=c.d, total=c.blocks, first=first)
    return results


def predict(order, oracle, race):
    records = [oracle[str(k)] for k in order]
    if race:
        t, winner = min((r["first"], i) for i, r in enumerate(records) if r["first"] is not None)
        if t == 0:
            return 0
        return sum(min(r["total"], t-1+int(i <= winner)) for i, r in enumerate(records))
    spent = 0
    for r in records:
        if r["first"] is not None:
            return spent+r["first"]
        spent += r["total"]
    raise ArithmeticError("guaranteed line did not split")


def cover_check():
    for selected in range(128):
        masks = [d for d in range(1, 8) if (selected >> (d-1)) & 1]
        has_line = any(all(m in masks for m in l) for l in LINES)
        guarantees = all(any(bin(s & m).count("1") % 2 == 0 for m in masks) for s in range(8))
        if guarantees != has_line:
            raise ArithmeticError("Fano line condition failed")


def inputs():
    for label, total, domain in (("main", 12, "signed-curve-order-v1"),
                                 ("all_positive", 6, "signed-curve-order-all-positive-v1")):
        for bits in (16, 20):
            seed = f"{domain}/{bits}".encode()
            accepted = sample = 0
            while accepted < total:
                p, q = (draw_prime(side, sample, bits=bits, seed=seed) for side in (b"p", b"q"))
                n = p*q
                if p != q and (label == "main" or n % 24 == 1):
                    yield label, bits, sample, n
                    accepted += 1
                sample += 1


def panel(repeats):
    rows = []
    for label, bits, sample, n in inputs():
        oracle = individually(n)
        timings = {p: [] for p in POLICIES}
        results = {}
        for rep in range(repeats):
            shift = sample % len(POLICIES)
            order = POLICIES[shift:] + POLICIES[:shift]
            for policy in (order if rep % 2 == 0 else reversed(order)):
                possible.cache_clear()
                timer = process_time_ns()
                result = search(n, policy)
                timings[policy].append(process_time_ns()-timer)
                if result["blocks"] != predict(result["order"], oracle, policy == "round_robin"):
                    raise ArithmeticError("independent block-level replay disagrees")
                if not result["hit"] or policy in results and results[policy] != result:
                    raise ArithmeticError("search missed a split or was nondeterministic")
                results[policy] = result
        g = int(results["original"]["hit"]["factor"])
        pair = sorted((g, n//g))
        if n % g or any(int(v["hit"]["factor"]) not in pair for v in results.values()):
            raise ArithmeticError("schedules disagree on prime factors")
        for p in POLICIES:
            results[p]["median_cpu_ns"] = int(median(timings[p]))
        rows.append(dict(panel=label, bits=bits, sample=sample, n=str(n), pair=list(map(str, pair)),
                         curves=oracle, policies=results, certificate_sha256=certificate(n, pair)))
    return rows


def totals(rows):
    result = {}
    for label in ("main", "all_positive"):
        for bits in (16, 20):
            part = [r for r in rows if r["panel"] == label and r["bits"] == bits]
            values = {}
            for policy in POLICIES:
                work = [r["policies"][policy] for r in part]
                baseline = [r["policies"]["original"]["blocks"] for r in part]
                values[policy] = dict(blocks=sum(w["blocks"] for w in work),
                                      lines=sum(w["line_tests"] for w in work),
                                      cpu_ns=sum(w["median_cpu_ns"] for w in work),
                                      fewer=sum(w["blocks"] < b for w, b in zip(work, baseline)),
                                      more=sum(w["blocks"] > b for w, b in zip(work, baseline)))
            result[f"{label}-{bits}"] = values
    return result


def controls():
    out = []
    for fixture in json.loads((ROOT/"benchmarks/projected-divisor-wheel.json").read_text()):
        n = int(fixture["n"])
        if n.bit_length() == 2048:
            c = {k: prepare(n, k) for k in eligible(n)}
            lines = {",".join(map(str, l)): str(sum(c[k].blocks for k in l))
                     for l in LINES if all(k in c for k in l)}
            out.append(dict(id=fixture["id"], n=str(n), mod24=n%24, line_blocks=lines,
                            curves={str(k):dict(target=v.d,positions=str(v.positions),blocks=str(v.blocks))
                                    for k,v in c.items()},
                            trials={p: search(n, p, 64) for p in POLICIES}))
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repetitions", type=int, default=2)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("need a positive repetition count")
    cover_check()
    cases = panel(args.repetitions)
    report = dict(main_domain="signed-curve-order-v1/<bits>", conditioned_domain="signed-curve-order-all-positive-v1/<bits>",
                  selection="first twelve distinct-prime pairs per width; separately first six with N%24=1 on independent streams",
                  timings="CPU per call includes pricing, axes, scheduling, root construction and gcd, using alternating order and cold residue tables. Every visit charges one chart block including its lines.",
                  python=platform.python_version(), machine=platform.machine(), repetitions=args.repetitions,
                  lines=LINES, controls=controls(), totals=totals(cases), cases=cases)
    text = json.dumps(report, indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
