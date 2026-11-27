"""Compare three traversals of the same bounded difference-of-squares multipliers."""

import argparse
from collections import Counter
from hashlib import sha256
from heapq import heappop, heappush
from itertools import islice
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.rectangular_root_windows import (
    SQUARE, WHEEL, bounds, interval, multiplier_ratio, primitive_classes, product_count_bound,
    weight_products,
)
from experiments.rectangular_weight_panel import SCALE
from experiments.split_prime_holdout import certificate

ROOT = Path(__file__).resolve().parents[1]
POLICIES = ("eager_sorted", "lazy_sorted", "pair_order")


def starts(t, limit, scale, excess, work):
    """Increasing first coprime product of each nonempty lane of one parity family."""
    if t == 1 and limit >= 1:
        work["lane_starts"] += 1
        yield (1, 1, 1, 1, min(limit, (scale+excess)//scale))
    if excess == 0:
        return
    gap = 2 if t == 1 else 1
    step = 2 if t == 1 else 1
    a = max(1, (scale*gap+excess-1)//excess)
    if t == 1:
        a = max(3, a | 1)
    while t*a*(a+gap) <= limit:
        first = a+gap
        last = min(limit//(t*a), (scale+excess)*a//scale)
        work["lane_starts"] += 1
        yield (t*a*first, t, a, first, last)
        a += step


def next_entry(k, t, a, b, last, work):
    """Advance a single lane after its first, already coprime pair."""
    for candidate in range(b+2, last+1, 2):
        work["subsequent_gcds"] += 1
        if gcd(a, candidate) == 1:
            return (k+(candidate-b)*t*a, t, a, candidate, last)
    return None


def lazy_sorted(limit, scale, excess, work):
    """Merge only active lanes; keep one pending beginning from each family."""
    families = {t: starts(t, limit, scale, excess, work) for t in (1, 4)}
    pending, active = [], []
    for family in families.values():
        first = next(family, None)
        if first is not None:
            heappush(pending, first)
    previous = 0
    while pending or active:
        if pending and (not active or pending[0][0] <= active[0][0]):
            entry = heappop(pending)
            first = next(families[entry[1]], None)
            if first is not None:
                heappush(pending, first)
        else:
            entry = heappop(active)
        work["peak_lanes"] = max(work["peak_lanes"], 1+len(pending)+len(active))
        work["coprime_pairs"] += 1
        if entry[0] != previous:
            previous = entry[0]
            yield previous
        successor = next_entry(*entry, work)
        if successor is not None:
            heappush(active, successor)


def pair_order(limit, scale, excess, work):
    """Visit each eligible coprime pair once. Equal products get separate row scans."""
    for t in (1, 4):
        for entry in starts(t, limit, scale, excess, work):
            work["peak_lanes"] = 1
            while entry is not None:
                work["coprime_pairs"] += 1
                yield entry[0]
                entry = next_entry(*entry, work)


def eager_lanes(limit, scale, excess):
    """Number of generator objects retained in the original merge's outer list."""
    odd_count = (isqrt(limit)+1)//2
    if excess == 0:
        return odd_count
    last = (isqrt(1+4*(limit//4))-1)//2
    first = max(1, (scale+excess-1)//excess)
    return odd_count+max(0,last-first+1)


def stream(name, limit, scale, excess, work):
    if name == "eager_sorted":
        work["peak_lanes"] = eager_lanes(limit, scale, excess)
        return weight_products(limit, scale, excess, work)
    if name == "lazy_sorted":
        return lazy_sorted(limit, scale, excess, work)
    if name == "pair_order":
        return pair_order(limit, scale, excess, work)
    raise ValueError(name)


def scan(n, bits, policy, row_cap=None, position_cap=None):
    """All policies use the same D=1 search. Store only the first factor witness."""
    cpu, wall = process_time_ns(), perf_counter_ns()
    y_limit, h, k_limit = bounds(n, 1)
    if h+y_limit >= n:
        raise ValueError("direct row gcd requires H+Y<N")
    limit = k_limit if row_cap is None else min(row_cap, k_limit)
    excess = multiplier_ratio(n, h, bits, SCALE)
    classes = primitive_classes(n, 1)
    work = Counter()
    first = None
    first_times = [None, None]
    for k in stream(policy, limit, SCALE, excess, work):
        work["visited_rows"] += 1
        if k % WHEEL not in classes:
            continue
        work["admitted_rows"] += 1
        lo, hi = interval(n, 1, k, y_limit, h)
        if position_cap is not None:
            work["skipped_positions"] += max(0,hi-lo+1-position_cap)
            hi = min(hi, lo+position_cap-1)
        kn = k*n
        for y in range(lo, hi+1):
            work["coordinates"] += 1
            square = y*y-kn
            if square % WHEEL not in SQUARE:
                continue
            work["isqrts"] += 1
            x = isqrt(square)
            if x*x != square:
                continue
            g = gcd(y-x,n)
            work["row_gcds"] += 1
            if not 1<g<n or n%g:
                raise ArithmeticError("a positive short row failed its proper gcd assertion")
            if first is None:
                first_times = [process_time_ns()-cpu, perf_counter_ns()-wall]
                first = dict(k=k, x=x, y=y, pair=list(map(str,sorted((g,n//g)))),
                             visited=work["visited_rows"], coordinates=work["coordinates"],
                             isqrts=work["isqrts"], peak_lanes=work["peak_lanes"])
    times = first_times+[process_time_ns()-cpu, perf_counter_ns()-wall]
    return dict(first=first, work=dict(work)), times


def trace(n, bits, row_cap=None):
    """Untimed equality and sequence diagnostics; these temporary lists are excluded from search."""
    _,h,k_limit = bounds(n, 1)
    limit = min(k_limit,row_cap) if row_cap is not None else k_limit
    excess = multiplier_ratio(n, h, bits, SCALE)
    eager, lazy, direct = (list(stream(p,limit,SCALE,excess,Counter())) for p in POLICIES)
    if eager != lazy or eager != sorted(set(direct)) or any(a>=b for a,b in zip(eager,eager[1:])):
        raise ArithmeticError("sorted streams or eligible sets disagree")
    bound = product_count_bound(limit,SCALE,excess)
    if len(direct)>bound:
        raise ArithmeticError("pair visits exceed public pair-count bound")
    def digest(numbers):
        return sha256(",".join(map(str,numbers)).encode()).hexdigest()
    return dict(limit=str(limit), excess=excess, distinct=len(eager), pairs=len(direct),
                repeated=len(direct)-len(eager), bound=str(bound),
                descending_steps=sum(a>b for a,b in zip(direct,direct[1:])),
                sorted_prefix=eager[:16], pair_prefix=direct[:16], sorted_sha256=digest(eager),
                pair_order_sha256=digest(direct))


def compare(n, bits, sample, repeats, row_cap=None, position_cap=None):
    order_trace = trace(n,bits,row_cap)
    methods, timings = {}, {p: [] for p in POLICIES}
    for rep in range(repeats):
        shift = (rep+sample)%len(POLICIES)
        for p in POLICIES[shift:]+POLICIES[:shift]:
            result, times = scan(n,bits,p,row_cap,position_cap)
            timings[p].append(times)
            if methods.setdefault(p,result) != result:
                raise ArithmeticError("nondeterministic search")
    for p, data in methods.items():
        recorded = timings[p]
        data["medians_ns"] = {
            key: int(median(values)) if values[0] is not None else None
            for key, values in zip(("first_cpu","first_wall","full_cpu","full_wall"), zip(*recorded))
        }
    if methods["eager_sorted"]["first"] != methods["lazy_sorted"]["first"]:
        ea, la = methods["eager_sorted"]["first"], methods["lazy_sorted"]["first"]
        if not ea or not la or any(ea[key]!=la[key] for key in ea if key!="peak_lanes"):
            raise ArithmeticError("first sorted witness disagrees")
    return dict(n=str(n),bits=bits,trace=order_trace,methods=methods)


def unrestricted_prefix(n,bits,count,cap):
    _,h,limit = bounds(n,1)
    excess = multiplier_ratio(n,h,bits,SCALE)
    out = dict(domain_limit=str(limit), eager_initial_lanes=str(eager_lanes(limit,SCALE,excess)))
    control = list(islice(weight_products(cap,SCALE,excess,Counter()),count))
    for p in ("lazy_sorted","pair_order"):
        work = Counter()
        before = process_time_ns()
        values = list(islice(stream(p,limit,SCALE,excess,work),count))
        elapsed = process_time_ns()-before
        if p=="lazy_sorted" and values!=control:
            raise ArithmeticError("unrestricted-domain first entries differ from capped sorted stream")
        out[p] = dict(entries=len(values),last=values[-1],prefix=values[:16],work=dict(work),
                      generator_cpu_ns=elapsed)
    return out


def check_reference(case, old):
    """The original ordered scanner supplies an independent row and square-test ledger."""
    before = old["methods"]["weights"]["data"]
    after = case["methods"]["eager_sorted"]
    for earlier, current in (("rows","visited_rows"),("intervals","admitted_rows"),
                             ("coordinates","coordinates"),("square_tests","isqrts")):
        if before["work"][earlier] != after["work"].get(current,0):
            raise ArithmeticError("new ordered row ledger disagrees with the earlier scanner")
    if before["first"] is None:
        if after["first"] is not None:
            raise ArithmeticError("earlier scanner missed an ordered hit")
    else:
        a, b = before["first"], after["first"]
        if not b or (a["multiplier"],int(a["x"]),int(a["y"])) != (b["k"],b["x"],b["y"]):
            raise ArithmeticError("new scan disagrees with the earlier search")


def report(repeats):
    reference_path = ROOT/"research/rectangular-multiplier-products.json"
    previous = json.loads(reference_path.read_text())
    cases = []
    for old in previous["panel"]:
        n = int(old["n"])
        case = compare(n,old["bits"],old["sample"],repeats)
        expected = old["factors"]
        for data in case["methods"].values():
            if data["first"]["pair"]!=expected:
                raise ArithmeticError("recovered factors disagree with certified panel")
        check_reference(case, old)
        new_first = case["methods"]["eager_sorted"]["first"]
        case["sample"] = old["sample"]
        case["certificate"] = certificate(n,new_first["pair"])
        if case["certificate"]!=old["certificate"]:
            raise ArithmeticError("Lean certificate changed")
        cases.append(case)
    controls = []
    for i,old in enumerate(previous["full_size"]):
        n = int(old["n"])
        case = compare(n,1024,i,repeats,65536,1)
        check_reference(case, old)
        case["id"] = old["id"]
        case["unrestricted_generation"] = unrestricted_prefix(n,1024,64,65536)
        for data in case["methods"].values():
            if data["first"]:
                data["certificate"] = certificate(n,data["first"]["pair"])
        controls.append(case)
    return dict(panel=cases,controls=controls,repeats=repeats,machine=platform.machine(),
                python=platform.python_version(),reference=str(reference_path.relative_to(ROOT)),
                cost="Generator setup, 64-residue table, all rows and coordinates, integer roots and gcd. Median process and wall nanoseconds, schedules rotated. Exact sequence comparisons and certificate checks are untimed.",
                memory="Peak retained weight lanes only. Eager outer list counted exactly by formula; lazy counts pending, active and current; pair order retains one. Input and output integers have size-dependent storage.",
                caps="Both full-size controls use numerical k<=65536 and at most one y per row. Unrestricted-domain control generates only the first 64 entries and does no square tests.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--repetitions",type=int,default=3)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("expected at least one repetition")
    encoded = json.dumps(report(args.repetitions),indent=2)+"\n"
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded,end="")
