"""Compare one-prime and full-modulus matches of centered weighted powers."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.weighted_global_trace import FIXTURE, row_squares, schedule, trace_search
from experiments.weighted_stride_search import geometric_values, root_polynomial
from scripts.factor import render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "research/local-gap-polynomial.json"
LOCAL = ("individual", "row_product", "geometric", "derivative")
METHODS = ("square", "global", *LOCAL, "ordinary")


class Readouts:
    def __init__(self, n, start):
        self.n = n
        self.start = start
        self.first = None
        self.divisors = set()
        self.work = Counter()

    def check(self, value, stage):
        g = gcd(value, self.n)
        if g == 1:
            outcome = "one"
        elif g == self.n:
            outcome = "whole"
        else:
            outcome = "proper"
            self.divisors.add(g)
            if self.first is None:
                self.first = process_time_ns() - self.start
        self.work[f"{stage}_{outcome}"] += 1
        return g


def keys(n, gaps, coordinates, out):
    """X=u^s*(u^(h+1))^-c and Y=v^d, v=u^h. The base u=2 is a unit."""
    u, h = 2, n // 2
    if gcd(u, n) != 1:
        raise ValueError("the panel requires odd semiprimes")
    work = out.work
    work["base_gcd"] += 1
    v = pow(u, h, n)
    vinv, center = pow(v, -1, n), pow(u * v % n, -1, n)
    work.update(large_powers=1, inversions=2, key_multiplications=1)
    oriented, current, inverse = {0: 1}, 1, 1
    for i in range(1, max(gaps, default=0) + 1):
        current, inverse = current * v % n, inverse * vinv % n
        work["key_multiplications"] += 2
        oriented[i], oriented[-i] = current, inverse
    for d in gaps:
        out.check(oriented[d] * oriented[d] - 1, "right_precheck")
    lookup = {e: oriented[e] for e in sorted({z for d in gaps for z in (d, -d)})}
    centers, previous = {}, {}
    left = []
    for _, _, c, s, _ in coordinates:
        if c in previous and s - previous[c][0] in (1, 2):
            value = previous[c][1] * (u if s == previous[c][0] + 1 else u*u) % n
            work["key_multiplications"] += 1
        else:
            if c not in centers:
                centers[c] = pow(center, c, n)
                work["center_powers"] += 1
            value = pow(u, s, n) * centers[c] % n
            work["coordinate_powers"] += 1
            work["key_multiplications"] += 1
        previous[c] = (s, value)
        left.append(value)
    return v, left, lookup


def resolve(n, differences, out):
    """The input product has gcd N and every individual difference is nonzero mod N.

    For distinct-prime semiprimes both hidden primes occur among the differences.
    Bisect to exhibit a proper gcd. If the tested half is clear, move to its
    complement. A single whole-modulus leaf is impossible after exclusion.
    """
    lo, hi = 0, len(differences)
    while hi - lo > 1:
        mid = (hi + lo) // 2
        product = 1
        for j in range(lo, mid):
            product = product * differences[j] % n
        out.work["refine_multiplications"] += mid - lo
        g = out.check(product, "bisect")
        if 1 < g < n:
            out.divisors.add(n // g)
            return
        if g == n:
            hi = mid
        else:
            lo = mid
    raise ArithmeticError("a nonzero single residue cannot be zero modulo N")


def shifted_grid(poly, v, radius, n, out):
    """F(v^-D),...,F(v^D) by coefficient shift and one geometric convolution."""
    factor = pow(v, -radius, n)
    power, shifted = 1, []
    for c in poly:
        shifted.append(c * power % n)
        power = power * factor % n
    count = 2 * radius + 1
    degree = len(poly) - 1
    out.work.update(grid_convolutions=1, grid_convolution_inputs=2*degree+count+1,
                    grid_points=count, grid_shift_powers=1,
                    grid_multiplications=2*len(poly) + len(poly) + count
                    + 2*(degree+count + max(count, degree+1)), grid_inversions=1)
    return geometric_values(shifted, v, count, n)


def local_search(name, n, left, signed, v, out):
    right = list(dict.fromkeys(signed.values()))
    work = out.work
    if name == "individual":
        for x in left:
            for y in right:
                out.check(x-y, "leaf")
        return
    if name == "row_product":
        for x in left:
            value = 1
            for y in right:
                if y != x:
                    value = value * (x-y) % n
                    work["row_multiplications"] += 1
            if out.check(value, "row") == n:
                resolve(n, [x-y for y in right if x != y], out)
        return

    if not left or not right:
        return
    # A repeated full-modulus left residue gives the same individual gcds.
    poly = root_polynomial(left, n, stats=work)
    radius = max(map(abs, signed))
    values = shifted_grid(poly, v, radius, n, out)
    left_set = set(left)
    first_exponent = {}
    for e, y in signed.items():
        first_exponent.setdefault(y, e)
    overlaps = left_set.intersection(right)
    work["global_equal_cells"] = len(overlaps)
    derivative_values = None
    if name == "derivative" and overlaps:
        derivative = [j * poly[j] % n for j in range(1, len(poly))]
        work["derivative_coefficients"] = len(derivative)
        derivative_values = shifted_grid(derivative, v, radius, n, out)

    for y, e in first_exponent.items():
        if derivative_values is not None and y in overlaps:
            value = derivative_values[e+radius]
            work["derivative_queries"] += 1
        else:
            value = values[e+radius]
        if out.check(value, "column") != n:
            continue
        if name == "geometric" and y in overlaps:
            # The ordinary product is forced to zero. Replay the other cells.
            for x in left:
                if x != y:
                    out.check(x-y, "replay")
        else:
            resolve(n, [x-y for x in left if x != y], out)


def run_method(name, n, bits, limit, per_row):
    start = process_time_ns()
    out = Readouts(n, start)
    gaps, coordinates, common = schedule(n, bits, limit, per_row)
    scheduled = process_time_ns()
    out.work["coordinate_visits"] = len(coordinates)
    setup_divisors = []
    if name in ("square", "ordinary"):
        rows = dict.fromkeys((k, y) for k, y, _, _, _ in coordinates)
        if name == "ordinary":
            first = isqrt(n-1)+1
            out.work["ordinary_start_isqrt"] += 1
            rows = ((1, y) for y in range(first, first+len(rows)))
        prepared = process_time_ns()
        for k, y in rows:
            z = y*y-k*n
            x = isqrt(z)
            out.work["square_tests"] += 1
            if x*x == z:
                out.check(y-x, "square_readout")
                out.check(y+x, "square_readout")
    else:
        v, all_left, signed = keys(n, gaps, coordinates, out)
        left = list(dict.fromkeys(all_left))
        setup_divisors = sorted(out.divisors)
        out.work.update(distinct_left=len(left), distinct_right=len(set(signed.values())))
        prepared = process_time_ns()
        if name == "global":
            by_trace = defaultdict(list)
            for d in gaps:
                by_trace[(signed[d]+signed[-d]) % n].append(signed[d])
            for x in left:
                trace = (x + pow(x, -1, n)) % n
                out.work["left_trace_inversions"] += 1
                for y in by_trace.get(trace, ()):
                    out.check(x-y, "global")
        else:
            local_search(name, n, left, signed, v, out)
    stop = process_time_ns()
    return (dict(divisors=sorted(out.divisors), setup_divisors=setup_divisors, work=dict(out.work)),
            dict(schedule=scheduled-start, setup=prepared-scheduled, comparison=stop-prepared,
                 first=out.first, complete=stop-start), common)


def diagnostics(n, bits, limit, per_row, expected):
    gaps, coordinates, _ = schedule(n, bits, limit, per_row)
    previous_square = row_squares(n, coordinates)[0]
    previous_global = trace_search(n, 2, gaps, coordinates, True)[0]
    if sorted(map(int, previous_square["divisors"])) != expected["square"]["divisors"]:
        raise ArithmeticError("row-square baseline changed")
    if sorted(map(int, previous_global["divisors"])) != expected["global"]["divisors"]:
        raise ArithmeticError("whole-trace baseline changed")
    out = Readouts(n, process_time_ns())
    _, left, signed = keys(n, gaps, coordinates, out)
    found = set(out.divisors)
    count = Counter()
    first = {}
    for (k, y, c, s, own_gap), x in zip(coordinates, left):
        for e, yr in signed.items():
            g = gcd(x-yr, n)
            if 1 < g < n:
                found.add(g)
                kind = "own_gap" if abs(e) == own_gap else "different_gap"
                count[kind] += 1
                if kind not in first:
                    a, b = (c-own_gap)//2, (c+own_gap)//2
                    first[kind] = dict(k=k, y=str(y), weights=[a,b], s=str(s), gap=e,
                                       x_power=str(x), y_power=str(yr), gcd=str(g))
    if any(sorted(found) != expected[method]["divisors"] for method in LOCAL):
        raise ArithmeticError("local batches did not preserve all individual proper divisors")
    return dict(raw_hit_counts=dict(count), first_witness=first)


def inputs(bits, seed, count):
    index = 0
    rows = []
    while len(rows) < count:
        p, q = [draw_prime(side, index, bits=bits, seed=seed) for side in (b"p", b"q")]
        if p != q:
            rows.append((index, p*q))
        index += 1
    return rows


def case(n, bits, limit, per_row, repeats, offset):
    work, times = {}, defaultdict(list)
    for j in range(repeats):
        order = (offset+j) % len(METHODS)
        for method in METHODS[order:] + METHODS[:order]:
            result, duration, common = run_method(method, n, bits, limit, per_row)
            if work.setdefault(method, result) != result:
                raise ArithmeticError("method work changed between timing repetitions")
            times[method].append(duration)
    seen = diagnostics(n, bits, limit, per_row, work)
    divisors = {g for result in work.values() for g in result["divisors"]}
    pairs = {tuple(sorted((g, n//g))) for g in divisors if 1 < g < n and n % g == 0}
    if bool(divisors) != bool(pairs) or len(pairs) > 1:
        raise ArithmeticError("a result was not a proper split of the panel semiprime")
    pair = [str(p) for p in next(iter(pairs))] if pairs else []
    return dict(n=str(n), factor_bits=bits, limit=limit, per_row=per_row, common=common,
                pair=pair, remaining=[] if pair else [str(n)], methods=work, diagnosis=seen,
                cpu_ns_medians={m: {k: int(median(t[k] for t in times[m])) if times[m][0][k]
                                    is not None else None for k in times[m][0]} for m in METHODS})


def run_fixture(case):
    """Run the column strategy; fixture expectations are read only by the checker."""
    result, _, setup = run_method("derivative", int(case["n"]), case["factor_bits"],
                                  case["multiplier_limit"], case["per_row"])
    counts = result["work"]
    return dict(multiplier_limit=case["multiplier_limit"], per_row=case["per_row"],
                skipped_coordinates=setup["omitted_coordinates_below_limit"],
                coordinates=setup["coordinate_visits"], right_powers=counts["distinct_right"],
                column_gcds=sum(counts.get("column_"+kind, 0) for kind in ("one","whole","proper")),
                derivative_queries=counts.get("derivative_queries", 0),
                divisors=[str(g) for g in result["divisors"]])


def check_fixture(case, result):
    n = int(case["n"])
    divisors = list(map(int, result["divisors"]))
    if any(not 1 < g < n or n % g for g in divisors):
        raise ArithmeticError("invalid factor")
    pair = [str(p) for p in sorted((divisors[0], n//divisors[0]))] if divisors else []
    if (result != case["checks"] or pair != case["factors"] or
            case["remaining"] != ([] if pair else [str(n)]) or
            case["status"] != ("complete" if pair else "partial")):
        raise ArithmeticError("unexpected local-gap benchmark outcome")


def verify_cases(rows):
    pairs = {int(row["n"]): tuple(map(int, row["pair"])) for row in rows if row["pair"]}
    if not pairs:
        raise ArithmeticError("no certificate to check")
    imports, bodies, claims, proofs = set(), [], [], []
    for index, (n, pair) in enumerate(sorted(pairs.items())):
        code = render_certificate(n, list(pair))
        imports.update(line for line in code.splitlines() if line.startswith("import "))
        body = code.split("namespace PrimeFactors.Generated\n", 1)[1].split("#print axioms", 1)[0]
        bodies.append(f"namespace Case{index}\n{body.strip()}\nend Case{index}")
        claims.append(f"ExactFactorization {n} {list(pair)}")
        proofs.append(f"Case{index}.factorization")
    namespace = "PrimeFactors.LocalGapCertificates"
    source = ["\n".join(sorted(imports)), "set_option maxRecDepth 8192",
              f"namespace {namespace}", *bodies,
              "theorem panel : " + " ∧\n  ".join(claims) + " :=\n  ⟨" + ", ".join(proofs) + "⟩",
              "#print axioms panel", f"end {namespace}"]
    text = "\n\n".join(source) + "\n"
    path = ROOT / "build/local-gap-polynomial/Factors.lean"
    path.parent.mkdir(exist_ok=True, parents=True)
    path.write_text(text)
    verify_file(path, namespace + ".panel")
    return dict(theorem=namespace+".panel", pairs=len(pairs), sha256=sha256(text.encode()).hexdigest())


def panel(repeats, verify):
    if repeats < 1:
        raise ValueError("a positive repeat count is required")
    holdout, scaling, controls = [], [], []
    for bits in (11, 15):
        seed = f"local-gap-polynomial-v1/{bits}".encode()
        for idx, n in inputs(bits, seed, 12):
            holdout.append(dict(draw_index=idx, **case(n, bits, 256, 4, repeats, idx)))
    scale_seed = b"local-gap-polynomial-scale-v1/20"
    idx, n = inputs(20, scale_seed, 1)[0]
    for limit in (256, 1024, 4096):
        scaling.append(dict(draw_index=idx, **case(n, 20, limit, 2, repeats, idx)))
    for item in json.loads(FIXTURE.read_text()):
        if item["factor_bits"] == 1024:
            controls.append(dict(id=item["id"], **case(int(item["n"]), 1024, 64, 2, repeats, 0)))
    return dict(seed="local-gap-polynomial-v1/<width>", scaling_seed=scale_seed.decode(),
                base=2, cpu_repeats=repeats, python=platform.python_version(),
                machine=platform.machine(), holdout=holdout, scaling=scaling, controls=controls,
                certificate=verify_cases(holdout+scaling+controls) if verify else None)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--verify", action="store_true")
    cli.add_argument("--repeats", type=int, default=5)
    cli.add_argument("--write", action="store_true")
    args = cli.parse_args()
    result = json.dumps(panel(args.repeats, args.verify), indent=2) + "\n"
    if args.write:
        REPORT.write_text(result)
    else:
        print(result, end="")
