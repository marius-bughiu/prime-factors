"""Compare a small-positive-norm pilot with ascending target-compatible CF walks."""

import argparse
from collections import Counter
from itertools import permutations
import json
from math import gcd, isqrt, prod
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.mixed_ratio_heights import jacobi
from experiments.pell_pairs import convergents
from experiments.split_prime_holdout import certificate
from experiments.target_norm_multipliers import primitive_mod16
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
DOMAIN = b"target-positive-norm-order-v1"
METHODS = ("ascending", "pilot_ascending", "pilot_norm")
ORDERS = tuple(permutations(METHODS))
LIMIT, PER_WALK, TOTAL, SAMPLES = 320, 256, 2048, 32
SQUARES = tuple(frozenset(x*x % m for x in range(m)) for m in (64, 63, 65))


def square_residue(x):
    return x & 63 in SQUARES[0] and x % 63 in SQUARES[1] and x % 65 in SQUARES[2]


def menu(n, d):
    retained = []
    primes = primes_through(LIMIT)
    at_two = primitive_mod16(d)
    for k in range(1, LIMIT + 1):
        shared = gcd(k, n)
        if 1 < shared < n:
            return [], shared
        factors = [p for p in primes if k % p == 0]
        if prod(factors) == k and gcd(k, n*d) == 1 and k*n % 16 in at_two:
            if all(jacobi(d, p) == 1 for p in factors if p > 2) and (d == 2 or jacobi(k*n, d) == 1):
                retained.append(k)
    return retained, None


def cutoff_convergents(n, k, steps, ceiling):
    """The usual CF recurrence with y initially tracked; 0 marks an omitted positive row."""
    radicand = n*k
    base = isqrt(radicand)
    if base*base == radicand:
        raise ValueError("square radicand")
    offset, denominator, quotient = 0, 1, base
    older_x, previous_x = 0, 1
    older_y, previous_y = 1, 0
    tracking = True
    for step in range(1, steps + 1):
        x = (quotient*previous_x + older_x) % n
        older_x, previous_x = previous_x, x
        if tracking:
            older_y, previous_y = previous_y, quotient*previous_y+older_y
            tracking = previous_y <= ceiling
        offset = quotient*denominator-offset
        denominator = (radicand-offset*offset)//denominator
        quotient = (base+offset)//denominator
        sign = -1 if step % 2 else int(not tracking)
        yield step, denominator, sign, x, quotient*denominator == 2*offset


def run(n, d, method, *, audit=None, cutoff=None, square_sieve=False):
    """Run all methods to an equal transition cap; remember their first target split."""
    multipliers, early = menu(n, d)
    if early:
        raise ValueError("the supplied examples have prime factors above the multiplier cap")
    budget = dict(visits=0, positive_tests=0, square_roots=0, started_walks=0, pilot_visits=0)
    streams = {}
    first = split = None
    preview = {}
    retired = set()

    def advance(k, count, pilot=False):
        nonlocal first, split
        if k not in streams:
            streams[k] = (convergents(n, k, PER_WALK) if cutoff is None
                          else cutoff_convergents(n, k, PER_WALK, cutoff))
            budget["started_walks"] += 1
        for _ in range(count):
            if k in retired or budget["visits"] == TOTAL:
                break
            row = next(streams[k], None)
            if row is None:
                retired.add(k)
                break
            step, norm, sign, x, center = row
            if audit is not None:
                audit.setdefault(k, []).append((step, norm, sign, x))
            budget["visits"] += 1
            budget["pilot_visits"] += int(pilot)
            if sign >= 0:
                budget["positive_tests"] += 1
                if step == 2:
                    preview[k] = norm
                if sign == 1 and norm % d == 0 and (not square_sieve or square_residue(norm // d)):
                    budget["square_roots"] += 1
                    t = isqrt(norm // d)
                    if d*t*t == norm:
                        g = gcd(t, n)
                        if g == 1:
                            root = x * pow(t, -1, n) % n
                            if (root*root - d) % n:
                                raise ArithmeticError("target root verification failed")
                            witness = dict(k=k, step=step, visits=budget["visits"], root=str(root))
                            if first is None:
                                first = witness
                            else:
                                g = gcd(root - int(first["root"]), n)
                        if 1 < g < n and split is None:
                            split = dict(k=k, step=step, visits=budget["visits"], factor=str(g))
            if center or norm == 1 or step == PER_WALK:
                retired.add(k)

    if method in ("pilot_ascending", "pilot_norm"):
        for k in multipliers:
            advance(k, 2, True)
        multipliers = [k for k in multipliers if k not in retired]
        if method == "pilot_norm":
            multipliers.sort(key=lambda k: (preview[k], k))
    elif method != "ascending":
        raise ValueError(method)
    for k in multipliers:
        if budget["visits"] == TOTAL:
            break
        advance(k, PER_WALK)
    return dict(**budget, first_root=first, split=split)


def inputs():
    for bits in (20, 24):
        seed = DOMAIN + b"/" + str(bits).encode()
        retained = sample = 0
        while retained < SAMPLES:
            primes = sorted(draw_prime(side, sample, bits=bits, seed=seed) for side in (b"p", b"q"))
            if primes[0] != primes[1]:
                yield bits, sample, prod(primes), primes
                retained += 1
            sample += 1


def compare():
    rows, all_times = [], []
    excluded = Counter()
    for bits, sample, n, hidden in inputs():
        for d in (2, 3):
            if jacobi(d, n) != 1:
                excluded[bits, d] += 1
                continue
            methods = {}
            durations = {m: [] for m in METHODS}
            for rep in range(len(ORDERS)):
                for m in ORDERS[(rep + sample) % len(ORDERS)]:
                    primes_through.cache_clear()
                    start = process_time_ns()
                    result = run(n, d, m)
                    durations[m].append(process_time_ns() - start)
                    if m in methods and result != methods[m]:
                        raise ArithmeticError("nondeterministic search")
                    methods[m] = result
            if len({v["visits"] for v in methods.values()}) != 1:
                raise ArithmeticError("unequal transition budget")
            for m, result in methods.items():
                if result["split"] and int(result["split"]["factor"]) not in hidden:
                    raise ArithmeticError("incorrect split")
                result["median_cpu_ns"] = int(median(durations[m]))
            rows.append(dict(bits=bits, sample=sample, n=str(n), target=d, methods=methods))
            all_times.append(durations)
    summaries = []
    for bits in (20, 24):
        for d in (2, 3):
            subset = [(r, t) for r, t in zip(rows, all_times) if (r["bits"], r["target"]) == (bits, d)]
            totals = {}
            for method in METHODS:
                outcomes = [r["methods"][method] for r, _ in subset]
                sums = [sum(t[method][rep] for _, t in subset) for rep in range(len(ORDERS))]
                totals[method] = dict(roots=sum(bool(o["first_root"]) for o in outcomes),
                                      splits=sum(bool(o["split"]) for o in outcomes),
                                      visits=sum(o["visits"] for o in outcomes), median_batch_cpu_ns=int(median(sums)))
            comparable = {}
            for base in METHODS[:-1]:
                comparable[base] = {
                    outcome: dict(gains=sum(bool(r["methods"]["pilot_norm"][outcome]) and not r["methods"][base][outcome]
                                            for r, _ in subset),
                                  losses=sum(bool(r["methods"][base][outcome]) and not r["methods"]["pilot_norm"][outcome]
                                             for r, _ in subset)) for outcome in ("first_root", "split")
                }
            summaries.append(dict(bits=bits, target=d, included=len(subset), excluded_jacobi=excluded[bits, d],
                                  methods=totals, paired=comparable))
    return dict(domain=DOMAIN.decode(), samples_per_width=SAMPLES, per_target_cf_budget=TOTAL,
                steps_per_walk=PER_WALK, multiplier_limit=LIMIT, methods=METHODS,
                implementation="Search sees only N,D. Positive norm D*t^2 is tested immediately on every visit including pilot rows. Sorting, setup and all transitions are timed. After first success, continue to the common cap for fixed-work comparison. Gcd diagnostics on nontarget rows are outside scope.",
                timings="Median process CPU in six orders; cold menu prime cache; input generation and retrospective checking excluded.",
                machine=platform.machine(), python=platform.python_version(), summaries=summaries, rows=rows)


def verify(report):
    """Recheck all roots and obtain a normal Lean certificate for each distinct split."""
    proved = {}
    for row in report["rows"]:
        n, d = int(row["n"]), row["target"]
        for method in METHODS:
            outcome = row["methods"][method]
            witness = outcome["first_root"]
            if witness and (int(witness["root"])**2 - d) % n:
                raise ArithmeticError("recorded root failed verification")
            if outcome["split"]:
                factor = int(outcome["split"]["factor"])
                if not 1 < factor < n or n % factor:
                    raise ArithmeticError("recorded factor failed verification")
                pair = sorted((factor, n // factor))
                if n not in proved:
                    proved[n] = (pair, certificate(n, pair))
                elif proved[n][0] != pair:
                    raise ArithmeticError("conflicting factorizations")
    return {str(n): {"pair": [str(x) for x in pair], "sha256": digest} for n, (pair, digest) in proved.items()}


def full_size():
    """Replay just the bounded walks, reconstructing their rational denominators independently."""
    fixtures = json.loads((ROOT / "benchmarks/projected-divisor-wheel.json").read_text())
    results = []
    for fixture in fixtures:
        n = int(fixture["n"])
        if n.bit_length() != 2048:
            continue
        for d in (2, 3):
            if jacobi(d, n) != 1:
                continue
            for method in METHODS:
                audit = {}
                outcome = run(n, d, method, audit=audit)
                heights = []
                within = {b: 0 for b in (64, 256, 384, 464)}
                skipped_isqrts = dict.fromkeys(within, 0)
                sieve_count = sieve_outside = 0
                for k, rows in audit.items():
                    radicand = k*n
                    base = isqrt(radicand)
                    old_x, x, old_y, y, last_norm = 1, base, 0, 1, 1
                    for _, norm, sign, numerator in rows:
                        if x*x-radicand*y*y != sign*norm or x % n != numerator:
                            raise ArithmeticError("independent convergent reconstruction failed")
                        if sign > 0:
                            if norm*norm >= 4*radicand:
                                raise ArithmeticError("positive complete denominator exceeded its proven bound")
                            heights.append(y.bit_length())
                            if norm % d == 0 and square_residue(norm // d):
                                sieve_count += 1
                                sieve_outside += int(y > 1 << 464)
                            for b in within:
                                within[b] += int(y <= 1 << b)
                                skipped_isqrts[b] += int(y <= 1 << b and norm % d == 0)
                        offset = isqrt(radicand - norm*last_norm)
                        quotient = (base + offset) // norm
                        old_x, x = x, quotient*x+old_x
                        old_y, y = y, quotient*y+old_y
                        last_norm = norm
                timings = {"ordinary": [], "cutoff": [], "square_sieve": [], "sieve_and_cutoff": []}
                options = [("ordinary", None, False), ("cutoff", 1 << 464, False),
                           ("square_sieve", None, True), ("sieve_and_cutoff", 1 << 464, True)]
                for rep in range(8):
                    i = rep % len(options)
                    for name, ceiling, sieve in options[i:] + options[:i]:
                        primes_through.cache_clear()
                        start = process_time_ns()
                        trial = run(n, d, method, cutoff=ceiling, square_sieve=sieve)
                        timings[name].append(process_time_ns() - start)
                        expected = dict(outcome)
                        if sieve:
                            expected["square_roots"] = sieve_count if ceiling is None else sieve_outside
                        elif ceiling is not None:
                            expected["square_roots"] -= skipped_isqrts[464]
                        if trial != expected:
                            raise ArithmeticError("budget or outcome differs from the independent numerical replay")
                results.append(dict(id=fixture["id"], target=d, method=method, outcome=outcome,
                                    largest_positive_denominator_bits=max(heights), within_power_of_two=within,
                                    square_tests_omitted_at_power_of_two=skipped_isqrts,
                                    sieve_square_tests=sieve_count, sieve_and_cutoff_square_tests=sieve_outside,
                                    median_cpu_ns={k: int(median(v)) for k, v in timings.items()}))
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-report", type=Path, help="check recorded roots and certify each split with Lean")
    parser.add_argument("--full-size", action="store_true", help="audit walks on the two public 2048-bit inputs")
    args = parser.parse_args()
    if args.verify_report:
        result = verify(json.loads(args.verify_report.read_text()))
    else:
        result = full_size() if args.full_size else compare()
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(data)
    else:
        print(data, end="")
