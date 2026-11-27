"""Compare broad and unit-reduced signed conics on the same public prime products."""

import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.signed_norm_arcs import (
    MULTIPLIERS, SEED, domain_size, exact_points, full_size, holdouts, point_scan, possible, search,
)
from experiments.split_prime_holdout import certificate
from scripts.factor import primes_through


DOMAINS = ("broad", "unit")
METHODS = ("direct", "arcs", "integer_arcs")
TARGETS = (-6, -3, -2, -1, 2, 3, 6)


def root_classes(n, points):
    classes = set()
    for d, _, x, y in points:
        if gcd(y, n) == 1:
            r = x*pow(y, -1, n) % n
            classes.add((d, min(r, -r % n)))
    return classes


def verify_small():
    equations = solutions = 0
    for n in range(2, 129):
        for d in TARGETS:
            for m in MULTIPLIERS:
                for domain in DOMAINS:
                    expected = exact_points(n, d, m, domain)
                    for method in METHODS:
                        found = list(point_scan(n, d, m, method, Counter(), domain=domain))
                        if len(found) != len(expected) or set(found) != expected:
                            raise ArithmeticError(f"points differ for {n}, {d}, {m}, {domain}, {method}")
                    equations += 1
                    solutions += len(expected)
    pairs = classes = 0
    for p, q in combinations((p for p in primes_through(79) if p > 3), 2):
        n = p*q
        targets = search(n, "integer_arcs", domain="unit")["targets"]
        exact = {(d, min(r, n-r)) for d in targets for r in range(n) if (r*r-d) % n == 0}
        for domain in DOMAINS:
            result = search(n, "integer_arcs", domain=domain)
            if root_classes(n, result["points"]) != exact or int(result["factor"]) not in (p, q):
                raise ArithmeticError(f"root classes differ for {n}, {domain}")
        pairs += 1
        classes += len(exact)
    return dict(domain_equations=equations, nonnegative_solutions=solutions, semiprimes=pairs,
                target_root_classes_up_to_sign=classes)


def measure(repetitions):
    rows = []
    options = [(domain, method) for domain in DOMAINS for method in METHODS]
    for bits, sample, n in holdouts():
        raw, elapsed, first = {}, {}, {}
        for rep in range(repetitions):
            i = sample % len(options)
            order = options[i:]+options[:i]
            for domain, method in (order if rep % 2 == 0 else reversed(order)):
                possible.cache_clear()
                start = process_time_ns()
                result = search(n, method, domain=domain)
                key = (domain, method)
                elapsed.setdefault(key, []).append(process_time_ns()-start)
                first.setdefault(key, []).append(result.pop("first_cpu_ns"))
                if not result["complete"] or result["factor"] is None:
                    raise ArithmeticError("completed scan missed a split")
                if key in raw and raw[key] != result:
                    raise ArithmeticError("replays disagree")
                raw[key] = result
        reference = raw["broad", "direct"]
        p = int(reference["factor"])
        pair = sorted((p, n//p))
        classes = root_classes(n, reference["points"])
        measurements = {}
        for domain in DOMAINS:
            ref_points = raw[domain, "direct"]["points"]
            if root_classes(n, ref_points) != classes:
                raise ArithmeticError("the unit-reduced domains discarded a root class")
            counts = {}
            positions, blocks = domain_size(n, domain)
            for method in METHODS:
                key = domain, method
                v = raw[key]
                if v["points"] != ref_points or int(v["factor"]) not in pair:
                    raise ArithmeticError("incomplete point set or incorrect factor")
                if v["work"]["coordinate_positions"] != positions or method != "direct" and v["work"]["blocks"] != blocks:
                    raise ArithmeticError("complete counts disagree with domain size")
                if method == "integer_arcs" and v["work"] != raw[domain, "arcs"]["work"]:
                    raise ArithmeticError("changing the slope arithmetic changed an intercept or operation count")
                counts[method] = dict(complete_cpu_ns=int(median(elapsed[key])),
                                      first_cpu_ns=int(median(first[key])), first_work=v["first_work"],
                                      work=v["work"], witnesses=v["witnesses"])
            measurements[domain] = dict(representations=len(ref_points), methods=counts)
        rows.append(dict(bits=bits, sample=sample, n=str(n), pair=[str(x) for x in pair],
                         roots_up_to_sign=sorted(classes), modes=measurements,
                         certificate_sha256=certificate(n, pair)))
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repetitions", type=int, default=2)
    parser.add_argument("--check-small", action="store_true")
    args = parser.parse_args()
    if args.repetitions <= 0:
        parser.error("repetitions must be positive")
    checks = verify_small()
    report = checks if args.check_small else dict(
        seed=SEED.decode(), python=platform.python_version(), machine=platform.machine(),
        repetitions=args.repetitions, validation=checks,
        timing="Every method builds its own tables. Forward/reverse order per input, CPU time to first factor and to complete. Signed root classes compared across domains; point sets and both arc line counts compared within each domain.",
        rows=measure(args.repetitions),
        capped_2048={domain: full_size(domain, "integer_arcs") for domain in DOMAINS})
    data = json.dumps(report, indent=2)+"\n"
    if args.output:
        args.output.write_text(data)
    else:
        print(data, end="")
