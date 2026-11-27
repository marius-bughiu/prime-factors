"""Paired bounded tests of discriminant schedules in a quadratic norm-one power search."""

from argparse import ArgumentParser
from collections import Counter
from hashlib import shake_256
import json
from math import gcd
from pathlib import Path
from random import Random
from time import perf_counter, process_time

from experiments.line_powers import trace_power
from experiments.mixed_ratio_heights import jacobi
from experiments.twelve_residue_panel import eligible_pairs
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
MODES = ("menu", "primes", "anchored_primes", "ordinary_projected", "ordinary")
ANCHOR_BOUND = 97
PRIMES = tuple(primes_through(ANCHOR_BOUND))
BUDGET = 8
SMOOTH = 13
SAMPLE = 512
POPULATION_SEED = 8641308
WORK_COLUMNS = ("divisor", "winner", "checkpoint", "trials", "jacobi_tests", "setup_gcds", "inversions",
                "powers", "exponent_bits", "ladder_products", "readout_gcds", "saturations", "skipped_seeds")


def prime_powers(bound):
    result = []
    for prime in primes_through(bound):
        power = prime
        while power <= bound // prime:
            power *= prime
        result.append(power)
    return result


def slope(n, d, repetition=0):
    data = f"prime-factors/signed-discriminant-menu/v1/{n}/{d}/{repetition}".encode("ascii")
    raw = shake_256(data).digest((n.bit_length() + 7)//8 + 16)
    return 2 + int.from_bytes(raw, "big") % (n - 3)


def schedule(mode, anchor, budget):
    if mode == "primes":
        return list(PRIMES[:budget])
    if mode.startswith("ordinary"):
        return [1] * budget
    values = [1, anchor]
    for prime in PRIMES:
        if len(values) >= budget:
            break
        if prime != anchor:
            values.append(prime)
            if mode == "menu":
                values.append(anchor * prime)
    return values[:budget]


def search(n, mode, budget=BUDGET, smooth=SMOOTH):
    if n < 5 or n % 2 == 0 or mode not in MODES or not 1 <= budget <= len(PRIMES) or smooth < 1:
        raise ValueError("want an odd product >=5, a supported mode and a positive bounded budget")
    work = dict(outcome="exhausted", anchor=None, jacobi_tests=0, trials=0, setup_gcds=0,
                inversions=0, powers=0, exponent_bits=0, ladder_products=0, readout_gcds=0,
                saturations=0, skipped_seeds=0, discriminants=[], winner=None, checkpoint=None)
    symbols = {1: 1}

    def symbol(d):
        if d not in symbols:
            symbols[d] = jacobi(d, n)
            work["jacobi_tests"] += 1
        return symbols[d]

    def finish(factor, source, d, stage):
        work.update(outcome=source, winner=d, checkpoint=stage)
        return factor, work

    anchor = None
    if mode in ("menu", "anchored_primes") and budget > 1:
        for d in PRIMES:
            sign = symbol(d)
            if not sign:
                divisor = gcd(n, d)
                work["setup_gcds"] += 1
                if divisor != n:
                    return finish(divisor, "anchor gcd", d, None)
            if sign == -1:
                anchor = d
                break
        if anchor is None:
            work["outcome"] = "anchor bound"
            return None, work
    work["anchor"] = anchor
    degrees = prime_powers(smooth)
    ordinary = mode.startswith("ordinary")
    for rep, d in enumerate(schedule(mode, anchor, budget)):
        work["trials"] += 1
        work["discriminants"].append(d)
        sign = symbol(d)
        if not sign:
            divisor = gcd(n, d)
            work["setup_gcds"] += 1
            if divisor < n:
                return finish(divisor, "discriminant gcd", d, None)
            continue
        t = slope(n, d, rep if ordinary else 0)
        square = t*t % n
        norm = (square - d) % n
        divisor = gcd(norm, n)
        work["setup_gcds"] += 1
        if divisor > 1:
            if divisor < n:
                return finish(divisor, "seed norm", d, None)
            work["skipped_seeds"] += 1
            continue
        inverse = pow(norm, -1, n)
        work["inversions"] += 1
        if ordinary:
            # One split-algebra coordinate of the D=1 Cayley element.
            value = ((t+1)**2 * inverse) % n
            identity = 1
        else:
            value = 2 * (square+d) * inverse % n
            identity = 2
        # Degree 0 in the report denotes the initial N-j projection.
        stages = [(e, e) for e in degrees]
        if mode != "ordinary":
            stages.insert(0, (0, n-sign))
        for checkpoint, exponent in stages:
            work["powers"] += 1
            work["exponent_bits"] += exponent.bit_length()
            if ordinary:
                value = pow(value, exponent, n)
            else:
                value = trace_power(value, exponent, n)
                work["ladder_products"] += 2*exponent.bit_length()-1
            divisor = gcd(value-identity, n)
            work["readout_gcds"] += 1
            if 1 < divisor < n:
                return finish(divisor, "power gcd", d, checkpoint)
            if divisor == n:
                work["saturations"] += 1
                break
    return None, work


def compare(n, offset=0, budget=BUDGET, smooth=SMOOTH):
    results = {}
    for i in range(len(MODES)):
        mode = MODES[(i+offset) % len(MODES)]
        wall, cpu = perf_counter(), process_time()
        d, work = search(n, mode, budget, smooth)
        cpu, wall = process_time()-cpu, perf_counter()-wall
        if d is not None and (not 1 < d < n or n % d):
            raise ArithmeticError("invalid reported divisor")
        results[mode] = dict(work, divisor=str(d) if d else None, cpu_s=round(cpu, 6), wall_s=round(wall, 6))
    return results


def signs(d, p, q):
    return (jacobi(d, p), jacobi(d, q))


def panel(bits):
    rng = Random(POPULATION_SEED + bits)
    totals = {mode: Counter() for mode in MODES}
    paired = {mode: Counter() for mode in MODES[1:]}
    coverage = {mode: Counter() for mode in MODES[:3]}
    examples = {}
    records = []
    for i, (p, q) in enumerate(eligible_pairs(bits, SAMPLE, rng)):
        n = p*q
        results = compare(n, i)
        # Keep a standard CSV row per product inside the JSON for compactness.
        # Every field is a nonnegative integer or empty (for a missing hit).
        fields = [results[mode][column] for mode in MODES for column in WORK_COLUMNS]
        records.append(",".join([str(n)] + [str(v) if v is not None else "" for v in fields]))
        for mode, row in results.items():
            if row["divisor"] and int(row["divisor"]) not in (p,q):
                raise ArithmeticError("failed independent prime-factor check")
            counts = totals[mode]
            counts["splits"] += bool(row["divisor"])
            if row["divisor"]:
                counts["split_by_" + row["outcome"].replace(" ", "_")] += 1
            for key in ("trials", "jacobi_tests", "setup_gcds", "inversions", "powers", "exponent_bits",
                        "ladder_products", "readout_gcds", "saturations", "cpu_s", "wall_s"):
                counts[key] += row[key]
        menu = results["menu"]
        for mode in MODES[:3]:
            row = results[mode]
            plan = schedule(mode, row["anchor"], BUDGET) if row["outcome"] != "anchor bound" else []
            coverage[mode][len({signs(d, p, q) for d in plan})] += 1
        for other in MODES[1:]:
            old = results[other]
            key = ("both" if old["divisor"] else "gained") if menu["divisor"] else (
                "lost" if old["divisor"] else "neither")
            paired[other][key] += 1
            if other == "primes" and key in ("gained", "lost"):
                win, lose = (menu, old) if key == "gained" else (old, menu)
                sign = signs(win["winner"], p, q)
                missing = sign not in {signs(d, p, q) for d in lose["discriminants"]}
                if missing:
                    paired[other][key + "_with_unseen_sign"] += 1
                    if win["outcome"] == "power gcd":
                        paired[other][key + "_by_power_with_unseen_sign"] += 1
                name = key + ("_unseen_sign" if missing else "_seen_sign")
                if name not in examples and win["outcome"] == "power gcd":
                    examples[name] = dict(n=str(n), factors=[str(p), str(q)], winning_sign=list(sign),
                                          sign_gcd=gcd(p-sign[0],q-sign[1]), modes=results)
    for group in totals.values():
        for key in ("cpu_s", "wall_s"):
            group[key] = round(group[key], 6)
    return dict(bits=bits, products=SAMPLE, seed=POPULATION_SEED+bits, totals=totals,
                menu_vs=paired, retrospective_sign_coverage=coverage, examples=examples,
                per_product_csv=records)


def check_ledger():
    """Use the same factor-certificate generator as the opposite-key comparison panel."""
    from experiments.opposite_key_comparison import check_prime_pairs
    data = json.loads((ROOT / "research/signed-discriminant-menu.json").read_text())
    indices = [i for i, name in enumerate(data["per_product_csv_columns"]) if name.endswith("_divisor")]
    products = set()
    for group in data["panels"]:
        for line in group["per_product_csv"]:
            fields = line.split(",")
            n = int(fields[0])
            for i in indices:
                if fields[i]:
                    d = int(fields[i])
                    a, b = sorted((d,n//d))
                    products.add((n,a,b))
    check_prime_pairs(sorted(products))
    print(f"Lean checked all {len(products)} distinct reported small factorizations.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--case", type=int, help="replay all five methods for one public product")
    action.add_argument("--check-ledger", action="store_true", help="certify all factors in the saved panel")
    args = parser.parse_args()
    if args.check_ledger:
        check_ledger()
        raise SystemExit(0)
    if args.case is not None:
        print(json.dumps(compare(args.case), indent=2))
        raise SystemExit(0)
    controls = {}
    for index, name in enumerate(("certified-control", "mixed-negative-control")):
        n = int(json.loads((ROOT / f"research/{name}.json").read_text())["product"])
        controls[name] = dict(n=str(n), modes=compare(n, index))
    print(json.dumps(dict(generator="python3 -m experiments.signed_discriminant_menu",
                          trial_cap=BUDGET, smooth_bound=SMOOTH, anchor_bound=ANCHOR_BOUND,
                          per_product_csv_columns=["n"] + [mode+"_"+key for mode in MODES for key in WORK_COLUMNS],
                          full_size=controls, panels=[panel(bits) for bits in (12,16,20)]), indent=2))
