"""Compare public prefix LCMs by continued fractions, shared powers and a fixed Fermat search."""
import argparse
import json
from math import gcd, lcm, prod
from pathlib import Path

from experiments.affine_radix_holdout import draw_prime
from experiments.power_denominator_census import probe
from scripts.factor import fermat_split, render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/scaled-power-menu.json"
CONTROL_FILE = ROOT / "benchmarks/target-norm-multipliers.json"
SEED = b"scaled-power-menu/v1"
WIDTHS = (12, 20, 28, 36)
ROWS_PER_WIDTH = 16
FERMAT_LIMIT = 1024


def prefixes(n):
    """Yield the first index and exponent of every distinct nontrivial LCM up to N."""
    exponent = 1
    index = 2
    while exponent <= n:
        previous = exponent
        exponent = lcm(index, exponent)
        if exponent > n:
            return
        if exponent != previous:
            yield index, exponent, exponent // previous
        index += 1


def split_pair(n, divisor):
    return [str(x) for x in sorted((divisor, n // divisor))] if divisor else []


def search(n, factor_bits, *, compare_full=False):
    """All three searches use only the product and the advertised common prime width."""
    if n < 3 or n % 2 == 0 or factor_bits < 2:
        raise ValueError("expected an odd product and a common prime width of at least two")
    menu = dict(power_updates=0, eligible=0, first_index=None, last_index=None)
    cf = dict(remainder_passes=0, convergents=0, early_stops=0, integer_totients=0,
              width_survivors=0, square_tests=0, split_exponents=0, pair=[], first=None)
    full = dict(convergents=0, integer_totients=0)
    modular = dict(gcd_one=0, gcd_product=0, proper_gcd=0, pair=[], first_index=None)
    power = 2 % n
    for index, exponent, multiplier in prefixes(n):
        menu["power_updates"] += 1
        power = pow(power, multiplier, n)
        if (exponent + 1)**2 < 4*n:
            continue
        menu["eligible"] += 1
        if menu["first_index"] is None:
            menu["first_index"] = index
        menu["last_index"] = index
        work = probe(n, exponent, factor_bits=factor_bits, early_stop=True)
        if compare_full:
            unlimited = probe(n, exponent, factor_bits=factor_bits)
            for key in ("passed", "width_survivors", "square_tests", "pair", "witness"):
                if work[key] != unlimited[key]:
                    raise ArithmeticError(f"stopped and full searches disagree on {key} at {index}")
            for key in full:
                full[key] += unlimited[key]
        cf["remainder_passes"] += work["passed"]
        cf["early_stops"] += work["stopped_early"]
        for key in ("convergents", "integer_totients", "width_survivors", "square_tests"):
            cf[key] += work[key]
        if work["pair"]:
            cf["split_exponents"] += 1
            if not cf["pair"]:
                cf["pair"] = work["pair"]
                cf["first"] = dict(prefix_index=index, exponent=str(exponent), **work["witness"])
        divisor = gcd(power-1, n)
        if divisor == 1:
            modular["gcd_one"] += 1
        elif divisor == n:
            modular["gcd_product"] += 1
        else:
            modular["proper_gcd"] += 1
            if not modular["pair"]:
                modular["pair"] = split_pair(n, divisor)
                modular["first_index"] = index
    divisor, spent = fermat_split(n, FERMAT_LIMIT)
    record = dict(menu=menu, cf=cf, modular=modular, fermat=dict(steps=spent, pair=split_pair(n, divisor)))
    if compare_full:
        record["full_cf"] = full
    return record


def run_fixture(case):
    """The native fixture exposes the CF split. The other two searches are comparisons."""
    work = search(int(case["n"]), case["factor_bits"])
    return {**work, "pair": work["cf"]["pair"]}


def methods(work):
    return {name for name in ("cf", "modular", "fermat") if work[name]["pair"]}


def measure():
    small = []
    for width in WIDTHS:
        rows = []
        seen = set()
        sample = 0
        while len(rows) < ROWS_PER_WIDTH:
            p, q = sorted(draw_prime(side, sample, bits=width, seed=SEED) for side in (b'p', b'q'))
            sample += 1
            n = p*q
            if p == q or n in seen:
                continue
            seen.add(n)
            work = search(n, width, compare_full=True)
            for method in methods(work):
                if work[method]["pair"] != [str(p), str(q)]:
                    raise ArithmeticError("recovered factors disagree with input generation")
            rows.append(dict(sample=sample-1, n=str(n), **work))
        totals = {name: sum(name in methods(row) for row in rows) for name in ("cf", "modular", "fermat")}
        totals["cf_without_modular"] = sum("cf" in methods(r) and "modular" not in methods(r) for r in rows)
        totals["cf_only"] = sum(methods(r) == {"cf"} for r in rows)
        totals["any"] = sum(bool(methods(r)) for r in rows)
        small.append(dict(factor_bits=width, splits=totals, rows=rows))
    controls = []
    for case in json.loads(CONTROL_FILE.read_text()):
        if case["id"] in ("target-norm-fresh-2048", "target-norm-crossed-2048"):
            controls.append(dict(id=case["id"], n=case["n"], factor_bits=1024,
                                 **search(int(case["n"]), 1024, compare_full=True)))
    if len(controls) != 2:
        raise ValueError("expected the fresh and crossed controls")
    return dict(seed=SEED.decode(), fermat_midpoint_budget=FERMAT_LIMIT,
                rows_per_width=ROWS_PER_WIDTH, small=small, controls=controls)


def verify(record):
    """Check the product and both primes for each unique recovered factorization in one Lean run."""
    imports, bodies, goals, proofs = set(), [], [], []
    rows = [row for block in record["small"] for row in block["rows"]] + record["controls"]
    for i, row in enumerate(rows):
        successes = {tuple(row[method]["pair"]) for method in methods(row)}
        if not successes:
            continue
        if len(successes) != 1:
            raise ArithmeticError("different searches returned different pairs")
        pair = list(map(int, successes.pop()))
        n = int(row["n"])
        if prod(pair) != n:
            raise ArithmeticError("factor product mismatch")
        source = render_certificate(n, pair)
        imports.update(line for line in source.splitlines() if line.startswith("import "))
        body = source.split("namespace PrimeFactors.Generated\n", 1)[1].split("#print axioms", 1)[0].strip()
        bodies.append(f"namespace Case{i}\n{body}\nend Case{i}")
        goals.append(f"ExactFactorization {n} {pair}")
        proofs.append(f"Case{i}.factorization")
    if not proofs:
        raise ValueError("no factorizations in the panel to certify")
    body = " ∧\n  ".join(goals)
    proof = "⟨" + ", ".join(proofs) + "⟩" if len(proofs) > 1 else proofs[0]
    path = ROOT / "build/ScaledPowerMenu.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    namespace = "PrimeFactors.ScaledPowerMenu"
    path.write_text("\n\n".join(["\n".join(sorted(imports)), "set_option maxRecDepth 8192",
                                 f"namespace {namespace}", *bodies,
                                 f"theorem panel :\n  {body} :=\n  {proof}", "#print axioms panel",
                                 f"end {namespace}", ""]))
    verify_file(path, namespace+".panel")
    return len(proofs)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    modes = cli.add_mutually_exclusive_group()
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check", action="store_true")
    cli.add_argument("--verify", action="store_true", help="check every recovered prime pair with Lean")
    args = cli.parse_args()
    record = measure()
    if args.write:
        RECORD.write_text(json.dumps(record, indent=2)+"\n")
    if args.check and record != json.loads(RECORD.read_text()):
        raise SystemExit("the recomputed power menu dispositions or work counts have changed")
    for block in record["small"]:
        print(block["factor_bits"], block["splits"])
    for row in record["controls"]:
        print(row["id"], row["menu"], row["cf"], row["modular"], row["full_cf"])
    if args.verify:
        print(f"Lean checked {verify(record)} factor pairs.")
