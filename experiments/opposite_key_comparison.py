"""Compare three product-only searches for complementary values on the same sample words."""

from argparse import ArgumentParser
from collections import Counter
import json
from math import gcd
from pathlib import Path
import platform
from random import Random
from statistics import median
import subprocess
from tempfile import TemporaryDirectory
from time import perf_counter, process_time

from experiments.complementary_keys import search
from experiments.twelve_residue_collision import keys, regular_samples
from experiments.twelve_residue_panel import eligible_pairs


ROOT = Path(__file__).resolve().parents[1]
MODES = ("target", "euclid", "direct")
SEEDS = (86412, 86413, 86414)
BUDGETS = (32, 64, 128, 256, 512)


def direct_search(n, draws, seed):
    """One product of all unordered sums, diagonal included, and one final gcd."""
    rng = Random(seed)
    samples = [rng.randrange(n) for _ in range(draws)]
    work = dict(source="none", setup_gcds=0, inversions=0, regular=None, products=0, direct_gcds=0)
    divisor, samples = regular_samples(samples, n, work)
    if divisor is not None:
        return divisor, work
    work["regular"] = len(samples)
    if samples:
        labels = keys(samples, n)
        work["inversions"] = 1
        product = 1
        for j, value in enumerate(labels):
            shift = value - 1
            for i in range(j + 1):
                product = product * (labels[i] + shift) % n
        work["products"] = len(labels) * (len(labels) + 1) // 2
        divisor = gcd(product, n)
        work["direct_gcds"] = 1
        if divisor == n:
            raise ArithmeticError("the product of complements vanished at both mixed primes")
        if divisor > 1:
            work["source"] = "direct sums"
            return divisor, work
    return None, work


def timed(mode, n, draws, seed):
    start_wall, start_cpu = perf_counter(), process_time()
    if mode == "direct":
        divisor, work = direct_search(n, draws, seed)
    else:
        divisor, work, _ = search(n, draws, seed, mode)
    cpu, wall = process_time() - start_cpu, perf_counter() - start_wall
    if divisor is not None and (not 1 < divisor < n or n % divisor):
        raise ArithmeticError(f"{mode} returned an invalid factor")
    return divisor, work, wall, cpu


def rotated(index):
    index %= len(MODES)
    return MODES[index:] + MODES[:index]


def oracle(p, q, draws, seed):
    """Independent per-prime scalar calculation. Known factors are used only after searches."""
    rng = Random(seed)
    samples = [rng.randrange(p*q) for _ in range(draws)]
    values = {p: [], q: []}
    for x in samples:
        regular = []
        for prime in (p, q):
            t = x*x % prime
            mask = x*(t-1)*(t-9)*(t+3)*(t-3)*((t-3)**2-36*t)
            regular.append(mask % prime != 0)
        if regular[0] != regular[1]:
            return "setup", p if not regular[0] else q
        if regular[0]:
            for prime in (p, q):
                t = x*x % prime
                v = (t**3-45*t*t+135*t-27) * pow((t+3)**3, -1, prime)
                values[prime].append(v*v % prime)

    hits = []
    for prime, labels in values.items():
        residues = set(labels)
        if any((1-u) % prime in residues for u in residues):
            hits.append(prime)
    if len(hits) > 1:
        raise ArithmeticError("opposites unexpectedly occurred at both primes")
    if hits:
        return "complement", hits[0]
    return "none", None


def check_prime_pairs(pairs):
    """Check each prime once and check every product against its two certificates."""
    primes = sorted({prime for _, p, q in pairs for prime in (p, q)})
    statements = ["import Mathlib.Tactic.NormNum.Prime"]
    for prime in primes:
        statements.append(f"private theorem prime{prime} : Nat.Prime {prime} := by norm_num1")
    for n, p, q in pairs:
        statements.append(
            f"example : {p}*{q}={n} ∧ Nat.Prime {p} ∧ Nat.Prime {q} := "
            f"⟨rfl, prime{p}, prime{q}⟩"
        )
    with TemporaryDirectory() as location:
        file = Path(location) / "PrimePairPanel.lean"
        file.write_text("\n".join(statements) + "\n")
        subprocess.run(["lake", "env", "lean", str(file)], cwd=ROOT, check=True)


def census(check=False):
    seed_stream = Random(86412)
    counts, pivots, examples = Counter(), Counter(), {}
    budget = 12
    pairs = []
    for p, q in eligible_pairs(12, 0, seed_stream):
        # Advance for every pair to replay the published panel at each product.
        seed = seed_stream.randrange(1 << 63)
        n = p*q
        if n % 12 not in (5, 7):
            continue
        methods = rotated(counts["products"])
        results = {mode: timed(mode, n, budget, seed)[:2] for mode in methods}
        kind, expected = oracle(p, q, budget, seed)
        for mode in ("direct", "target"):
            if results[mode][0] != expected:
                raise ArithmeticError(f"{mode} differed from the prime-coordinate check for {n}")
        divisor, work = results["euclid"]
        if expected is not None and divisor is None:
            raise ArithmeticError(f"Euclid lost a factor at {n}")
        if divisor is not None and divisor not in (p, q):
            raise ArithmeticError(f"unexpected divisor of {n}")
        counts["products"] += 1
        counts["oracle_" + kind] += 1
        counts["euclid_splits"] += int(divisor is not None)
        if check and divisor:
            a, b = sorted((divisor, n//divisor))
            pairs.append((n, a, b))
        if kind == "setup" and divisor != expected:
            raise ArithmeticError("identical setup checks returned different factors")
        if kind == "complement":
            bucket = "intended_factor" if divisor == expected else "other_factor_on_complement_word"
        elif kind == "none" and divisor is not None:
            bucket = "extra_without_complement"
        else:
            bucket = kind
        counts[bucket] += 1
        if divisor is not None and kind != "setup":
            pivots[work["source"] + " / " + bucket] += 1
            if (bucket, work["source"]) not in examples:
                examples[(bucket, work["source"])] = dict(
                    n=str(n), seed=seed, primes=[str(p), str(q)],
                    oracle_factor=str(expected) if expected else None, euclid_factor=str(divisor),
                    outcome=bucket, euclid_source=work["source"],
                )
    if check:
        check_prime_pairs(pairs)
    return dict(prime_bits=12, product_bits=24, residues=[5, 7], draws=budget, seed=86412,
                counts=counts, euclid_sources=pivots, examples=list(examples.values()))


def full_size():
    fixture = "complementary-keys-fresh-2048"
    cases = json.loads((ROOT / "benchmarks/complementary-keys.json").read_text())
    n = int(next(c["n"] for c in cases if c["id"] == fixture))
    if n.bit_length() != 2048 or n % 12 not in (5, 7):
        raise ValueError("the selected control must be a mixed 2048-bit product")

    rows, summaries = [], []
    keys_by_mode = {
        "target": ("target_values", "target_gcds"), "direct": ("products", "direct_gcds"),
        "euclid": ("euclid_gcds", "euclid_inversions", "coefficient_updates"),
    }
    for draws in BUDGETS:
        runs = []
        for i, seed in enumerate(SEEDS):
            order = rotated(i)
            group = dict(seed=seed, order=list(order), methods={})
            for mode in order:
                divisor, work, wall, cpu = timed(mode, n, draws, seed)
                counters = ["setup_gcds", "inversions", "regular", *keys_by_mode[mode]]
                group["methods"][mode] = dict(
                    factor=str(divisor) if divisor else None, source=work["source"],
                    wall_s=round(wall, 6), cpu_s=round(cpu, 6),
                    **{name: work[name] for name in counters},
                )
            answers = group["methods"]
            if answers["target"]["factor"] != answers["direct"]["factor"]:
                raise ArithmeticError("the two complement products disagree on the full-size control")
            if answers["target"]["factor"] and not answers["euclid"]["factor"]:
                raise ArithmeticError("Euclid missed a known complement")
            runs.append(group)
        rows.append(dict(draws=draws, runs=runs))
        stats = {"draws": draws}
        for mode in MODES:
            stats[mode] = {metric: median(run["methods"][mode][metric] for run in runs)
                           for metric in ("wall_s", "cpu_s")}
        summaries.append(stats)
    return dict(fixture=fixture, n=str(n), product_mod_12=n % 12, seeds=list(SEEDS),
                median_seconds=summaries, measurements=rows)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--check-census", action="store_true",
                        help="replay the small population and check every split with Lean")
    if parser.parse_args().check_census:
        result = census(check=True)
        print(f"Lean checked {result['counts']['euclid_splits']} distinct prime factorizations.")
    else:
        print(json.dumps(dict(generator="python3 -m experiments.opposite_key_comparison",
                              machine=platform.machine(), system=platform.system(),
                              system_release=platform.release(), python=platform.python_version(),
                              full_size=full_size(), mixed_census=census()), indent=2))
