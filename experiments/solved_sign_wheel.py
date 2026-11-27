"""Solve projected sign equations first, then build just the matching CRT rows."""

import argparse
from functools import lru_cache
from itertools import permutations, product
import json
from math import gcd, prod
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.pell_relations import insert_parity
from experiments.projected_divisor_wheel import BASE, PERIOD, allowed, search, wheel


ROOT = Path(__file__).resolve().parents[1]
PANEL = ROOT / "research/projected-divisor-wheel.json"
MODULI = (8,) + BASE[2:]
FLIP = sum(1 << i for i, p in enumerate(BASE) if i >= 2 and p % 4 == 3)
THREE_ROOTS = 246180296426219


def parity(word):
    return bin(word).count("1") % 2


def local_mask(public):
    # For p = 3 mod 4, the public bit (p/x) is (x/p) XOR (-1/x)
    # in additive sign notation. Substituting it toggles bit zero.
    if not 0 <= public < 1 << len(BASE):
        raise ValueError("constraint uses a character outside the fixed basis")
    return public ^ parity(public & FLIP)


def solve_signs(equations):
    """Yield the actual affine solution set using one free choice per nonpivot."""
    pivots = {}
    for mask, rhs in equations:
        if rhs not in (0, 1):
            raise ValueError("an affine equation requires a binary right-hand side")
        if insert_parity(pivots, local_mask(mask), rhs) == 1:
            return []
    ordered = sorted(pivots.items())

    def complete(free, homogeneous):
        # Each highest-bit pivot depends only on already resolved lower bits.
        for bit, (mask, rhs) in ordered:
            required = parity(mask & free) ^ (0 if homogeneous else rhs)
            free |= required << bit
        return free

    signatures = [complete(0, False)]
    for bit in range(len(BASE)):
        if bit not in pivots:
            direction = complete(1 << bit, True)
            signatures += [s ^ direction for s in signatures]
    return signatures


@lru_cache(maxsize=1)
def local_tables():
    """Allocate local CRT contributions in O(8 + sum of odd primes) entries."""
    if prod(MODULI) != PERIOD:
        raise ArithmeticError("the sign conductor disagrees with the reference wheel")
    tables = []
    for q in MODULI:
        cofactor = PERIOD // q
        basis = cofactor * pow(cofactor, -1, q)
        if q == 8:
            classes = [[], [], [], []]
            for a in (1, 3, 5, 7):
                sign_bits = int(a % 4 == 3) | (int(a in (3, 5)) << 1)
                classes[sign_bits].append(a * basis % PERIOD)
        else:
            # In an odd prime field the squares of the half roots cover each
            # positive unit exactly once. The other units have negative sign.
            squares = {a * a % q for a in range(1, (q + 1) // 2)}
            classes = [[], []]
            for a in range(1, q):
                classes[int(a not in squares)].append(a * basis % PERIOD)
        tables.append(classes)
    return tables


def generate(equations):
    tables = local_tables()
    signatures = solve_signs(equations)
    rows = []
    for signature in signatures:
        parts = [tables[0][signature & 3]]
        for bit, table in enumerate(tables[1:], 2):
            parts.append(table[(signature >> bit) & 1])
        rows.extend(sum(contributions) % PERIOD for contributions in product(*parts))
    rows.sort()
    return rows


@lru_cache(maxsize=1)
def indexed_tables():
    """A second baseline can trade whole-wheel storage for faster repeated queries."""
    buckets = [[] for _ in range(1 << len(BASE))]
    for residue, public_signs in wheel():
        # Local and public words differ on the 3 mod 4 primes whenever (-1/x) is negative.
        local = public_signs ^ (FLIP if public_signs & 1 else 0)
        buckets[local].append(residue)
    return buckets


def indexed_generate(equations):
    buckets = indexed_tables()
    rows = []
    for signature in solve_signs(equations):
        rows.extend(buckets[signature])
    rows.sort()
    return rows


def verify_affine():
    """Exhaust the individual characters and full signatures, including both RHS values."""
    systems = [[(mask, rhs)] for mask in range(1 << len(BASE)) for rhs in (0, 1)]
    systems += [[(1 << bit, (rhs >> bit) & 1) for bit in range(len(BASE))]
                for rhs in range(1 << len(BASE))]
    systems += [[(11, 1), (27, 0), (16, rhs)] for rhs in (0, 1)]
    for eqs in systems:
        reference = [r for r, word in wheel() if all(parity(word & mask) == rhs for mask, rhs in eqs)]
        if generate(eqs) != reference or indexed_generate(eqs) != reference:
            raise ArithmeticError(f"direct Jacobi comparison failed on {eqs}")
    return len(systems)


def timed(callback):
    start = process_time_ns()
    result = callback()
    return result, process_time_ns() - start


def certified_inputs():
    """Reuse the public projector's root receipts without rerunning its continued fractions."""
    public = []
    records = json.loads(PANEL.read_text())["rows"]
    for row in records:
        n = int(row["n"])
        relation = row["relation"]
        constraints = relation["constraints"]
        for eq in constraints:
            mask, delta = eq["mask"], eq["discriminant"]
            if (delta != prod(p for i, p in enumerate(BASE) if (mask >> i) & 1)
                    or gcd(delta, n) != 1 or (int(eq["root"]) ** 2 - delta) % n):
                raise ArithmeticError("a published root failed verification")
        public.append((row["sample"], row["bits"], n, constraints, relation["projected_rank"]))
    return public


def panel(repetitions):
    # Fixed preprocessing and per-product CPU are separate for both methods.
    # Repeat both cold setups with cache cleanup outside their timers.
    setups = {"reference": [], "solved": [], "indexed": []}
    orders = tuple(permutations(setups))
    for repeat in range(repetitions):
        calls = dict(reference=wheel, solved=local_tables, indexed=indexed_tables)
        for key in orders[repeat % len(orders)]:
            fn = calls[key]
            if key == "indexed":
                wheel.cache_clear()
            fn.cache_clear()
            _, duration = timed(fn)
            setups[key].append(duration)
    systems_checked = verify_affine()
    rows = []
    times = {key: [0] * repetitions for key in setups}
    three = None
    for i, (sample, bits, n, constraints, rank) in enumerate(certified_inputs()):
        def solved():
            return generate((eq["mask"], 0) for eq in constraints)

        def reference():
            return allowed(constraints)

        def indexed():
            return indexed_generate((eq["mask"], 0) for eq in constraints)

        durations = {key: [] for key in setups}
        for rep in range(repetitions):
            callbacks = dict(reference=reference, solved=solved, indexed=indexed)
            answers = {}
            for key in orders[(i + rep) % len(orders)]:
                result, elapsed = timed(callbacks[key])
                answers[key] = result
                durations[key].append(elapsed)
                times[key][rep] += elapsed
            if any(xs != answers["reference"] for xs in answers.values()):
                raise ArithmeticError("constructed and scanned divisor classes differ")
        count = len(answers["solved"])
        if count * (1 << rank) != len(wheel()):
            raise ArithmeticError("rank and cardinality disagree")
        rows.append(dict(sample=sample, bits=bits, n=str(n), rank=rank,
                         signatures=1 << (len(BASE) - rank), output_rows=count,
                         median_cpu_ns={k: int(median(v)) for k, v in durations.items()}))
        if n == THREE_ROOTS:
            factor, divisions = search(n, bits, answers["solved"], 1 << bits)
            if not factor or n % factor or divisions != 14474 or count != 240:
                raise ArithmeticError("three-root example disagrees with its benchmark")
            three = dict(n=str(n), factor=str(factor), cofactor=str(n // factor),
                         masks=[eq["mask"] for eq in constraints], discriminants=[eq["discriminant"] for eq in constraints],
                         signatures=1 << (len(BASE) - rank), output_rows=count, divisions=divisions)
    if three is None or len(rows) != 24:
        raise ArithmeticError("expected the 24-input comparison including the three-root case")
    return dict(source=str(PANEL.relative_to(ROOT)), python=platform.python_version(),
                machine=platform.machine(), timings="Median process CPU in rotated method orders; fixed preprocessing separately from warm table generation. Cached published roots are verified before timing; no method reruns continued fractions. Exact sorted list equality checked on every repetition. Indexed precomputes all 1920 residues in sign buckets and uses the same equation solver.",
                repetitions=repetitions, base=BASE, period=PERIOD, full_unit_rows=len(wheel()),
                contributions=sum(len(lane) for table in local_tables() for lane in table),
                fibers_checked=systems_checked, fixed_setup_cpu_ns={k: int(median(v)) for k, v in setups.items()},
                batch_cpu_ns={k: int(median(v)) for k, v in times.items()}, rows=rows, three_roots=three)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=int, default=12)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repetitions <= 0:
        parser.error("repetitions must be positive")
    text = json.dumps(panel(args.repetitions), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
