"""Check the joint Jacobi-filter limits on the two existing balanced inputs."""
import argparse
from fractions import Fraction
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.mixed_ratio_heights import jacobi
from experiments.reciprocal_anchor import collect_anchors, progressions, candidate_cap
from scripts.factor import verify_file


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "research/two-character-windows.json"
SCALE = 10**6


def conditions(q):
    root = isqrt(q - 1) + 1
    bits = q.bit_length()
    error = (root * (5220 + 347 * bits) + 2219) // 2220
    minus_one = next(x for x in range(2, 1000) if jacobi(x, q) == -1)
    return root, bits, error, minus_one


def measure(case):
    n = int(case["n"])
    pmax = 2**1024 - 1
    lo, hi = (n - 1) // pmax + 1, isqrt(n)
    anchors = collect_anchors(n, steps=32768, count=2)
    a, b = (v["period"] for v in anchors)
    if gcd(a, b) != 1 or gcd(a * b, 60 * n) != 1:
        raise ValueError("anchor and stride coprimality failed")
    rows = list(progressions(lo, hi, (i for i in range(60) if gcd(i, 60) == 1), 60))
    errors = [conditions(q)[2] for q in (a, b, a*b)]
    total = sum(length for _, length in rows)
    aggregate = sum((length + sum(errors)) // 4 for _, length in rows)
    least = (hi - lo + 1) // 60
    # Uniform integer certificate accounts for every final incomplete wheel lane.
    fraction = Fraction(SCALE * (least + 1 + sum(errors)), 4 * least)
    ppm = -(-fraction.numerator // fraction.denominator)
    return dict(
        id=case["id"], cf_steps=32768, anchor_steps=[v["step"] for v in anchors],
        moduli=[str(a), str(b)], negative_roots=[str(v["minus_root"]) for v in anchors],
        nonprincipal_witnesses=[conditions(q)[3] for q in (a, b, a*b)],
        lower=str(lo), upper=str(hi), wheel_lanes=len(rows),
        wheel_positions=str(total), single_filter_upper=str(candidate_cap(rows, a, a//2)),
        two_filter_upper=str(aggregate), certified_parts_per_million=ppm,
    )


def receipt(case, work, destination):
    n = int(case["n"])
    a, b = map(int, work["moduli"])
    x, y = work["negative_roots"]
    hi = int(work["upper"])
    lines = [
        'import PrimeFactors.TwoCharacterWindow',
        'namespace PrimeFactors.Generated.TwoCharacterReceipt',
        'open TwoCharacterWindow',
        'set_option maxRecDepth 16384',
        'set_option exponentiation.threshold 4096',
        f'private abbrev n : ℕ := {n}', f'private abbrev a : ℕ := {a}',
        f'private abbrev b : ℕ := {b}', f'private abbrev x : ℤ := {x}',
        f'private abbrev y : ℤ := {y}',
        'private abbrev B : ℕ := 2^1024-1',
        'private theorem a3 : a%4=3 := by decide +kernel',
        'private theorem b3 : b%4=3 := by decide +kernel',
        'private theorem ca : n.Coprime a := by decide +kernel',
        'private theorem cb : n.Coprime b := by decide +kernel',
        'private theorem ra : (n:ℤ) ∣ x^2+a := by decide +kernel',
        'private theorem rb : (n:ℤ) ∣ y^2+b := by decide +kernel',
        'private theorem wheelUnit : n.Coprime 60 := by decide +kernel',
        'private theorem pairwise : a.Coprime b := by decide +kernel',
        f'private theorem root : n.sqrt={hi} :=',
        '  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt\'.mpr (by decide +kernel)))',
        '    (Nat.le_sqrt\'.mpr (by decide +kernel))',
    ]
    for label, name, q in (("a", "a", a), ("b", "b", b), ("ab", "(a*b)", a*b)):
        radius, bits, error, witness = conditions(q)
        lines.extend([
            f'private abbrev E{label} : ℕ := {error}',
            f'private theorem pv{label} (pv : PublishedPV) (s l : ℕ) :',
            f'    total {name} s 60 l ≤ E{label} := by',
            f'  apply progression_bound pv (r:={radius}) (b:={bits})',
            '    (by decide +kernel) (by decide +kernel)',
            f'    ⟨{witness},by norm_num [char,a,b]⟩ (by decide +kernel)',
            '    (by decide +kernel) (by decide +kernel) (by decide +kernel)',
        ])
    cap = work["certified_parts_per_million"]
    lines.extend([
        'theorem checked : a.Coprime b ∧',
        '    (∀ p q : ℕ, n=p*q → Nat.Prime p → 2^1023≤p → p≤q → q≤B →',
        '     ∃ r∈wheel, ∃ i∈hits a b (rowStart (lower n B) r) 60 (rowLength (lower n B) n.sqrt r),',
        '       p=rowStart (lower n B) r+60*i) ∧',
        '    (PublishedPV →',
        f'     {SCALE}*(∑ r ∈ wheel, (hits a b (rowStart (lower n B) r) 60 (rowLength (lower n B) n.sqrt r)).card) ≤',
        f'       {cap}*(∑ r ∈ wheel, rowLength (lower n B) n.sqrt r)) := by',
        '  refine ⟨pairwise,?_,?_⟩',
        '  · intro p q eq prime lowerBound ordered bounded',
        '    have div : p∣n := eq ▸ dvd_mul_right p q',
        '    have info := factors_located prime.pos ordered bounded (wheelUnit.of_dvd_left div)',
        '      (prime.odd_of_ne_two (by omega)) a3 b3 (eq ▸ ca) (eq ▸ cb) (eq ▸ ra) (eq ▸ rb)',
        '    simpa only [←eq] using info',
        '  · intro pv',
        '    apply window_bound (by decide +kernel) (by decide +kernel) (pva pv) (pvb pv) (pvab pv)',
        '    rw [root]',
        '    exact wheel_budget (by decide +kernel) (by decide +kernel)',
        '#print axioms checked',
        'end PrimeFactors.Generated.TwoCharacterReceipt',
    ])
    destination.write_text("\n".join(lines) + "\n")
    verify_file(destination, "PrimeFactors.Generated.TwoCharacterReceipt.checked")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="generate and kernel-check both numeric receipts")
    args = parser.parse_args()
    cases = [c for c in json.loads((ROOT / "benchmarks/reciprocal-anchors.json").read_text())
             if int(c["n"]).bit_length() == 2048]
    expected = json.loads(RESULTS.read_text())
    records = [measure(case) for case in cases]
    if records != expected:
        raise ValueError("two-character measurements disagree with their stored results")
    directory = ROOT / "build/two-character-windows"
    if args.verify:
        directory.mkdir(parents=True, exist_ok=True)
    for case, record in zip(cases, records):
        if args.verify:
            receipt(case, record, directory / (case["id"] + ".lean"))
        print(case["id"], record["certified_parts_per_million"], "parts per million")


if __name__ == "__main__":
    main()
