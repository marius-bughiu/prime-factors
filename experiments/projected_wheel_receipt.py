"""Generate Lean private-cofactor certificates for the two public full-size inputs."""

import argparse
import json
from math import isqrt
from pathlib import Path

from experiments.pell_pairs import convergents
from experiments.pell_relations import _private_parts


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "research/many-character-windows.json"
RECEIPT = ROOT / "benchmarks/controls/ProjectedWheelPrivate.lean"
EXTERNAL = 2 * 3 * 5 * 7 * 11
STEPS = 256


def generate(steps=STEPS):
    paragraphs = [
        "import PrimeFactors.SquareClassPrivateRows",
        "/-! Reproduce with python3 -m experiments.projected_wheel_receipt --check. -/",
        "namespace PrimeFactors.ProjectedWheelPrivate\nopen SquareClassPrivateRows",
    ]
    for case in json.loads(INPUT.read_text()):
        label = case["id"].removeprefix("reciprocal-anchor-").removesuffix("-2048")
        n = int(case["n"])
        rows = [den for _, den, _, _, _ in convergents(n, 4, steps)]
        witnesses = []
        for row, private in zip(rows, _private_parts(rows, EXTERNAL)):
            modulus = next((m for m in range(2, 256) if
                            all(z*z % m != private % m for z in range(m))), None)
            if modulus is None:
                raise ValueError(f"no small nonsquare witness for {label}, row {len(witnesses)+1}")
            witnesses.append(f"({row // private},{modulus})")
        lines = [", ".join(witnesses[i:i+8]) for i in range(0, len(witnesses), 8)]
        paragraphs += [
            f"def {label} : ℕ := {n}",
            f"private theorem {label}_sqrt : (4*{label}).sqrt = {isqrt(4*n)} :=\n"
            f"  (Nat.eq_sqrt'.mpr (by decide +kernel)).symm",
            f"private def {label}Witnesses : List (ℕ × ℕ) := [\n  " + ",\n  ".join(lines) + "]",
            f"set_option maxRecDepth 16000 in\nset_option maxHeartbeats 1600000 in\nprivate theorem {label}_checks :\n"
            f"    let rows := cfRows {label} {steps}\n"
            f"    check rows.prod {EXTERNAL} rows {label}Witnesses = true := by\n"
            f"  simp only [cfRows, {label}_sqrt]\n  decide +kernel",
            f"theorem {label}_obstruction {{s : List ℕ}} (sub : s.Sublist (cfRows {label} {steps}))\n"
            f"    (nonempty : s ≠ []) {{M k : ℕ}} (support : M ∣ {EXTERNAL}^k) :\n"
            f"    ¬ IsSquare (s.prod * M) :=\n"
            f"  no_supported_square {label}_checks sub nonempty support",
            f"theorem {label}_no_remainder {{s : List ℕ}} (sub : s.Sublist (cfRows {label} {steps}))\n"
            f"    (nonempty : s ≠ []) {{M k : ℕ}} (support : M ∣ {EXTERNAL}^k) (z : ℕ) :\n"
            f"    s.prod ≠ M*z^2 :=\n"
            f"  no_supported_remainder {label}_checks sub nonempty support z",
        ]
    paragraphs += ["end PrimeFactors.ProjectedWheelPrivate"]
    return "\n\n".join(paragraphs) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify the existing receipt matches the public inputs")
    args = parser.parse_args()
    source = generate()
    if args.check:
        if RECEIPT.read_text() != source:
            parser.exit(1, "receipt differs from the regenerated source\n")
    else:
        RECEIPT.write_text(source)
