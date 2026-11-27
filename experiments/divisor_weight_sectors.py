"""Turn a public, certified divisor-free interval into a whole family of impossible weight assignments."""

import argparse
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

from experiments.binomial_divisor_window import search as divisor_search
from experiments.quartic_divisor_window import odd_quartile_center
from experiments.rectangular_root_windows import bounds, cube_root, multiplier_ratio
from scripts.factor import verify_file
from scripts.sifted_window_certificate import check_sifted_interval


ROOT = Path(__file__).resolve().parents[1]
IDS = ("sifted-divisor-window-fresh-440", "sifted-divisor-window-crossed-three-quarters")


def convergents(num, den):
    old_a, a, old_b, b = 0, 1, 1, 0
    while den:
        quotient, remainder = divmod(num, den)
        num, den = den, remainder
        old_a, a = a, old_a + quotient * a
        old_b, b = b, old_b + quotient * b
        yield a, b


def in_sector(n, error, first, last, a, b):
    """Both endpoints contain the strip of admissible weighted differences."""
    return (a * first + error) * first <= b * n <= a * last**2 - error * last


def choose(n, first, last):
    """Find an interior rational direction and a unimodular odd starting pair."""
    center = (first + last) // 2
    height, error, cap = bounds(n, 1)
    excess = multiplier_ratio(n, error, 1024)
    top = isqrt(cap)
    for steps, (v, w) in enumerate(convergents(n, center**2), 1):
        if v % 2 == w % 2 or not v * first**2 < w * n < v * last**2:
            continue
        # A Bezout companion makes every weight pair on this line coprime.
        b = pow(v, -1, w)
        a = (v * b - 1) // w
        start = (top // 4) // v
        if not ((a + start * v) % 2 and (b + start * w) % 2):
            start += 1
        a, b = a + start * v, b + start * w
        count = (top - a) // (2 * v) + 1
        fits = (
            0 < b <= a <= top and 0 < w <= v and count > 0
            and a % 2 == b % 2 == 1 and v * b == w * a + 1
            and in_sector(n, 2 * error, first, last, a, b)
            and 1024 * a <= (1024 + excess) * b and 1024 * v <= (1024 + excess) * w
        )
        if fits:
            family = dict(N=n, H=error, L=first, U=last, K=cap, e=excess,
                          A=a, B=b, V=v, W=w, count=count)
            return family, height, steps
    raise ArithmeticError("no interior unimodular family in the prescribed public interval")


def proof_source(f, height, interval_application):
    n = f["N"]
    cube = cube_root(n - 1) + 1
    square = isqrt(n)
    spec = ", ".join(f"{key} := {value}" for key, value in f.items())
    return f"""import PrimeFactors.WeightDivisorSector
import PrimeFactors.SiftedDivisorWindow
set_option exponentiation.threshold 16384
set_option maxRecDepth 10000
namespace PrimeFactors.WeightSectorControl
open WeightDivisorSector RectangularFullWidth

abbrev family : Family := {{ {spec} }}

private theorem excluded (d : ℕ) (lo : family.L≤d) (hi : d≤family.U) : ¬d∣family.N := by
{interval_application}

private theorem valid : Valid family := by
  constructor <;> first | (unfold Sector; decide +kernel) | decide +kernel

private theorem public_parameters :
    family.H=H family.N ∧ family.K=K family.N ∧ family.e=excess family.N := by
  apply WeightDivisorSector.parameters (N:=family.N) (T:={cube}) (S:={square}) (Y:={height})
    (H':=family.H) (K':=family.K) (e:=family.e)
  all_goals decide +kernel

theorem checked :
    (family.H=H family.N ∧ family.K=K family.N ∧ family.e=excess family.N) ∧
    Function.Injective (fun i : Fin family.count => product family i) ∧
    ∀ i : Fin family.count, product family i ∈ RectangularSearchFloor.emitted family.K 1024 family.e ∧
      ∀ p q t x y : ℕ, p*q=family.N → 0<q → 0<t → x≤y → x≤family.H →
      ¬ MixedUnityCofactors.Located t p q (major family i) (minor family i) x y :=
  ⟨public_parameters,collective valid excluded⟩

#print axioms checked
end PrimeFactors.WeightSectorControl
"""


def evaluate(case, folder):
    n, radius = int(case["n"]), int(case["radius"])
    center = odd_quartile_center(n)
    first, last = center - 2 * radius, center + 2 * radius
    work = divisor_search(n, first, 2 * radius, degree=case["degree"], depth=case["depth"],
                          modulus_limit=case["modulus_limit"], centered=True, sifted=True)

    def application(_n, _work, _path, _module, text):
        return text

    witness = check_sifted_interval(n, work, None, application)
    family, height, steps = choose(n, first, last)
    source = proof_source(family, height, witness)
    path = folder / (case["id"] + ".lean")
    path.write_text(source)
    verify_file(path, "PrimeFactors.WeightSectorControl.checked")
    return dict(
        interval_case=case["id"], source_sha256=sha256(source.encode()).hexdigest(),
        continued_fraction_steps=steps, interval_lattice_work=work["work"],
        family={key: str(value) for key, value in family.items()},
        assignments_excluded=str(family["count"]), assignments_enumerated=0, remaining=[str(n)],
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "research/divisor-weight-sectors.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    folder = ROOT / "build/divisor-weight-sectors"
    folder.mkdir(parents=True, exist_ok=True)
    cases = {c["id"]: c for c in json.loads((ROOT / "benchmarks/sifted-divisor-window.json").read_text())}
    results = [evaluate(cases[name], folder) for name in IDS]
    output = json.dumps(results, indent=2) + "\n"
    if args.check:
        if output != args.output.read_text():
            raise ValueError("reconstructed sector receipts differ")
    else:
        args.output.write_text(output)
