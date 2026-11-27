"""Construct a selected 2048-bit control and check its negative-target obstruction in Lean."""

import argparse
from hashlib import sha256
import json
from math import prod
from pathlib import Path

from experiments.norm_direction_check import prime_root
from experiments.signed_norm_arcs import search
from scripts.factor import prime_witness, primes_through, render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "research/negative-menu-control.json"
BUILD = ROOT / "build/negative-menu-control"
BOUND = 739
PRIMES = primes_through(BOUND)
EXCLUDED_THROUGH = 769
MODULI = [8, *PRIMES[1:]]
PERIOD = prod(MODULI)
CRT = {m: (PERIOD//m)*pow(PERIOD//m, -1, m) for m in MODULI}
NONRESIDUES = {
    ell: [r for r in range(1, ell) if pow(r, (ell-1)//2, ell) == ell-1]
    for ell in PRIMES if ell % 4 == 3
}


def construct(side):
    """Return the first prime with an order witness in a reproducible CRT stream."""
    signed_primes = list(NONRESIDUES)[side::2]
    lower, upper = 3 << 1022, 1 << 1024
    candidates = 0
    for seed in range(4096):
        residue = 1 + ((7 if side == 0 else 1)-1)*CRT[8]
        for ell in signed_primes:
            digest = sha256(f"negative-menu-v1/{side}/{seed}/{ell}".encode()).digest()
            choices = NONRESIDUES[ell]
            residue += (choices[int.from_bytes(digest, "big") % len(choices)]-1)*CRT[ell]
        first = lower + (residue-lower) % PERIOD
        for candidate in range(first, upper, PERIOD):
            candidates += 1
            witness = prime_witness(candidate, BOUND)
            if witness is not None:
                covered = prod(p**e for p, e in witness.powers)
                return candidate, dict(seed=seed, candidates=candidates, covered_order_bits=covered.bit_length())
    raise RuntimeError("no accepted prime in the bounded construction")


def obstruction(n, roots, p, q):
    excluded = primes_through(EXCLUDED_THROUGH)
    lines = [
        "import PrimeFactors.NegativeTargetObstruction",
        "import Mathlib.Tactic.NormNum.Prime",
        "import Mathlib.Tactic.ReduceModChar",
        "set_option maxRecDepth 16384",
        "set_option maxHeartbeats 2000000",
        "namespace PrimeFactors.NegativeMenuControl",
        f"private abbrev n : ℕ := {n}",
        f"private def basis : List ℕ := {excluded}",
        "private theorem n_odd : Odd n := Nat.odd_iff.mpr (by decide +kernel)",
        "private theorem basis_complete : ∀ r : Fin 773, r.val.Prime → r.val ∈ basis := by decide +kernel",
    ]
    for d in [-1, *excluded]:
        name = "neg" if d < 0 else str(d)
        expected = -1 if d < 0 else 1
        lines.extend([
            f"private theorem sign_{name} : jacobiSym ({d}) n = {expected} := by",
            f"  rw [jacobiSym.mod_right ({d}) n_odd]",
            f"  change jacobiSym ({d}) {n % (4*abs(d))} = {expected}",
            "  norm_num",
        ])
    lines.extend([
        "private theorem signs : ∀ d ∈ basis, jacobiSym (d : ℤ) n = 1 := by",
        "  unfold basis",
    ])
    for ell in excluded:
        lines.append(f"  refine List.forall_mem_cons.mpr ⟨sign_{ell}, ?_⟩")
    lines.extend([
        "  simp",
        "theorem obstruction :",
        "    (∀ w : List ℤ, (∀ d ∈ w, ∃ r : ℕ, r.Prime ∧ r < 773 ∧ d = (r : ℤ)) →",
        "      ¬ IsSquare ((-w.prod : ℤ) : ZMod n)) ∧",
        "    ¬ IsSquare ((-773 : ℤ) : ZMod n) ∧",
        "    IsSquare (2 : ZMod n) ∧ IsSquare ((-7*773 : ℤ) : ZMod n) ∧",
        "    IsSquare ((-809 : ℤ) : ZMod n) ∧ Nat.Prime 773 ∧ 2^2047 ≤ n ∧ n < 2^2048 ∧",
        f"    2^1023 ≤ ({p} : ℕ) ∧ ({p} : ℕ) < 2^1024 ∧",
        f"    2^1023 ≤ ({q} : ℕ) ∧ ({q} : ℕ) < 2^1024 := by",
        "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩",
        "  · intro w support",
        "    apply NegativeTargetObstruction.no_negative_word n_odd sign_neg",
        "    intro d hd",
        "    obtain ⟨r, prime, bound, rfl⟩ := support d hd",
        "    exact signs r (basis_complete ⟨r, by omega⟩ prime)",
        f"  · apply ThreeRootTargets.reject (p := {p}) (a := {p % (4*773)})",
        f"      ⟨{q}, by decide +kernel⟩ (Nat.odd_iff.mpr (by decide +kernel))",
        "      (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel)",
        "    norm_num",
        *(f"  · exact ⟨({roots[d]} : ZMod n), by unfold n; reduce_mod_char⟩" for d in [2, -7*773, -809]),
        "  · decide +kernel",
        "#print axioms obstruction",
        "end PrimeFactors.NegativeMenuControl",
    ])
    return "\n".join(lines) + "\n"


def inputs():
    p, pwork = construct(0)
    q, qwork = construct(1)
    n = p*q
    roots = {}
    for d in (2, -7*773, -809):
        a, b = prime_root(d, p), prime_root(d, q)
        roots[d] = a + p*((b-a)*pow(p, -1, q) % q)
        if (roots[d]**2-d) % n:
            raise ArithmeticError("CRT root failed verification")
    if p % 8 != 7 or q % 8 != 1 or n.bit_length() != 2048:
        raise ArithmeticError("constructed input failed its defining conditions")
    return p, q, n, roots, [pwork, qwork]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true", help="verify both Lean sources and compare with the saved receipt")
    args = parser.parse_args()
    p, q, n, roots, work = inputs()
    BUILD.mkdir(parents=True, exist_ok=True)
    certs = [
        ("Factor", render_certificate(n, [p, q], certificate_trial_limit=BOUND), "PrimeFactors.Generated.factorization"),
        ("Obstruction", obstruction(n, roots, p, q), "PrimeFactors.NegativeMenuControl.obstruction"),
    ]
    hashes = {}
    for name, source, theorem in certs:
        path = BUILD / f"{name}.lean"
        path.write_text(source)
        verify_file(path, theorem)
        hashes[name] = sha256(source.encode()).hexdigest()

    prefix = search(n, "integer_arcs", max_blocks=64, domain="unit")
    if prefix["targets"] != [2, 3, 6] or prefix["complete"] or prefix["work"]["blocks"] != 64:
        raise ArithmeticError("unexpected signed-menu prefix")
    prefix["remaining"] = [str(n)] if prefix["factor"] is None else []
    result = dict(selection="Constructed using CRT residues of both prime labels.",
                  public_product=str(n), product_bits=n.bit_length(), factors=[str(p), str(q)],
                  factor_bits=[p.bit_length(), q.bit_length()], residues_mod_8=[p % 8, q % 8],
                  prime_bound=BOUND, prime_count=len(PRIMES),
                  excluded_through=EXCLUDED_THROUGH, excluded_prime_count=len(primes_through(EXCLUDED_THROUGH)),
                  excluded_targets="Negatives of all products of primes through 769, with repetitions.",
                  first_usable_extra_prime=773, negative_target_at_boundary=-7*773,
                  rejected_negative_target_at_boundary=-773,
                  crt_period=str(PERIOD), crt_period_bits=PERIOD.bit_length(), construction=work,
                  positive_target=2, roots_from_labels={str(d): str(r) for d, r in roots.items()},
                  lean_source_sha256=hashes,
                  product_only_prefix=prefix)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.check:
        if encoded != args.output.read_text():
            raise ValueError("reconstructed control differs from saved receipt")
    else:
        args.output.write_text(encoded)


if __name__ == "__main__":
    main()
