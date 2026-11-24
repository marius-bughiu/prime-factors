#!/usr/bin/env python3
"""Find factors by bounded Fermat search and emit a kernel-checkable Lean proof."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
import json
from math import isqrt, prod
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from time import perf_counter


REPO = Path(__file__).resolve().parents[1]
BASE_PRIME_LIMIT = 1000
TRIAL_LIMIT = 10_000
ROOT_LIMIT = 256


def primes_through(limit: int) -> list[int]:
    sieve = bytearray([1]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = 0
    return [p for p in range(2, limit + 1) if sieve[p]]


TRIAL_PRIMES = primes_through(TRIAL_LIMIT)
SMALL_PRIMES = frozenset(p for p in TRIAL_PRIMES if p <= BASE_PRIME_LIMIT)


@dataclass(frozen=True)
class Witness:
    root: int
    powers: tuple[tuple[int, int], ...]


@lru_cache(maxsize=4096)
def prime_witness(n: int) -> Witness | None:
    """Construct a Lucas certificate, with trial division for small leaves.

    One unstripped cofactor of n-1 can recursively be proved prime. Failure to
    find a witness says nothing about primality.
    """
    if n <= BASE_PRIME_LIMIT:
        return Witness(0, ()) if n in SMALL_PRIMES else None
    # Cheap rejection. A passing Fermat test contributes no evidence to the proof.
    if n % 2 == 0 or pow(2, n - 1, n) != 1:
        return None
    powers = []
    rest = n - 1
    for p in TRIAL_PRIMES:
        if p * p > rest:
            break
        exponent = 0
        while rest % p == 0:
            exponent += 1
            rest //= p
        if exponent:
            powers.append((p, exponent))
    if rest > 1:
        powers.append((rest, 1))
    if any(prime_witness(p) is None for p, _ in powers):
        return None
    for g in range(2, min(n, ROOT_LIMIT + 1)):
        if pow(g, n - 1, n) == 1 and all(
            pow(g, (n - 1) // p, n) != 1 for p, _ in powers
        ):
            return Witness(g, tuple(powers))
    return None


def fermat_split(n: int, limit: int) -> tuple[int | None, int]:
    """Try at most limit consecutive midpoints starting at ceil(sqrt(n))."""
    midpoint = isqrt(n - 1) + 1
    delta = midpoint * midpoint - n
    for step in range(1, limit + 1):
        distance = isqrt(delta)
        if distance * distance == delta:
            divisor = midpoint - distance
            return (divisor if divisor > 1 else None), step
        delta += 2 * midpoint + 1
        midpoint += 1
    return None, limit


def remove_hints(n: int, hints: list[int]) -> int:
    """Divide out the supplied hints in order. Hints can be composite."""
    cofactor = n
    for divisor in hints:
        if divisor < 2 or cofactor % divisor:
            raise ValueError(f"factor hint {divisor} must divide remaining cofactor {cofactor}")
        cofactor //= divisor
    return cofactor


def discover(n: int, max_steps: int, hints: list[int]) -> tuple[list[int], list[int], int]:
    """Return prime candidates with witnesses, unresolved cofactors and midpoint count."""
    if n < 1 or max_steps < 0:
        raise ValueError("expected a positive integer and a nonnegative step budget")
    factors = []
    pending = [*hints, remove_hints(n, hints)]
    steps = 0
    remaining = []
    while pending:
        value = pending.pop()
        # Strip small primes before centering the Fermat search on odd cofactors.
        for p in TRIAL_PRIMES:
            if p > 97 or p > value:
                break
            while value % p == 0:
                factors.append(p)
                value //= p
        if value == 1:
            continue
        if prime_witness(value) is not None:
            factors.append(value)
            continue
        divisor, used = fermat_split(value, max_steps - steps)
        steps += used
        if divisor is None:
            remaining.append(value)
        else:
            pending.extend([value // divisor, divisor])
    return sorted(factors), sorted(remaining), steps


def render_certificate(n: int, factors: list[int]) -> str:
    """Produce Lean source for a full factorization (also accepts externally found factors)."""
    if n < 1 or prod(factors) != n:
        raise ValueError("factor product must equal the positive input")
    lines = [
        "import PrimeFactors.Certificate",
        "import PrimeFactors.Pratt",
        "import Mathlib.Tactic.NormNum.Prime",
        "import Mathlib.Tactic.ReduceModChar",
        "",
        f"set_option exponentiation.threshold {max(256, n.bit_length())}",
        "set_option maxRecDepth 8192",
        "",
        "namespace PrimeFactors.Generated",
        "",
    ]
    emitted = set()

    def emit(p: int) -> None:
        if p in emitted:
            return
        witness = prime_witness(p)
        if witness is None:
            raise ValueError(f"no Lucas primality witness found for {p}")
        for q, _ in witness.powers:
            emit(q)
        lines.append(f"private theorem prime_{p} : Nat.Prime {p} := by")
        if not witness.powers:
            lines.extend(["  norm_num", ""])
        else:
            # Let Lean recompute and check p-1, its quotient by each q, and the modular powers.
            primes = [q for q, _ in witness.powers]
            cover = "covers_one"
            for q, exponent in reversed(witness.powers):
                cover = f"(Covers.cons {exponent} prime_{q} {cover})"
            g = witness.root
            lines.extend([
                f"  apply prime_of_lucas_cover ({g} : ZMod {p}) (ps := {primes})",
                f"  · exact {cover}",
                f"  · change ({g} : ZMod {p}) ^ {p - 1} = 1",
                "    reduce_mod_char",
                "  · intro q hq",
                "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq",
                "    rcases hq with " + " | ".join("rfl" for _ in primes),
            ])
            for q in primes:
                lines.extend([
                    f"    · change ({g} : ZMod {p}) ^ {(p - 1) // q} ≠ 1",
                    "      reduce_mod_char",
                    "      decide",
                ])
            lines.append("")
        emitted.add(p)

    for p in sorted(set(factors)):
        emit(p)
    ordered = sorted(factors)
    lines.extend([
        f"theorem factorization : ExactFactorization {n} {ordered} := by",
    ])
    # Explicit intermediate products avoid unification trying to solve '?x * ?y = n'.
    for p in ordered:
        n //= p
        lines.append(f"  apply ExactFactorization.cons (n := {n}) prime_{p}")
    lines.extend([
        "  exact exactFactorization_nil",
        "",
        "#print axioms factorization",
        "",
        "end PrimeFactors.Generated",
        "",
    ])
    return "\n".join(lines)


def verify_file(path: Path) -> None:
    checked = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", str(path.resolve())],
        cwd=REPO, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if checked.returncode:
        raise ValueError(checked.stdout.strip() or "Lean returned an error")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    theorem = "'PrimeFactors.Generated.factorization'"
    if f"{theorem} does not depend on any axioms" in checked.stdout:
        return
    match = re.search(re.escape(theorem) + r" depends on axioms:\s*\[([^\]]+)\]", checked.stdout)
    if match is None or not {a.strip() for a in match[1].split(",")} <= allowed:
        raise ValueError("generated theorem failed its axiom audit:\n" + checked.stdout)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="positive integer in decimal")
    parser.add_argument("--max-steps", type=int, default=10000, help="total Fermat midpoint budget")
    parser.add_argument("--method", choices=("fermat", "subgroup"), default="fermat",
                        help="subgroup tries a small-base gcd split before the Fermat search")
    parser.add_argument("--max-base", type=int,
                        help="last subgroup base to try (default: bit length squared)")
    parser.add_argument("--factor-hint", type=int, action="append", default=[], metavar="D",
                        help="split off this known divisor before searching (repeatable)")
    parser.add_argument("--lean", type=Path, metavar="FILE", help="save the generated Lean proof")
    parser.add_argument("--verify", action="store_true", help="run lake env lean on the certificate")
    args = parser.parse_args()
    try:
        start = perf_counter()
        hints = list(args.factor_hint)
        subgroup = None
        if args.max_base is not None and (args.method != "subgroup" or args.max_base < 1):
            raise ValueError("--max-base requires subgroup mode and a positive bound")
        if args.n < 1 or args.max_steps < 0:
            raise ValueError("expected a positive integer and a nonnegative step budget")
        if args.method == "subgroup":
            # Both the standalone experiment and this script can be run by filename.
            if not __package__:
                sys.path.insert(0, str(REPO))
            from experiments.subgroup_split import search

            cofactor = remove_hints(args.n, hints)
            if cofactor > 1:
                subgroup = search(cofactor, args.max_base)
                if subgroup["status"] == "split":
                    hints.append(int(subgroup["factor"]))
        factors, remaining, steps = discover(args.n, args.max_steps, hints)
        source = None
        if not remaining and (args.lean or args.verify):
            source = render_certificate(args.n, factors)
        discovery_seconds = perf_counter() - start
        verification_seconds = None
        if source is not None:
            destination = args.lean.resolve() if args.lean else None
            # Write in the destination filesystem so a successful replace is atomic.
            with tempfile.TemporaryDirectory(dir=destination.parent if destination else None) as temp:
                proof = Path(temp) / "Certificate.lean"
                proof.write_text(source, encoding="utf-8")
                if args.verify:
                    start = perf_counter()
                    verify_file(proof)
                    verification_seconds = perf_counter() - start
                if destination:
                    proof.replace(destination)
        report = {
            "n": str(args.n), "bits": args.n.bit_length(), "max_steps": args.max_steps,
            "status": "partial" if remaining else "complete",
            "factors": [str(p) for p in factors], "remaining": [str(p) for p in remaining],
            "fermat_steps": steps, "discovery_seconds": discovery_seconds,
            "verified": verification_seconds is not None, "verification_seconds": verification_seconds,
        }
        if subgroup is not None:
            report["subgroup"] = subgroup
        print(json.dumps(report))
        return 1 if remaining else 0
    except (ValueError, OSError) as error:
        parser.exit(2, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    sys.exit(main())
