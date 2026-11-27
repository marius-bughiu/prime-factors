"""Bound the first successful shift using the two synthetic controls' known factors."""

import argparse
from collections import Counter
from fractions import Fraction
import json
from math import gcd, isqrt, prod
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_winner_positions import published_controls
from scripts.factor import primes_through, render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
# The crossed product uses one smaller interval. Each entire interval is checked with
# one weighted trace, so these are certified lower bounds, not an exact first shift.
PREFIX_BITS = {"fresh": 343, "crossed": 342}


def partial_divisors(p, q, trial_primes, children):
    """Count divisors of known parts; identify the uncertified composite remainders."""
    powers = Counter()
    remainders = []
    for z in (p, q):
        rest = z - 1
        for prime in (*trial_primes, *children):
            while rest % prime == 0:
                rest //= prime
                powers[prime] += 1
        remainders.append(rest)
    known = prod(prime**multiplicity for prime, multiplicity in powers.items())
    assert known * prod(remainders) == (p-1)*(q-1)
    assert all(gcd(known, r) == 1 for r in remainders)
    assert gcd(*remainders) == 1
    unknown = [r for r in remainders if r > 1]
    # A composite nonsquare has at least four distinct divisors. These tests for
    # compositeness and nonsquareness are deterministic integer comparisons.
    assert all(pow(2, r-1, r) != 1 and isqrt(r)**2 != r for r in unknown)
    known_count = prod(e+1 for e in powers.values())
    return {
        "known_part_divisors": known_count,
        "composite_remainder_bits": [r.bit_length() for r in unknown],
        "divisor_count_lower_bound": known_count*4**len(unknown),
    }


def private_weights(total, deficit, width):
    """Find a rational approximation to the private curve's slope at the interval midpoint."""
    center = deficit+(width+1)//2
    target = Fraction(total, center**2)
    for bits in range(320, 361):
        frac = target.limit_denominator(1 << bits)
        a, b = frac.numerator, frac.denominator
        z = 4*a*b*total
        m = isqrt(z-1)+1
        r = isqrt(2*m)
        s = isqrt(m*m-z)
        if (m+1 <= 2*a*(deficit+1)+r and
                2*a*(deficit+width) <= m+1+r and s*s < m*m-z):
            return a, b, m, r, s
    raise ValueError("no full-interval certificate at the stated width")


def receipt(label, n, p, q, prime_source):
    total = (p-1)*(q-1)
    deficit = p+q-1
    bits = PREFIX_BITS[label]
    a, b, m, r, s = private_weights(total, deficit, 1 << bits)
    shift = q-p-1
    g = 2*(q-1)
    # Here F/g+1=(p+1)/2. One small divisor supplies a valid nontrivial exponent.
    d = next(ell for ell in primes_through(100) if ((p+1)//2) % ell == 0)
    multiplier = ((p+1)//2)//d
    assert n+shift == g*multiplier*d and multiplier >= 2
    return f"""import PrimeFactors.IntermediatePrivateShiftWindow
{prime_source}
namespace PrimeFactors.Generated.PrivateShiftWindow

open IntermediateShiftCount IntermediatePrivateShiftWindow
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

private abbrev n : ℕ := {n}
private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev F : ℕ := (p-1)*(q-1)
private abbrev D : ℕ := p+q-1

/-- Private-factor diagnostic. The conclusion concerns these two supplied primes and
every possible exponent at the specified shifts. The positive endpoint need not be first. -/
theorem checked : ExactFactorization n [p,q] ∧
    (∀ k, 0<k → k≤2^{bits} → ¬Extra n F k) ∧ Extra n F (q-p-1) ∧
    2^{shift.bit_length()-1}≤q-p-1 ∧ q-p-1<2^{shift.bit_length()} := by
  refine ⟨factorization,?_,?_,by decide +kernel,by decide +kernel⟩
  · apply empty (D:=D) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro v left right
    apply no_divisor (a:={a}) (b:={b}) (m:={m}) (r:={r}) (s:={s}) _ _ _ _ _ _ _ left right
    all_goals decide +kernel
  · exact ⟨{g}*{multiplier},realize (g:={g}) (a:={multiplier}) (d:={d})
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

#print axioms checked
end PrimeFactors.Generated.PrivateShiftWindow
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="kernel-check both generated receipts")
    args = parser.parse_args()
    record = json.loads((ROOT/"research/certified-control.json").read_text())
    children = [int(chain[-2]["prime"]) for chain in record["chains"].values()]
    trial = primes_through(2_000_000)
    out = ROOT / "build/site/proofs"
    out.mkdir(parents=True, exist_ok=True)
    for label, n, p, q in published_controls():
        if label == "small":
            continue
        profile = partial_divisors(p, q, trial, children)
        prime_source = lean_source(record, include_signature=False) if label == "fresh" else render_certificate(n, [p, q])
        path = out/f"intermediate-private-shift-{label}-2048.lean"
        path.write_text(receipt(label, n, p, q, prime_source))
        print(f"{label} partial factorization: {profile}", flush=True)
        if args.check:
            verify_file(path, "PrimeFactors.Generated.PrivateShiftWindow.checked")
            print(f"{label} verified: first extra shift > 2^{PREFIX_BITS[label]}; "
                  f"a {(q-p-1).bit_length()}-bit shift succeeds", flush=True)
        else:
            print(path)


if __name__ == "__main__":
    main()
