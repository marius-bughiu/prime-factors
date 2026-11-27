"""Replay the exact forced totient divisors at 2048 bits from six published primes.

Run python3 -m experiments.full_width_totient_divisor --check. All inputs and
certificate emitters come from this MIT-licensed repository. The grouped-norm
prime theorems are imported. The two Pocklington chains are shared by the signed
three-target control and the fresh control. No candidates are generated or searched.
"""
import argparse
import json
from math import gcd
from pathlib import Path

from experiments.certified_control import lean_source
from scripts.factor import render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
THEOREM = 'PrimeFactors.FullWidthTotientDivisor.common_iff'
CASES = {
    1: (('adjacentSmall', 'separatedLarge'), ('reduced', 'freshLeft')),
    5: (('right1024', 'adjacentSmall'), ('left1024', 'reduced')),
    7: (('left1024', 'adjacentSmall'), ('right1024', 'reduced')),
    11: (('reduced', 'adjacentSmall'), ('right1024', 'left1024')),
}
TARGET = {1: 4, 5: 12, 7: 8, 11: 24}


def fixture(filename, case):
    rows = json.loads((ROOT / 'benchmarks' / filename).read_text())
    return list(map(int, next(row for row in rows if row['id'] == case)['factors']))


def source():
    fresh = json.loads((ROOT / 'research/certified-control.json').read_text())
    targets = json.loads((ROOT / 'research/three-target-limits.json').read_text())
    signed = next(row for row in targets if row['menu'] == 'signed')
    left, right = map(int, signed['primes'])
    chains = {}
    for side, prime in [('left', left), ('right', right)]:
        parents = fresh['chains'][side][:-1]
        r = int(parents[-1]['prime'])
        k, rem = divmod(prime - 1, 2*r)
        witness = pow(2, 2*k, prime)
        if rem or prime > r*r or pow(witness, r, prime) != 1 or gcd(witness-1, prime) != 1:
            raise ValueError(f'invalid published Pocklington node for {side}')
        chains[side] = [*parents, dict(bits=1024, prime=str(prime), order_witness=str(witness))]
    prefix = lean_source(dict(chains=chains, product=str(left*right)), include_signature=False,
                         generator_comment='From the published signed three-target and fresh controls.')
    imports, parents = prefix.split('namespace PrimeFactors.Generated', 1)
    parents = parents.split('def controlProduct', 1)[0]
    node = fresh['chains']['left'][-1]
    reduced = fixture('reduced-orders.json', 'reduced-2048')[1]
    reduced_source = render_certificate(reduced, [reduced])
    reduced_body = reduced_source.split('namespace PrimeFactors.Generated', 1)[1].split(
        'end PrimeFactors.Generated', 1)[0]
    primes = {
        'adjacentSmall': min(fixture('grouped-norm.json', 'grouped-norm-adjacent-2048')),
        'separatedLarge': max(fixture('grouped-norm.json', 'grouped-norm-separated-2048')),
        'reduced': reduced, 'freshLeft': int(node['prime']), 'left1024': left, 'right1024': right,
    }
    lines = ['import PrimeFactors.CyclotomicDigitPeriod', 'import PrimeFactors.CyclotomicRadixLift',
             imports, 'namespace PrimeFactors.FullWidthReduced', reduced_body,
             'end PrimeFactors.FullWidthReduced', 'namespace PrimeFactors.FullWidthTotientDivisor',
             'open GroupedNormExamples CyclotomicDigitPeriod', 'set_option exponentiation.threshold 4096',
             parents, f"private abbrev freshLeft : ℕ := {node['prime']}",
             'private theorem freshLeft_prime : freshLeft.Prime := by',
             f"  apply certifyStep ({node['order_witness']} : ZMod freshLeft) left513_prime",
             '  · decide', '  · decide', '  · unfold freshLeft left513; reduce_mod_char',
             '  · decide +kernel', f'private abbrev reduced : ℕ := {reduced}',
             'private theorem reduced_prime : reduced.Prime :=',
             '  FullWidthReduced.factorization.2 reduced (by simp)',
             'private theorem adjacentSmall_prime : adjacentSmall.Prime := grouped_examples.1.2.1',
             'private theorem separatedLarge_prime : separatedLarge.Prime := grouped_examples.2.1.2.2.1',
             """
/-- Divisibility on every ordered, distinct, equal-width pair with a full-size product. -/
def Common (r d : ℕ) := ∀ {p q}, FullPair (p*q) p q → p*q%12=r → d∣(p-1)*(q-1)

private def Size (p q : ℕ) := 2^1023≤p ∧ p<q ∧ q<2^1024 ∧ 2^2047≤p*q ∧ p*q<2^2048

private theorem test {d r p q : ℕ} (h : Common r d) (hp : p.Prime) (hq : q.Prime)
    (v : Size p q ∧ p*q%12=r) : d∣(p-1)*(q-1) := h ⟨rfl,hp,hq,v.1⟩ v.2

theorem common_iff {r d : ℕ} (cls : r=1 ∨ r=5 ∨ r=7 ∨ r=11) :
    Common r d ↔ d∣CyclotomicRadixLift.stride r := by
  constructor
  · intro h
    rcases cls with rfl|rfl|rfl|rfl"""]
    for residue, pairs in CASES.items():
        totals = []
        for a, b in pairs:
            p, q = primes[a], primes[b]
            if not (2**1023 <= p < q < 2**1024 and
                    (p*q).bit_length() == 2048 and p*q % 12 == residue):
                raise ValueError(f'inconsistent full-width fixture {a}, {b}')
            totals.append((p-1)*(q-1))
        if gcd(*totals) != TARGET[residue]:
            raise ValueError(f'wrong class gcd for {residue}')
        (a,b),(c,e) = pairs
        lines.extend([f'    · have x := test h {a}_prime {b}_prime (by unfold Size; decide +kernel)',
                      f'      have y := test h {c}_prime {e}_prime (by unfold Size; decide +kernel)',
                      f'      rw [←show (({a}-1)*({b}-1)).gcd (({c}-1)*({e}-1)) =',
                      f'        CyclotomicRadixLift.stride {residue} by decide +kernel]',
                      '      exact Nat.dvd_gcd x y'])
    lines.append("""
  · intro h p q pair residue
    obtain ⟨_,pp,qp,low,lt,_,_,_⟩ := pair
    have large : 2 < 2^1023 := by decide +kernel
    have hi : CyclotomicRadixLift.stride (p*q) = CyclotomicRadixLift.stride r := by
      rw [←residue]
      unfold CyclotomicRadixLift.stride CyclotomicRadixLift.weight CyclotomicRadixLift.bonus
      rw [Nat.mod_mod_of_dvd _ (by decide : 4∣12),Nat.mod_mod_of_dvd _ (by decide : 3∣12)]
    rw [←hi] at h
    exact h.trans (CyclotomicRadixLift.divides (pp.odd_of_ne_two (by omega))
      (qp.odd_of_ne_two (by omega)))

#print axioms common_iff
end PrimeFactors.FullWidthTotientDivisor
""")
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check the generated proof and audit its axioms')
    parser.add_argument('--output', type=Path, default=ROOT/'build/FullWidthTotientDivisor.lean')
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source())
    if args.check:
        verify_file(args.output, THEOREM)
        print(f'Lean verified {THEOREM} for all four classes at exactly 2048 bits.')
    print(args.output)


if __name__ == '__main__':
    main()
