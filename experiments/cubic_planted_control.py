"""Construct and independently certify a branched cubic example.

Run python3 -m experiments.cubic_planted_control --check --verify from the
project root. The increasing search over d constructs an example in a
prescribed family. Recovery from N alone is a separate statement in the
generated Lean receipt.
"""

import argparse
from collections import Counter
from math import gcd, prod
from pathlib import Path
from subprocess import run
from time import perf_counter

from experiments.small_factorization import factor_small
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT/'benchmarks/controls/CubicForcedControl.lean'
SHIFT = 308
SIEVE = 8191
BLOCK = 500_000


def sides(s):
    return (4*s**3-4*s*s+2*s-1, 4*s**3+4*s*s+2*s+1)


def start(bits):
    """First positive multiplier whose product has at least this bit length."""
    def enough(d):
        p, q = sides((d << SHIFT)+1)
        return (p*q).bit_length() >= bits

    lo, hi = 1, 2
    while not enough(hi):
        hi *= 2
    while lo < hi:
        mid = (lo+hi)//2
        if enough(mid):
            hi = mid
        else:
            lo = mid+1
    return lo


def forbidden_residues():
    result = []
    for prime in primes_through(SIEVE):
        if prime == 2:
            continue  # All three candidates are odd.
        inverse = pow(2, -SHIFT, prime)
        for residue in range(prime):
            p, q = sides(residue)
            if not (residue*p*q) % prime:
                result.append((prime, (residue-1)*inverse % prime))
    return result


def order_witness(n, factors):
    order = prod(p**e for p, e in factors.items())
    if (n-1) % order:
        raise ValueError('requested local order must divide the predecessor')
    for base in range(2, 257):
        z = pow(base, (n-1)//order, n)
        if pow(z, order, n) == 1 and all(gcd(pow(z, order//p, n)-1, n) == 1 for p in factors):
            return z
    return None


def construct():
    lo, hi = start(2048), start(2049)
    forbidden = forbidden_residues()
    work = Counter()
    for first in range(lo, hi, BLOCK):
        length = min(hi-first, BLOCK)
        live = bytearray(b'\1')*length
        work['blocks'] += 1
        for p, r in forbidden:
            pos = (r-first) % p
            live[pos::p] = bytes((length-pos+p-1)//p)
        pos = live.find(1)
        while pos != -1:
            d = first+pos
            s = (d << SHIFT)+1
            p, q = sides(s)
            # These screens reject candidates only. Every accepted candidate
            # must have three kernel-checkable order witnesses.
            for name, candidate in (('s', s), ('p', p), ('q', q)):
                work[name+'_screens'] += 1
                if pow(2, candidate-1, candidate) != 1:
                    break
            else:
                covered = ({2: SHIFT}, factor_small(2*d), {2: 1, s: 1})
                covered[1][2] += SHIFT
                roots = [order_witness(number, factors) for number, factors in zip((s,p,q), covered)]
                if all(z is not None for z in roots):
                    return (s,p,q), covered, roots, dict(work, first_d=lo, stop_d=hi,
                            hit_d=d, inspected=d-lo+1, residue_classes=len(forbidden))
            pos = live.find(1, pos+1)
    raise RuntimeError('no simultaneous certified candidate in the prescribed finite interval')


def receipt(numbers, covered, roots):
    s, p, q = numbers
    n = p*q
    lines = ['import PrimeFactors.Certificate', 'import PrimeFactors.CubicPlantedPrimality',
             'import PrimeFactors.CubicForcedParameters',
             'import Mathlib.Tactic.NormNum.Prime', 'import Mathlib.Tactic.ReduceModChar', '',
             '-- Generated from the increasing construction in experiments/cubic_planted_control.py.',
             'set_option maxRecDepth 8192', 'set_option exponentiation.threshold 2048', '',
             'namespace PrimeFactors.CubicForcedControl', '',
             f'abbrev parameter : ℕ := {s}', f'abbrev left : ℕ := {p}', f'abbrev right : ℕ := {q}',
             f'abbrev publicProduct : ℕ := {n}', '']
    small = sorted({r for group in covered for r in group if r != s})
    for r in small:
        lines.extend([f'private theorem small_{r} : Nat.Prime {r} := by norm_num', ''])
    for name, number, factors, z in zip(('parameter','left','right'), numbers, covered, roots):
        order = prod(r**e for r,e in factors.items())
        ps = list(factors)
        proof = 'covers_one'
        for r in reversed(ps):
            lemma = 'parameter_prime' if r == s else f'small_{r}'
            proof = f'(Covers.cons {factors[r]} {lemma} {proof})'
        lines.append(f'theorem {name}_prime : Nat.Prime {name} := by')
        ps_lean = '[' + ','.join(map(str, ps)) + ']'
        if name == 'parameter':
            lines.extend([f'  apply prime_of_partial_order_cover ({z} : ZMod {name}) (F := {order}) (ps := {ps_lean})',
                          '  · decide', '  · decide', '  · decide +kernel'])
        else:
            low = 3 if name == 'left' else 1
            lines.extend([f'  apply CubicPlantedPrimality.prime_of_order ({z} : ZMod {name})',
                          f'    (F := {order}) (low := {low}) (high := {s+1}) (ps := {ps_lean})',
                          '  · decide', '  · decide', '  · decide +kernel', '  · decide', '  · decide',
                          '  · exact fun _ _ => CubicPlantedPrimality.reject_' +
                          ('three (by decide)' if low == 3 else 'one')])
        lines.extend([f'  · exact {proof}', f'  · unfold {name}', '    reduce_mod_char',
                      '  · intro r mem',
                      '    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem',
                      '    rcases mem with ' + ' | '.join('rfl' for _ in ps)])
        for r in ps:
            exponent = order//r
            residue = pow(z, exponent, number)
            lines.extend([f'    · change Nat.Coprime ((({z} : ZMod {name}) ^ {exponent} - 1).val) {name}',
                          f'      have h : ({z} : ZMod {name}) ^ {exponent} = {residue} := by',
                          f'        unfold {name}', '        reduce_mod_char', '      rw [h]', '      decide +kernel'])
        lines.append('')
    lines.extend(['theorem factorization : ExactFactorization publicProduct [left,right] := by',
                  '  refine ⟨by decide +kernel, ?_⟩', '  intro r hr',
                  '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr',
                  '  rcases hr with rfl | rfl', '  · exact left_prime', '  · exact right_prime', '',
                  'theorem dimensions : 2^2047 ≤ publicProduct ∧ publicProduct < 2^2048 ∧',
                  '    2^1023 ≤ left ∧ left < right ∧ right < 2^1024 := by decide +kernel', '',
                  'theorem recovered : CubicForcedParameters.decode publicProduct=some (left,right) := by',
                  '  have input : CubicForcedParameters.target parameter=publicProduct := by decide +kernel',
                  '  have lhs : CubicForcedParameters.low parameter=left := by decide +kernel',
                  '  have rhs : CubicForcedParameters.high parameter=right := by decide +kernel',
                  '  rw [←input,CubicForcedParameters.decode_target (by decide : 2≤parameter),lhs,rhs]', '',
                  'theorem control_checks : CubicForcedParameters.decode publicProduct=some (left,right) ∧',
                  '    ExactFactorization publicProduct [left,right] := ⟨recovered,factorization⟩', '',
                  '#print axioms control_checks', '', 'end PrimeFactors.CubicForcedControl', ''])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare the generated Lean source with the receipt')
    parser.add_argument('--verify', action='store_true', help='strictly check the archived certificate in Lean')
    args = parser.parse_args()
    started = perf_counter()
    values, covered, roots, work = construct()
    output = receipt(values, covered, roots)
    if args.check or args.verify:
        if output != RECEIPT.read_text():
            raise SystemExit('regenerated certificate differs from the archived receipt')
        print(f'Construction {work}, {perf_counter()-started:.3f}s', flush=True)
        if args.verify:
            run(['lake','env','lean','-DwarningAsError=true',str(RECEIPT)], cwd=ROOT, check=True)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
