"""Generate the fixed recursive Pocklington comparison without running a factor search."""

import argparse
from hashlib import shake_256
import json
from math import gcd, isqrt
from pathlib import Path

from scripts.factor import primes_through, verify_file


DOMAIN = 'prime-factors/certified-control/v1'
ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / 'research/certified-control.json'
CERTIFICATE = ROOT / 'benchmarks/controls/PocklingtonControl.lean'
SEARCH_FIXTURES = ROOT / 'benchmarks/quartic-factor-lanes.json'
SEARCH_ID = 'unit-lane-fresh-2048'
SMALL_PRIMES = primes_through(1000)


def draws(side, bits, low, high):
    """Rejection sampling over the inclusive interval, independently at each level."""
    width = high-low+1
    sample_bits = (width-1).bit_length()
    mask = (1 << sample_bits)-1
    counter = 0
    while True:
        message = f'{DOMAIN}/{side}/{bits}/{counter}'.encode('ascii')
        digest = shake_256(message).digest((sample_bits+7)//8)
        offset = int.from_bytes(digest, 'big') & mask
        counter += 1
        if offset < width:
            yield counter-1, low+offset


def prime_chain(side, bits):
    minimum = 3 << (bits-2) if bits == 1024 else 1 << (bits-1)
    maximum = (1 << bits)-1
    if bits <= 10:
        for counter, k in draws(side, bits, minimum//2, maximum//2):
            n = 2*k+1
            if all(n % d for d in range(2, isqrt(n)+1)):
                return [dict(bits=bits, counter=counter, prime=str(n))]

    chain = prime_chain(side, (bits+1)//2+1)
    r = int(chain[-1]['prime'])
    # Exactly the multipliers K with minimum ≤ 1+2Kr ≤ maximum.
    stride = 2*r
    low = (minimum-2)//stride+1
    high = (maximum-1)//stride
    for counter, k in draws(side, bits, low, high):
        n = 1+2*k*r
        if any(n % p == 0 for p in SMALL_PRIMES):
            continue
        z = pow(2, 2*k, n)
        if gcd(z-1, n) == 1 and pow(z, r, n) == 1:
            assert n <= r*r
            chain.append(dict(bits=bits, counter=counter, prime=str(n),
                              multiplier=str(k), order_witness=str(z)))
            return chain


def generate():
    chains = {side: prime_chain(side, 1024) for side in ('left', 'right')}
    p, q = (int(chain[-1]['prime']) for chain in chains.values())
    assert p != q and (p*q).bit_length() == 2048
    return dict(domain=DOMAIN, product=str(p*q), chains=chains)


def base_two_certificate(record):
    """Use the two largest certified child orders to separate candidate sums."""
    lines = []
    for side, chain in record['chains'].items():
        parent = f"{side}{chain[-1]['bits']}"
        child = f"{side}{chain[-2]['bits']}"
        exponent = 2*int(chain[-1]['multiplier'])
        value = chain[-1]['order_witness']
        lines.extend([
            f"private theorem {side}Witness :",
            f"    (((2 : ZMod {parent})^{exponent})^{child}=1) ∧",
            f"      (2 : ZMod {parent})^{exponent}≠1 := by",
            f"  have val : (2 : ZMod {parent})^{exponent} = {value} := by",
            f"    unfold {parent}", "    reduce_mod_char", "  rw [val]", "  constructor",
            f"  · unfold {parent} {child}", "    reduce_mod_char", "  · decide +kernel", "",
        ])
    n = int(record['product'])
    first = 1+isqrt(4*n-1)
    last = isqrt(9*n//2)
    lines.extend([
        f"private abbrev sumLow : ℕ := {first}",
        f"private abbrev sumHigh : ℕ := {last}", "",
        "theorem base_two_no_repeat {e : ℕ} (positive : 0<e) (small : e≤2^1021) :",
        "    (2 : ZMod controlProduct)^e≠1 := by",
        "  change (2 : ZMod (left1024*right1024))^e≠1",
        "  intro equal",
        "  have divides := FixedBaseSignature.product_period left513_prime right513_prime",
        "    (by decide +kernel) leftWitness.1 leftWitness.2 rightWitness.1 rightWitness.2 equal",
        "  have big : 2^1021 < left513*right513 := by decide +kernel",
        "  exact (not_le_of_gt big) ((Nat.le_of_dvd positive divides).trans small)", "",
        "theorem base_two_isolates (s : ℕ)",
        "    (lo : 4*controlProduct≤s^2) (hi : 2*s^2≤9*controlProduct) :",
        "    (2 : ZMod controlProduct)^s=2^(controlProduct+1) ↔ s=left1024+right1024 := by",
        "  have hs : s ∈ Set.Icc sumLow sumHigh := by",
        "    constructor",
        "    · by_contra! below",
        "      have sq := Nat.pow_le_pow_left (show s≤sumLow-1 by omega) 2",
        "      exact (not_lt_of_ge (lo.trans sq)) (by decide +kernel : (sumLow-1)^2<4*controlProduct)",
        "    · by_contra! above",
        "      have sq := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (show sumHigh+1≤s by omega) 2)",
        "      exact (not_lt_of_ge (sq.trans hi)) (by decide +kernel : 9*controlProduct<2*(sumHigh+1)^2)",
        "  letI : NeZero controlProduct := ⟨by decide +kernel⟩",
        "  let g := ZMod.unitOfCoprime 2 (by decide +kernel : Nat.Coprime 2 controlProduct)",
        "  have trueSum : left1024+right1024 ∈ Set.Icc sumLow sumHigh :=",
        "    ⟨by decide +kernel, by decide +kernel⟩",
        "  have target : g^(left1024+right1024)=g^(controlProduct+1) :=",
        "    unit_pow_factorSum left1024_prime right1024_prime (by decide +kernel) g",
        "  apply FixedBaseSignature.recognize g _ trueSum hs target",
        "  intro e pos limit",
        "  exact base_two_no_repeat pos (limit.trans (by decide +kernel : sumHigh-sumLow≤2^1021))", "",
        "theorem control_checks : ExactFactorization controlProduct [left1024,right1024] ∧",
        "    ∀ s : ℕ, 4*controlProduct≤s^2 → 2*s^2≤9*controlProduct →",
        "      ((2 : ZMod controlProduct)^s=2^(controlProduct+1) ↔ s=left1024+right1024) :=",
        "  ⟨factorization,base_two_isolates⟩", "", "#print axioms control_checks", "",
    ])
    return lines


def lean_source(record):
    lines = [
        'import PrimeFactors.Certificate', 'import PrimeFactors.PartialOrder', 'import PrimeFactors.FixedBaseSignature',
        'import Mathlib.Tactic.NormNum.Prime', 'import Mathlib.Tactic.ReduceModChar', '',
        '-- Generated by experiments/certified_control.py from two independent hash streams.',
        'set_option maxRecDepth 8192', 'set_option exponentiation.threshold 2048', '',
        'namespace PrimeFactors.Generated', '',
        'private theorem certifyStep {n r : ℕ} (z : ZMod n) (prime : r.Prime)',
        '    (size : 1 < n) (large : n ≤ r^2) (full : z^r = 1)',
        '    (proper : Nat.Coprime (z-1).val n) : n.Prime := by',
        '  apply prime_of_partial_order_cover z size prime.pos large (ps := [r])',
        '  · simpa using (Covers.cons (n := 1) 1 prime covers_one)',
        '  · exact full', '  · intro l hl', '    simp only [List.mem_singleton] at hl',
        '    subst l', '    simpa [Nat.div_self prime.pos] using proper', '',
    ]
    for side, chain in record['chains'].items():
        previous = None
        for node in chain:
            name = f"{side}{node['bits']}"
            lines.append(f"private abbrev {name} : ℕ := {node['prime']}")
            lines.append(f'private theorem {name}_prime : Nat.Prime {name} := by')
            if previous is None:
                lines.append(f'  norm_num [{name}]')
            else:
                lines.extend([
                    f"  apply certifyStep ({node['order_witness']} : ZMod {name}) {previous}_prime",
                    '  · decide', '  · decide',
                    f'  · unfold {name} {previous}', '    reduce_mod_char',
                    '  · decide +kernel',
                ])
            lines.append('')
            previous = name
    lines.extend([
        f"def controlProduct : ℕ := {record['product']}", '',
        'theorem full_size : 2^2047 ≤ controlProduct ∧ controlProduct < 2^2048 := by',
        '  decide +kernel', '',
        'theorem factorization : ExactFactorization controlProduct [left1024, right1024] :=',
        '  ExactFactorization.cons (n := right1024) left1024_prime',
        '    (.cons (n := 1) right1024_prime exactFactorization_nil)', '',
        '#print axioms factorization', '', *base_two_certificate(record), 'end PrimeFactors.Generated', '',
    ])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true', help='regenerate the record and Lean source')
    mode.add_argument('--verify', action='store_true', help='check both files and the Lean certificate')
    args = parser.parse_args()
    record = generate()
    data = json.dumps(record, indent=2)+'\n'
    source = lean_source(record)
    if args.write:
        CERTIFICATE.parent.mkdir(parents=True, exist_ok=True)
        RECORD.write_text(data)
        CERTIFICATE.write_text(source)
    elif args.verify:
        if RECORD.read_text() != data or CERTIFICATE.read_text() != source:
            raise ValueError('checked-in construction differs from the deterministic regeneration')
        fixtures = json.loads(SEARCH_FIXTURES.read_text())
        inputs = [case['n'] for case in fixtures if case['id'] == SEARCH_ID]
        if inputs != [record['product']]:
            raise ValueError(f'{SEARCH_ID} must name the certified product exactly once')
        verify_file(CERTIFICATE, 'PrimeFactors.Generated.control_checks')
        print('Regenerated the control, matched its search input and checked the factorization and base-2 test.')
    else:
        print(record['product'])


if __name__ == '__main__':
    main()
