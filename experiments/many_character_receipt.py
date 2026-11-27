"""Generate and check Lean certificates for the sixteen-character control windows."""

import argparse
import json
from pathlib import Path

from experiments.many_character_window import COUNT, RESULTS, SCALE, cases
from scripts.factor import verify_file


THEOREM = 'PrimeFactors.Generated.ManyCharacterReceipt.checked'
OUTPUT = Path(__file__).resolve().parents[1] / 'build/many-character-windows'


def vector(name, values, element_type):
    if len(values) != COUNT:
        raise ValueError(f'expected {COUNT} values for {name}')
    entries = ',\n  '.join(str(int(value)) for value in values)
    return f'private abbrev {name} : Fin {COUNT} → {element_type} := ![\n  {entries}]'


def render(case, row):
    n = int(case['n'])
    bits = int(case['factor_bits'])
    if row['id'] != case['id'] or int(row['n']) != n or int(row['factor_bits']) != bits:
        raise ValueError('archived character data do not match the public control input')
    if row['wheel'] != 60 or row['wheel_lanes'] != 16:
        raise ValueError('the finite-interval proof uses the sixteen unit classes modulo 60')
    h = int(row['max_modulus_bits'])
    t = int(row['t'])
    c1, c2 = int(row['c1']), int(row['c2'])
    cap = int(row['certified_parts_per_million'])
    if cap != row['ppm_by_t'][t]:
        raise ValueError('the archived rate does not match its selected shift')
    lines = [
        'import PrimeFactors.CharacterWindowRate',
        'namespace PrimeFactors.Generated.ManyCharacterReceipt',
        'open Finset TwoCharacterWindow CharacterWindowRate',
        'set_option maxRecDepth 32768',
        'set_option exponentiation.threshold 4096',
        f'private abbrev n : ℕ := {n}',
        f'private abbrev B : ℕ := 2^{bits}-1',
        f'private abbrev lo : ℕ := {int(row["lower"])}',
        f'private abbrev hi : ℕ := {int(row["upper"])}',
        f'private abbrev L : ℕ := {int(row["min_lane_length"])}',
        vector('D', row['moduli'], 'ℕ'),
        vector('A', row['negative_roots'], 'ℤ'),
        vector('R', row['radii'], 'ℕ'),
        'private theorem low : lower n B = lo := by decide +kernel',
        'private theorem high : n.sqrt = hi :=',
        '  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt\'.mpr (by decide +kernel)))',
        '    (Nat.le_sqrt\'.mpr (by decide +kernel))',
        'private theorem three : ∀ i, D i % 4 = 3 := by decide +kernel',
        'private theorem productUnits : ∀ i, n.Coprime (D i) := by decide +kernel',
        'private theorem norm : ∀ i, (n : ℤ) ∣ (A i)^2 + D i := by decide +kernel',
        'private theorem roots (i) : IsSquare (-(D i : ZMod n)) :=',
        '  ReciprocalDivisorClasses.square_of_witness (norm i)',
        'private theorem cop : Pairwise (fun i j => (D i).Coprime (D j)) := by',
        '  change ∀ i j, i ≠ j → (D i).Coprime (D j)',
        '  decide +kernel',
        f'private theorem radiusSum : (∑ i, (R i : ℤ)) = {int(row["radius_sum"])} := by',
        '  decide +kernel',
        f'private theorem radiusSqSum : (∑ i, (R i : ℤ)^2) = {int(row["radius_square_sum"])} := by',
        '  decide +kernel',
        'theorem checked :',
        f'    positions (lower n B) n.sqrt = {int(row["wheel_positions"])} ∧',
        '    (∀ p q : ℕ, n = p*q → 0 < p → p ≤ q → q ≤ B →',
        '      ∃ w∈wheel, ∃ j∈CharacterWindowMoment.hits D (rowStart (lower n B) w) 60',
        '        (rowLength (lower n B) n.sqrt w), p = rowStart (lower n B) w + 60*j) ∧',
        f'    (PublishedPV → {SCALE}*passes D (lower n B) n.sqrt ≤',
        f'      {cap}*positions (lower n B) n.sqrt) := by',
        '  refine ⟨?_,?_,?_⟩',
        '  · rw [low, high]',
        '    decide +kernel',
        '  · intro p q eq positive ordered bounded',
        '    have pdiv : p ∣ n := eq ▸ dvd_mul_right p q',
        '    have unit := (show n.Coprime 60 by decide +kernel).of_dvd_left pdiv',
        '    have odd := Nat.coprime_two_right.mp (unit.of_dvd_right (by decide : 2 ∣ 60))',
        '    exact factors_located D eq positive ordered bounded unit odd three productUnits roots',
        '  · intro pv',
        '    rw [low, high]',
        f'    apply window D R lo hi L {t} {h} {c1} {c2} {SCALE} {cap} pv',
        '      (by decide +kernel) three cop (by decide +kernel) (by decide +kernel)',
        '      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
        '      (by decide +kernel) (by decide +kernel)',
        '    rw [radiusSum, radiusSqSum]',
        '    decide +kernel',
        '#print axioms checked',
        'end PrimeFactors.Generated.ManyCharacterReceipt',
    ]
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='write Lean files under build/ and check them')
    args = parser.parse_args()
    public_cases = cases()
    records = json.loads(RESULTS.read_text())
    indexed = {row['id']: row for row in records}
    if len(public_cases) != 2 or len(records) != 2 or set(indexed) != {c['id'] for c in public_cases}:
        raise ValueError('expected exactly the two existing 2048-bit control inputs')
    if args.verify:
        OUTPUT.mkdir(parents=True, exist_ok=True)
    for case in public_cases:
        row = indexed[case['id']]
        source = render(case, row)
        if args.verify:
            path = OUTPUT / (case['id'] + '.lean')
            path.write_text(source)
            verify_file(path, THEOREM)
        status = 'Lean checked' if args.verify else 'archived'
        print(f'{case["id"]}: {row["certified_parts_per_million"]}/{SCALE} under PublishedPV ({status})',
              flush=True)


if __name__ == '__main__':
    main()
