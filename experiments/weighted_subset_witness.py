"""Generate Lean certificates for the public eight-weight, two-rank square menu.

Run python3 -m experiments.weighted_subset_witness --check to regenerate and
kernel-check the four archived exclusion and uniqueness certificates.
"""

import argparse
import json
import re
from math import isqrt, prod
from pathlib import Path

from experiments.weighted_square_pairs import first_label
from scripts.factor import primes_through, verify_file


ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {
    'weighted-square-triples-fresh-2048': 'WeightedSubsetFresh',
    'weighted-square-triples-crossed-2048': 'WeightedSubsetCrossed',
    'weighted-square-subsets-2222417': 'WeightedSubsetFour',
    'weighted-square-subsets-8928473': 'WeightedSubsetFive',
}


def _rows(n):
    ceilings = []
    excesses = []
    for weight in range(1, 9):
        radicand = 4 * weight * n
        ceilings.append(isqrt(radicand - 1) + 1)
        label, stride = first_label(n, weight)
        excesses.extend((label + rank * stride) ** 2 - radicand for rank in range(2))
    return ceilings, excesses


def _signatures(excesses, prime_limit, omitted=None):
    """Row-reduce sign masks over F₂, retaining the primes that realize each sum."""
    count = len(excesses)
    columns = [i for i in range(count) if i != omitted]
    basis = {}
    tested = 0
    skipped = 0
    symbols = 0
    for prime in primes_through(prime_limit):
        if prime == 2:
            continue
        tested += 1
        if any(value % prime == 0 for value in excesses):
            skipped += 1
            continue
        mask = sum((pow(value, (prime - 1) // 2, prime) == prime - 1) << i
                   for i, value in enumerate(excesses))
        symbols += count
        support = {prime}
        for i in columns:
            if not mask & (1 << i):
                continue
            if i not in basis:
                basis[i] = mask, support
                break
            other, other_support = basis[i]
            mask ^= other
            support ^= other_support
        if len(basis) == len(columns):
            break
    if len(basis) != len(columns):
        raise ValueError(f'only {len(basis)} independent signatures for {len(columns)} columns '
                         f'through prime {prime_limit}')
    for i in reversed(columns):
        mask, support = basis[i]
        for j in columns:
            if j > i and mask & (1 << j):
                other, other_support = basis[j]
                mask ^= other
                support ^= other_support
        basis[i] = mask, support
    moduli = [sorted(basis[i][1]) if i in basis else [] for i in range(count)]
    stats = dict(rank=len(basis), last_prime=prime, prime_candidates=tested, skipped_nonunits=skipped,
                 euler_readings=symbols, largest_modulus_bits=max(prod(row).bit_length() for row in moduli))
    return moduli, stats


def certificate(n, namespace, prime_limit=997, *, allow_pivot=False):
    """Construct a standalone Lean source from N and a safe descriptive namespace."""
    if n < 2 or prime_limit < 3:
        raise ValueError('expected a positive composite-sized input and an odd-prime budget')
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', namespace):
        raise ValueError('expected a capitalized, unqualified Lean namespace')
    ceilings, excesses = _rows(n)
    # For the rank-fifteen examples, preassign the weight-one, rank-zero row
    # as pivot. The other fifteen signatures determine its sole possible relation.
    pivot = 0 if allow_pivot else None
    signatures, stats = _signatures(excesses, prime_limit, omitted=pivot)
    ceiling_array = ',\n  '.join(map(str, ceilings))
    pairs = [f'![{signatures[i]}, {signatures[i + 1]}]' for i in range(0, len(signatures), 2)]
    signature_array = ',\n  '.join(pairs)
    source = f'''import PrimeFactors.WeightedSubsetWitness

/-! Reproduce with python3 -m experiments.weighted_subset_witness --check. -/
namespace PrimeFactors.{namespace}
open WeightedSubsetWitness

def product : ℕ := {n}

private noncomputable def ceiling : Fin 8 → ℕ := ![
  {ceiling_array}]

private noncomputable def probes : Fin 8 → Fin 2 → List ℕ := ![
  {signature_array}]

'''
    if pivot is None:
        source += '''/-- Every nonempty subset of the sixteen public remainders has nonsquare product. -/
theorem noSquareSubset (S : Finset Id) (nonempty : S.Nonempty) (z : ℕ) :
    (∏ i∈S, excess product i) ≠ z^2 :=
  certify product ceiling probes (by decide +kernel) (by decide +kernel)
    (by decide +kernel) S nonempty z

#print axioms noSquareSubset
'''
    else:
        support = [pivot]
        for i, primes in enumerate(signatures):
            negatives = sum(pow(excesses[pivot], (p - 1) // 2, p) == p - 1 for p in primes)
            if i != pivot and negatives % 2:
                support.append(i)
        square = prod(excesses[i] for i in support)
        root = isqrt(square)
        if root * root != square:
            raise ValueError('the only possible nonempty support has a nonsquare product')
        stats['pivot_verification_readings'] = sum(map(len, signatures))
        stats['mask'] = sum(1 << i for i in support)
        stats['square_root'] = str(root)
        rows = ', '.join(f'({i // 2},{i % 2})' for i in support)
        source += f'''/-- Coordinates are zero-based for both the weight index and the rank. -/
def uniqueRows : Finset Id := {{{rows}}}

/-- Exactly one nonempty subset of the sixteen public remainders has square product. -/
theorem onlySquareSubset (S : Finset Id) (nonempty : S.Nonempty) :
    (∃ y : ℕ, (∏ i∈S, excess product i)=y^2) ↔ S=uniqueRows :=
  certify_unique product ceiling probes (0,0) uniqueRows {root} (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S nonempty

#print axioms onlySquareSubset
'''
    source += f'end PrimeFactors.{namespace}\n'
    return source, stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true', help='write the four deterministic certificates')
    mode.add_argument('--check', action='store_true', help='compare the sources and replay all four in Lean')
    args = parser.parse_args()
    cases = json.loads((ROOT / 'benchmarks/weighted-square-triples.json').read_text())
    cases += json.loads((ROOT / 'benchmarks/weighted-square-subsets.json').read_text())
    controls = {row['id']: int(row['n']) for row in cases if row['id'] in CONTROLS}
    for name, namespace in CONTROLS.items():
        unique = name.startswith('weighted-square-subsets-')
        source, stats = certificate(controls[name], namespace, allow_pivot=unique)
        path = ROOT / 'benchmarks/controls' / f'{namespace}.lean'
        if args.write:
            path.write_text(source)
        if args.check:
            if path.read_text() != source:
                raise SystemExit(f'generated certificate differs from {path.name}')
            theorem = 'onlySquareSubset' if unique else 'noSquareSubset'
            verify_file(path, f'PrimeFactors.{namespace}.{theorem}')
        print(name, json.dumps(stats, sort_keys=True))


if __name__ == '__main__':
    main()
