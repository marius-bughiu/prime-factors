"""Read the first differing factor bit via disjoint public divisor intervals."""

import argparse
import json
from math import gcd, isqrt
from pathlib import Path

if __package__:
    from .short_pascal_row import interval
else:
    from short_pascal_row import interval

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "benchmarks" / "dyadic-factor-bands.json"


def cut(n, root, j):
    width = 1 << j
    lower = (root >> j) << j
    return max(lower, n // (lower + width) + 1)


def search(n, max_positions, wheel=30):
    """Use only n and public budgets. The width promise is for the two factors."""
    if max_positions < 0 or wheel < 1:
        raise ValueError("expected a nonnegative span and a positive wheel")
    low, root = interval(n)
    if low > root:
        return dict(factors=[], remaining=[str(n)], rows=[], examined=0, modular_multiplications=0)
    common = gcd(wheel, n)
    if common != 1:
        raise ValueError("the wheel and the input must be coprime")
    width = (n.bit_length() + 1) // 2
    residues = [r for r in range(wheel) if gcd(r, wheel) == 1]
    previous = max(low, cut(n, root, width - 1))
    rows = []
    spent = products = 0
    factor = None
    for j in range(width - 2, 0, -1):
        end = min(root + 1, max(low, cut(n, root, j)))
        stop = min(end, previous + max_positions - spent)
        residue = 1
        multiplies = 0
        if previous < stop:
            for r in residues:
                first = previous + (r - previous) % wheel
                for candidate in range(first, stop, wheel):
                    residue = (residue * candidate) % n
                    multiplies += 1
        divisor = gcd(n, residue)
        paid = stop - previous
        spent += paid
        products += multiplies
        complete = stop == end
        if 1 < divisor < n:
            factor = divisor
            reading = str(divisor)
        elif complete:
            reading = str(n if (root >> j) & 1 else 1)
        else:
            reading = None
        rows.append(dict(index=j, positions=str(end - previous), examined=paid,
                         modular_multiplications=multiplies, mask_gcd=reading))
        if factor is not None or not complete:
            break
        previous = end
    return dict(factors=sorted([str(factor), str(n // factor)], key=int) if factor else [],
                remaining=[] if factor else [str(n)], rows=rows, examined=spent,
                modular_multiplications=products)


def fixtures():
    references = {x['id']: x for x in json.loads((ROOT / 'benchmarks' / 'dyadic-totative-masks.json').read_text())}
    results = []
    for case in json.loads(FIXTURES.read_text()):
        n = int(case['n'])
        result = search(n, case['max_positions'])
        if result['factors'] != case['factors'] or result['remaining'] != case['remaining']:
            raise AssertionError(case['id'])
        for key, expected in case['checks'].items():
            if result[key] != expected:
                raise AssertionError((case['id'], key, result[key], expected))
        if 'reference' in case:
            original = references[case['reference']]['checks']['rows']
            if [(r['index'], r['mask_gcd']) for r in result['rows']] != [(r['index'], r['gcd']) for r in original]:
                raise AssertionError((case['id'], 'original coefficient gcd mismatch'))
        results.append(dict(id=case['id'], **result))
    return results


def fresh_proof(path, n):
    """Reuse the existing independently generated prime certificates for the fixed control."""
    original = (ROOT / 'benchmarks' / 'controls' / 'PocklingtonControl.lean').read_text()
    path.write_text('import PrimeFactors.DyadicFactorBands\n' + original + """
namespace PrimeFactors.Generated
open DyadicTotativeMasks

theorem fresh_first_mask :
    (coefficient (endpoint INPUT 1022)).gcd INPUT = INPUT := by
  rw [show INPUT = left1024*right1024 by decide +kernel]
  exact DyadicFactorBands.upper_quarter_mask left1024_prime right1024_prime
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

#print axioms fresh_first_mask
end PrimeFactors.Generated
""".replace("INPUT", str(n)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument('n', nargs='?', type=int)
    selection.add_argument('--fixtures', action='store_true')
    selection.add_argument('--fresh-proof', type=Path, metavar='FILE')
    parser.add_argument('--max-positions', type=int, default=4096)
    args = parser.parse_args()
    if args.fresh_proof:
        control = next(case for case in json.loads(FIXTURES.read_text()) if case.get("certify_first_mask"))
        fresh_proof(args.fresh_proof, int(control["n"]))
    else:
        print(json.dumps(fixtures() if args.fixtures else search(args.n, args.max_positions), indent=2))
