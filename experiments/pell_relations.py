"""Check all square dependencies in a bounded block of continued-fraction norms."""

from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt, prod

if __package__:
    from .pell_pairs import convergents
else:
    from pell_pairs import convergents


def _private_parts(values, external=1):
    """Remove all primes shared with other entries or the external support."""
    if not values:
        return []
    levels = [values]
    while len(levels[-1]) > 1:
        row = levels[-1]
        levels.append([prod(row[i:i + 2]) for i in range(0, len(row), 2)])
    # The remainder at a leaf v is (product of all entries) modulo v².
    remainders = [levels[-1][0] * external]
    for level in reversed(levels[:-1]):
        remainders = [remainders[i // 2] % (v * v) for i, v in enumerate(level)]
    private = []
    for value, remainder in zip(values, remainders):
        shared = gcd(value, remainder // value)
        while shared != 1:
            value //= shared
            shared = gcd(value, shared)
        private.append(value)
    return private


def _coprime_base(values):
    """Split overlapping distinct bases until every pair is coprime."""
    bases = {v for v in values if v > 1}
    while True:
        ordered = sorted(bases)
        for i, u in enumerate(ordered):
            for v in ordered[i + 1:]:
                g = gcd(u, v)
                if g != 1:
                    bases.difference_update((u, v))
                    bases.update(w for w in (g, u // g, v // g) if w > 1)
                    break
            else:
                continue
            break
        else:
            return ordered


def _dependencies(norms):
    """A basis for the subsets whose signed product is an integer square."""
    base = _coprime_base([abs(q) for q in norms])
    pivots = {}
    dependencies = []
    for i, q in enumerate(norms):
        parity, value = int(q < 0), abs(q)
        for j, b in enumerate(base, start=1):
            exp = 0
            while value % b == 0:
                value //= b
                exp += 1
            if exp % 2 and isqrt(b)**2 != b:
                parity |= 1 << j
        if value != 1:
            raise ArithmeticError('gcd refinement lost a factor')
        subset = 1 << i
        while parity:
            bit = parity.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = (parity, subset)
                break
            row, indices = pivots[bit]
            parity ^= row
            subset ^= indices
        else:
            dependencies.append(subset)
    return dependencies


def search(n, multiplier, max_steps, *, use_gmp=False, external=1):
    """Generate a bounded prefix and try every independent square relation."""
    if n <= 1 or multiplier < 1 or max_steps < 0 or external < 1:
        raise ValueError('expected n > 1, positive multiplier and external support, nonnegative step budget')
    if use_gmp:
        from gmpy2 import mpz as tree_integer
    else:
        tree_integer = int
    work = dict(factor=None, outcome='no_split', steps=0, center=False, rows=0,
                private_pruned=0, pruning_rounds=0, min_private_bits=None,
                dependencies=0, tested=0, selected_steps=[])
    rows = []
    for step, denominator, sign, numerator, symmetric in convergents(n, multiplier, max_steps):
        norm = sign * denominator
        if (numerator * numerator - norm) % n:
            raise ArithmeticError('incorrect signed convergent norm')
        work['steps'] = step
        work['center'] = symmetric
        divisor = gcd(denominator, n)
        if 1 < divisor < n:
            return dict(work, outcome='denominator', factor=divisor, rows=len(rows))
        if divisor == 1:
            rows.append((step, norm, numerator))
        if denominator == 1 or work['center']:
            break
    work['rows'] = len(rows)
    # A nonsquare supported on primes private to one row forbids that row
    # in every dependency. Removing it can expose new private cofactors.
    while rows:
        private = _private_parts([tree_integer(abs(q)) for _, q, _ in rows], external)
        kept = []
        for row, part in zip(rows, private):
            if isqrt(part)**2 == part:
                kept.append(row)
            else:
                bits = part.bit_length()
                if work['min_private_bits'] is None or bits < work['min_private_bits']:
                    work['min_private_bits'] = bits
        if len(kept) == len(rows):
            break
        work['pruning_rounds'] += 1
        work['private_pruned'] += len(rows) - len(kept)
        rows = kept
    basis = _dependencies([q for _, q, _ in rows])
    work['dependencies'] = len(basis)
    for mask in basis:
        chosen = [row for i, row in enumerate(rows) if mask >> i & 1]
        square = prod(q for _, q, _ in chosen)
        root = isqrt(square)
        if root * root != square:
            raise ArithmeticError('parity dependency produced a nonsquare')
        numerator = 1
        for _, _, residue in chosen:
            numerator = numerator * residue % n
        divisor = gcd(numerator - root, n)
        work['tested'] += 1
        if 1 < divisor < n:
            return dict(work, outcome='relation', factor=divisor,
                        selected_steps=[step for step, _, _ in chosen])
    return work


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--multiplier', type=int, default=1)
    parser.add_argument('--max-steps', type=int, default=64)
    parser.add_argument('--gmp', action='store_true', help='use optional gmpy2 for the product tree')
    parser.add_argument('--external-smooth', type=int, metavar='B',
                        help='strengthen private-row exclusions against primes up to B (requires --gmp)')
    args = parser.parse_args()
    external = 1
    if args.external_smooth is not None:
        if not args.gmp or args.external_smooth < 1:
            parser.error('--external-smooth requires --gmp and a positive bound')
        from gmpy2 import primorial
        external = primorial(args.external_smooth)
    print(dumps(search(args.n, args.multiplier, args.max_steps, use_gmp=args.gmp, external=external)))
