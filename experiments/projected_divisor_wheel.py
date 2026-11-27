"""Project continued-fraction square classes onto signs at five small primes."""

from bisect import bisect_left
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, isqrt, prod

from experiments.mixed_ratio_heights import jacobi
from experiments.pell_pairs import convergents
from experiments.pell_relations import _coprime_base, _private_parts, insert_parity

BASE = (-1, 2, 3, 5, 7, 11)
PERIOD = 4 * prod(BASE[1:])


@dataclass
class Row:
    step: int
    value: int
    root: int
    small: int
    residual: int


def split_support(value):
    parity = int(value < 0)
    residual = abs(value)
    for bit, prime in enumerate(BASE[1:], 1):
        while residual % prime == 0:
            residual //= prime
            parity ^= 1 << bit
    return parity, residual


def projected_root(n, rows, indices, mask):
    selected = [row for i, row in enumerate(rows) if indices >> i & 1]
    delta = prod(p for i, p in enumerate(BASE) if mask >> i & 1)
    quotient, remainder = divmod(prod(row.value for row in selected), delta)
    if remainder or quotient < 1:
        raise ArithmeticError('incorrect projected square class')
    scale = isqrt(quotient)
    if scale**2 != quotient:
        raise ArithmeticError('large cofactors did not cancel')
    root = prod(row.root for row in selected) * pow(scale, -1, n) % n
    if (root*root - delta) % n:
        raise ArithmeticError('incorrect projected root')
    return dict(mask=mask, discriminant=delta, root=str(root), steps=[row.step for row in selected])


def project(n, limit):
    """Return all independent small square classes obtainable from this public prefix."""
    if n <= 1 or gcd(PERIOD, n) != 1 or isqrt(n)**2 == n or limit < 0:
        raise ValueError('expected a nonsquare n > 1 coprime to the wheel and a nonnegative budget')
    rows = []
    factor = None
    step = 0
    for step, absolute, sign, root, center in convergents(n, 4, limit):
        value = sign * absolute
        if (root*root - value) % n:
            raise ArithmeticError('incorrect continued-fraction norm')
        common = gcd(absolute, n)
        if 1 < common < n:
            factor = common
            break
        if common == 1:
            small, residual = split_support(value)
            rows.append(Row(step, value, root, small, residual))
        if absolute == 1 or center:
            break

    original_count = len(rows)
    direct_basis = {}
    for row in rows:
        if isqrt(row.residual)**2 == row.residual:
            insert_parity(direct_basis, row.small, 0)

    # A private nonsquare forbids this row in every combination with square cofactor.
    while rows:
        private = _private_parts([r.residual for r in rows])
        kept = [r for r, u in zip(rows, private) if isqrt(u)**2 == u]
        if len(kept) == len(rows):
            break
        rows = kept
    pieces = _coprime_base([row.residual for row in rows])
    nonsquare = [isqrt(base)**2 != base for base in pieces]
    large_basis, small_basis = {}, {}
    constraints = []
    smooth_dimension = square_dimension = 0
    for i, row in enumerate(rows):
        residual = row.residual
        large = 0
        for bit, base in enumerate(pieces):
            odd = False
            while residual % base == 0:
                residual //= base
                odd = not odd
            if odd and nonsquare[bit]:
                large |= 1 << bit
        if residual != 1:
            raise ArithmeticError('coprime basis missed a cofactor')
        indices = insert_parity(large_basis, large, 1 << i)
        if indices is None:
            continue
        smooth_dimension += 1
        small = 0
        for j, other in enumerate(rows):
            if indices >> j & 1:
                small ^= other.small
        dependency = insert_parity(small_basis, small, indices)
        if dependency is None:
            constraints.append(projected_root(n, rows, indices, small))
        else:
            square_dimension += 1
            root = int(projected_root(n, rows, dependency, 0)['root'])
            common = gcd(root - 1, n)
            if 1 < common < n and factor is None:
                factor = common
    return dict(steps=step, input_rows=original_count, private_pruned=original_count-len(rows),
                direct_rank=len(direct_basis), projected_rank=len(small_basis),
                smooth_dimension=smooth_dimension, square_dimension=square_dimension,
                constraints=constraints, setup_factor=str(factor) if factor else None)


@lru_cache(maxsize=1)
def wheel():
    """The sign vector of every unit of the small wheel, reusable across products."""
    return [(r, sum(1 << i for i, p in enumerate(BASE) if jacobi(p, r) == -1))
            for r in range(1, PERIOD, 2) if gcd(r, PERIOD) == 1]


def allowed(constraints):
    masks = [entry['mask'] for entry in constraints]
    rows = [r for r, signs in wheel() if all(bin(signs & m).count('1') % 2 == 0 for m in masks)]
    if len(rows) * (1 << len(masks)) != len(wheel()):
        raise ArithmeticError('projected rank disagrees with the enumerated unit count')
    return rows


def search(n, bits, residues, division_limit):
    """Stream only the sorted residues; the inputs promise two primes of this width."""
    bound = 2**bits - 1
    low = max(2**(bits-1), (n-1)//bound + 1)
    high = isqrt(n)
    first, offset = divmod(low, PERIOD)
    index = bisect_left(residues, offset)
    divisions = 0
    for block in range(first, high//PERIOD + 1):
        for j in range(index, len(residues)):
            candidate = block*PERIOD + residues[j]
            if candidate > high or divisions == division_limit:
                return None, divisions
            divisions += 1
            if n % candidate == 0:
                return candidate, divisions
        index = 0
    return None, divisions


def run(n, bits, steps, division_limit):
    if bits < 2 or division_limit < 0:
        raise ValueError('invalid width or division budget')
    work = project(n, steps)
    residues = allowed(work['constraints'])
    factor = work['setup_factor']
    divisions = 0
    if not factor:
        factor, divisions = search(n, bits, residues, division_limit)
    return dict(work, unit_rows=len(wheel()), allowed_rows=len(residues), divisions=divisions,
                step_limit=steps, division_limit=division_limit, factor=str(factor) if factor else None)
