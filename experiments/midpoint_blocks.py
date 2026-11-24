"""Compute a masked Jacobi pass parity on a bounded block of consecutive midpoints.

Example: python3 experiments/midpoint_blocks.py 1900014700027 1378412 16 600600 --compare

This reference uses schoolbook polynomial construction, Horner evaluation per
row, and direct cyclic convolution of the odd histogram entries. Constructing a
degree-d slice costs O(d²) coefficient operations, evaluating it costs O(d) per
row, and a convolution can take O(p²) operations for a small prime p. The
paper uses fast polynomial multiplication and multipoint evaluation. The reported counters measure the work actually performed here.
"""

from argparse import ArgumentParser
from dataclasses import asdict, dataclass
from json import dumps
from math import gcd

if __package__:
    from .midpoint_readings import reading
else:
    from midpoint_readings import reading


@dataclass
class Work:
    selected_entries: int = 0
    trial_divisors: int = 0
    small_prime_histogram_updates: int = 0
    small_prime_convolution_pairs: int = 0
    small_prime_signs: int = 0
    slice_polynomials: int = 0
    coefficient_products: int = 0
    polynomial_evaluations: int = 0
    horner_steps: int = 0
    nonunit_blocks: int = 0
    exceptional_singletons: int = 0
    tail_readings: int = 0


def block_shape(length):
    if length < 1:
        raise ValueError('the block length must be positive')
    columns = 1 << (((length-1).bit_length()+1)//2)
    return (length+columns-1)//columns, columns


def selected_indices(mask, width):
    if mask is None:
        return list(range(width))
    if mask < 0 or mask.bit_length() > width:
        raise ValueError('mask has bits outside the block dimensions')
    return [i for i in range(width) if (mask >> i) & 1]


def small_prime_product(n, start, width, rows, cols, prime, work):
    """Combine parity histograms by schoolbook cyclic convolution modulo 2."""
    row_parities = [0]*prime
    col_parities = [0]*prime
    for row in rows:
        row_parities[row*width % prime] ^= 1
    for col in cols:
        col_parities[col % prime] ^= 1
    work.small_prime_histogram_updates += len(rows)+len(cols)
    odd_rows = [r for r in range(prime) if row_parities[r]]
    odd_cols = [c for c in range(prime) if col_parities[c]]
    freq = [0]*prime
    for r in odd_rows:
        for c in odd_cols:
            freq[(r+c) % prime] ^= 1
    work.small_prime_convolution_pairs += len(odd_rows)*len(odd_cols)
    sign = 1
    for offset, odd in enumerate(freq):
        if odd:
            residue = ((start+2*offset)**2-n) % prime
            sign *= reading(residue or prime, prime)
            work.small_prime_signs += 1
    return sign


def slice_polynomial(n, columns, modulus, work):
    """Multiply successive monic quadratics; coefficients are low degree first."""
    poly = [1]
    for col in columns:
        constant = (4*col*col-n) % modulus
        linear = 4*col % modulus
        product = [0]*(len(poly)+2)
        for j, value in enumerate(poly):
            product[j] += value*constant
            product[j+1] += value*linear
            product[j+2] += value
        work.coefficient_products += 2*len(poly)
        poly = [value % modulus for value in product]
    work.slice_polynomials += 1
    return poly


def residual_product(n, start, width, rows, cols, modulus, work):
    """Reuse each column-slice polynomial across all rows visiting that slice."""
    pending = [(0, width, rows, cols)]
    sign = 1
    while pending:
        left, right, active_rows, active_cols = pending.pop()
        if not active_cols or not active_rows:
            continue
        poly = slice_polynomial(n, active_cols, modulus, work)
        dirty_rows = []
        for row in active_rows:
            row_start = start+2*row*width
            value = poly[-1]
            for coefficient in reversed(poly[:-1]):
                value = (value*row_start+coefficient) % modulus
            work.polynomial_evaluations += 1
            work.horner_steps += len(poly)-1
            if gcd(value, modulus) == 1:
                sign *= reading(value, modulus)
            else:
                work.nonunit_blocks += 1
                if right-left == 1:
                    sign *= reading((row_start+2*left)**2-n, modulus)
                    work.exceptional_singletons += 1
                else:
                    dirty_rows.append(row)
        if dirty_rows:
            middle = (left+right)//2
            pending.append((left, middle, dirty_rows, [c for c in active_cols if c < middle]))
            pending.append((middle, right, dirty_rows, [c for c in active_cols if c >= middle]))
    return sign


def masked_reading(n, start, length, seed, row_mask=None, column_mask=None):
    """Return the exact product of selected signs and parity of their +1 entries.

    Bit i selects row/column i. An omitted mask selects all rows/columns.
    Positions past the end of a partially filled row contribute zero pass bits.
    """
    height, width = block_shape(length)
    if n < 1 or seed < 1 or start < 1 or start*start <= n:
        raise ValueError('expected a positive product, seed and first discriminant')
    rows = selected_indices(row_mask, height)
    cols = selected_indices(column_mask, width)
    full_rows, tail = divmod(length, width)
    tail_cols = [c for c in cols if c < tail] if full_rows in rows else []
    rows = [r for r in rows if r < full_rows]
    work = Work(selected_entries=len(rows)*len(cols)+len(tail_cols))
    sign = 1
    remaining = seed
    if rows and cols:
        for divisor in range(2, max(2, width)+1):
            if remaining == 1:
                break
            work.trial_divisors += 1
            exponent = 0
            while remaining % divisor == 0:
                remaining //= divisor
                exponent += 1
            if divisor != 2 and exponent % 2:
                sign *= small_prime_product(n, start, width, rows, cols, divisor, work)
        if remaining > 1:
            sign *= residual_product(n, start, width, rows, cols, remaining, work)
    for col in tail_cols:
        position = full_rows*width+col
        sign *= reading((start+2*position)**2-n, seed)
        work.tail_readings += 1
    return dict(sign_product=sign, pass_parity=(work.selected_entries+int(sign < 0)) % 2,
                rows=height, columns=width, work=asdict(work))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    for name in ('n', 'start', 'length', 'seed'):
        parser.add_argument(name, type=int)
    parser.add_argument('--rows', type=lambda s: int(s, 0), help='row bit mask, e.g. 0x3')
    parser.add_argument('--columns', type=lambda s: int(s, 0), help='column bit mask')
    parser.add_argument('--compare', action='store_true', help='also check each selected position')
    args = parser.parse_args()
    result = masked_reading(args.n, args.start, args.length, args.seed, args.rows, args.columns)
    if args.compare:
        active_rows = selected_indices(args.rows, result['rows'])
        active_cols = selected_indices(args.columns, result['columns'])
        passes = 0
        for row in active_rows:
            for col in active_cols:
                j = row*result['columns']+col
                if j < args.length:
                    passes += reading((args.start+2*j)**2-args.n, args.seed) == 1
        if passes % 2 != result['pass_parity']:
            raise AssertionError('masked and direct pass parities disagree')
        result['direct_passes'] = passes
    print(dumps(result))
