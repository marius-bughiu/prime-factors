"""Read a prime from low bits of two complete Jacobi sums.

The guaranteed lattice readout assumes distinct primes 1 mod 4 and a modulus
larger than the selected prime. For balanced factors sqrt(2N) is an upper
bound. All discovery inputs are public. A truncated sum never enters the
decoder.
"""
from collections import Counter
from math import gcd, isqrt

from .mixed_ratio_heights import jacobi
from .short_basis_sieve import shortest_lattice_vector


def decode(n, bits, first, twisted):
    """Accept just the two residues modulo 2^(bits+2) and verify the output."""
    modulus = 1 << bits
    if first % 8 != 4 or twisted % 4:
        return None, None, 0
    slope = (twisted // 4) * pow(first // 4, -1, modulus) % modulus
    work = Counter()
    x, y = shortest_lattice_vector(modulus, slope, lambda v: v, work)
    norm = x*x + y*y
    factor = norm if 1 < norm < n and n % norm == 0 else None
    return factor, [x, y], work['gauss_iterations']


def search(n, max_positions, max_selector, bits=None):
    if n < 3 or n % 2 == 0 or max_positions < 0 or max_selector < 1:
        raise ValueError('expected odd N >= 3, nonnegative position budget and positive selector limit')
    if bits is None:
        bits = isqrt(2*n).bit_length()
    if bits < 1:
        raise ValueError('precision must be positive')
    result = dict(factor=None, selector=None, selector_tests=0, positions=0,
                  required_positions=str(n//2), symbol_evaluations=0, bits=bits,
                  residues=None, vector=None, gauss_iterations=0)
    if n % 4 == 3:
        return dict(result, outcome='cancellation')
    for d in range(2, max_selector+1):
        result['selector_tests'] += 1
        symbol = jacobi(d, n)
        if symbol == -1:
            result['selector'] = d
            break
        if symbol == 0:
            factor = gcd(d, n)
            if factor < n:
                return dict(result, factor=factor, outcome='selector_divisor')
    else:
        return dict(result, outcome='selector_limit')

    # For N = 1 mod 4 the terms at x and -x agree. Keep only the low bits
    # throughout, including when evaluating the very last pair of terms.
    mask = (1 << (bits+2)) - 1
    first = twisted = 0
    positions = min(n//2, max_positions)
    for x in range(1, positions+1):
        square = x*x % n
        first = (first + 2*jacobi(x*(square-1), n)) & mask
        twisted = (twisted + 2*jacobi(x*(square-d), n)) & mask
    result.update(positions=positions, symbol_evaluations=2*positions)
    if positions < n//2:
        return dict(result, outcome='position_limit')
    factor, vector, iterations = decode(n, bits, first, twisted)
    return dict(result, factor=factor, vector=vector, gauss_iterations=iterations,
                residues=[first, twisted], outcome='trace_divisor' if factor else 'no_split')
