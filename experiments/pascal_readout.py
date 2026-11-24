"""Evaluate the public binomial formula at bounded indices, including its full coefficient size."""

from argparse import ArgumentParser
from json import dumps
from math import comb, isqrt

if __package__:
    from .predecessor_square import factor_from_sum
else:
    from predecessor_square import factor_from_sum


def search(n, cutoff, max_index):
    if n <= 1 or n % 2 == 0 or max_index < 0:
        raise ValueError('expected an odd product above one and a nonnegative index budget')
    if cutoff == 'sqrt':
        index = 2*((isqrt(n)-1)//2)+1
    elif cutoff == 'dyadic':
        factor_bits = (n.bit_length()+1)//2
        index = (1 << factor_bits)-1
    else:
        raise ValueError('expected sqrt or dyadic cutoff')
    result = dict(cutoff=cutoff, index=str(index), max_index=max_index, coefficients_evaluated=0,
                  coefficient_bits=None, residue=None, factor=None)
    if index > max_index:
        return result
    coefficient = comb(n-1, index)
    residue = coefficient % n
    if cutoff == 'sqrt':
        candidate = residue+1
        factor = candidate if 1 < candidate < n and n % candidate == 0 else None
    else:
        factor = factor_from_sum(n, residue+1)
    result.update(coefficients_evaluated=1, coefficient_bits=coefficient.bit_length(),
                  residue=str(residue), factor=factor)
    return result


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--cutoff', choices=['sqrt', 'dyadic'], default='sqrt')
    parser.add_argument('--max-index', type=int, default=65535)
    args = parser.parse_args()
    print(dumps(search(args.n, args.cutoff, args.max_index)))
