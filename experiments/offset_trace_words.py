"""Sieve bounded offset charts with periodic bit masks from normalized factor sums."""

import argparse
import json
from math import gcd, isqrt

from experiments.offset_winner_window import bounds, coordinate_range
from scripts.factor import primes_through


def index_masks(n, t, primes, work):
    """For each nonzero multiplier residue, mark the allowed j=2i modulo p."""
    masks = {}
    for p in primes:
        sums = {(u+n*pow(u, -1, p)) % p for u in range(1, p)}
        work['unit_inverses'] += p-1
        half = (p+1)//2
        for k in range(1, p):
            # Scaling and translation are permutations, so each bit is added exactly once.
            masks[p, k] = sum(1 << ((k*(r-2*t)*half) % p) for r in sums)
            work['mask_entries'] += len(sums)
    return masks


def repeated_mask(base, p, first, width):
    """Bit i tests j=first+2i, using the stored mask for j=2i."""
    block = (1 << p)-1
    rotation = first*((p+1)//2) % p
    rotated = ((base | (base << p)) >> rotation) & block
    copies = (width+p-1)//p
    return rotated*(((1 << (copies*p))-1)//block)


def search(n, *, prime_limit=97, max_word_bits=4096, max_pairs=10000):
    """Scan a same-width balanced semiprime, with caps on word size and raw coordinate pairs.

    The width guard runs before mask setup and before constructing any bit words.
    The padded words have at most max_word_bits+prime_limit-1 bits, and the
    two-period rotation temporarily uses at most 2*prime_limit bits.
    """
    if n < 5 or n % 2 == 0 or min(max_pairs, prime_limit) < 0 or max_word_bits < max(1, prime_limit):
        raise ValueError('expected odd n >= 5, nonnegative caps, and a bit cap covering the prime limit')
    box = bounds(n)
    t, h, jmax, kmax, lower = (box[k] for k in ('T', 'h', 'J', 'K', 'L'))
    radius = isqrt(kmax)
    upper = (max(0, t-lower)*(kmax+radius)+4*lower*radius)//(2*lower)
    work = dict(prime_limit=prime_limit, max_word_bits=max_word_bits, max_pairs=max_pairs,
                word_bits_required=(jmax+1)//2, coordinate_upper=upper, unvisited_upper=upper,
                raw_pairs=0, charts=0, parity_positions=0, prime_tests=0, unit_inverses=0,
                mask_entries=0, word_intersections=0, residue_survivors=0, square_tests=0,
                proper_hits=0, first_hit=None, factor=None, exhaustive=False, outcome='word_cap')
    if not h:
        work.update(factor=t, unvisited_upper=0, exhaustive=True, outcome='square')
        return work
    if work['word_bits_required'] > max_word_bits:
        return work
    # The advertised factor promise implies lower <= p <= T.
    if lower > t:
        work.update(unvisited_upper=0, exhaustive=True, outcome='empty_width_interval')
        return work
    if max_pairs == 0:
        work['outcome'] = 'pair_cap'
        return work
    primes = [p for p in primes_through(prime_limit) if p >= 5]
    for p in primes:
        work['prime_tests'] += 1
        if n % p == 0 and p < n:
            work.update(factor=p, outcome='setup_split')
            return work
    masks = index_masks(n, t, primes, work)
    for v in range(1, radius+1):
        for s in coordinate_range(t, lower, kmax, v):
            if work['raw_pairs'] == max_pairs:
                work.update(outcome='pair_cap', unvisited_upper=upper-work['raw_pairs'])
                return work
            work['raw_pairs'] += 1
            if gcd(s, v) != 1:
                continue
            k = s*v
            first = max(1, isqrt(4*n*k*k-1)+1-2*t*k)
            first += (s+v-first) % 2
            width = max(0, (jmax-first)//2+1)
            bits = (1 << width)-1
            work['charts'] += 1
            work['parity_positions'] += width
            for p in primes:
                if not bits:
                    break
                if k % p:
                    bits &= repeated_mask(masks[p, k % p], p, first, width)
                    work['word_intersections'] += 1
            while bits:
                one = bits & -bits
                bits -= one
                j = first+2*(one.bit_length()-1)
                work['residue_survivors'] += 1
                if gcd(j, k) != 1:
                    continue
                work['square_tests'] += 1
                trace = j+2*t*k
                delta = trace*trace-4*n*k*k
                gap = isqrt(delta)
                if gap*gap != delta:
                    continue
                for signed in {gap, -gap}:
                    p, rem = divmod(trace+signed, 2*s*s)
                    q, other = divmod(trace-signed, 2*v*v)
                    if rem == other == 0 and 1 < p < q and p*q == n:
                        work['proper_hits'] += 1
                        if work['factor'] is None:
                            work.update(factor=p, first_hit=[j, k, s, v])
    work.update(exhaustive=True, unvisited_upper=0, outcome='exhausted')
    return work


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--prime-limit', type=int, default=97)
    parser.add_argument('--max-word-bits', type=int, default=4096)
    parser.add_argument('--max-pairs', type=int, default=10000)
    print(json.dumps(search(**vars(parser.parse_args())), indent=2))
