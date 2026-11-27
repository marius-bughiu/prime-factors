"""Reproduce fixed-budget comparisons on a complete small population and larger samples."""
from argparse import ArgumentParser
from bisect import bisect_left
from itertools import combinations
import json
from random import Random
from time import perf_counter

from experiments.twelve_residue_collision import search
from scripts.factor import primes_through


def run(bits, draws, sample):
    if bits < 2 or draws < 0 or sample < 0:
        raise ValueError('prime width must be at least two and budgets nonnegative')
    rng = Random(86412)
    primes = [p for p in primes_through((1 << bits)-1) if p.bit_length() == bits]
    if sample:
        lower_product = 1 << (2*bits-1)
        eligible = sum(len(primes) - bisect_left(primes, (lower_product+p-1)//p, lo=i+1)
                       for i, p in enumerate(primes))
        if sample > eligible:
            raise ValueError(f'only {eligible} distinct eligible prime pairs exist')
        choices = set()
        while len(choices) < sample:
            p, q = sorted(rng.sample(primes, 2))
            if (p*q).bit_length() == 2*bits:
                choices.add((p, q))
        pairs = sorted(choices)
    else:
        pairs = ((p,q) for p,q in combinations(primes,2) if (p*q).bit_length()==2*bits)
    counts = {mode: dict(splits=0, setup=0, pair=0, shared_key=0, seconds=0.0)
              for mode in ('twelve','matched','raw','power')}
    total = added = lost = 0
    for p, q in pairs:
        n = p*q
        seed = rng.randrange(1 << 63)
        found = {}
        for mode, totals in counts.items():
            start = perf_counter()
            factor, work, _ = search(n, draws, seed, mode)
            totals['seconds'] += perf_counter()-start
            if factor is not None:
                assert factor in (p,q)
                totals['splits'] += 1
                totals[{'regularity check':'setup', 'pair':'pair', 'shared key':'shared_key'}[work['source']]] += 1
            found[mode] = factor is not None
        added += found['twelve'] and not found['matched']
        lost += found['matched'] and not found['twelve']
        total += 1
    for totals in counts.values():
        totals['seconds'] = round(totals['seconds'],3)
    return dict(prime_bits=bits, draws=draws, products=total, population='sample' if sample else 'complete',
                added_vs_matched=added, lost_vs_matched=lost, modes=counts)


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('--bits', type=int, required=True)
    p.add_argument('--draws', type=int, required=True)
    p.add_argument('--sample', type=int, default=0, help='zero enumerates all eligible pairs')
    a = p.parse_args()
    print(json.dumps(run(a.bits,a.draws,a.sample), indent=2))
