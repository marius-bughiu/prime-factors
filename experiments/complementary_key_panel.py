"""Replay the earlier twelve-key panel, grouping outcomes by the public product modulo twelve."""
from argparse import ArgumentParser
from collections import Counter
import json
from random import Random
from time import process_time

from experiments.complementary_keys import search
from experiments.twelve_residue_collision import search as original
from experiments.twelve_residue_panel import eligible_pairs


def run(bits, draws, sample):
    rng = Random(86412)
    groups = {}
    for p, q in eligible_pairs(bits, sample, rng):
        n = p*q
        seed = rng.randrange(1 << 63)
        group = groups.setdefault(n % 12, Counter())
        group['products'] += 1
        methods = [('old', original, 'twelve'), ('folded', search, 'folded')]
        if n % 12 in (5, 7):
            methods.append(('target', search, 'target'))
        outcomes = {}
        for label, method, mode in methods:
            start = process_time()
            factor, work, _ = method(n, draws, seed, mode)
            group[label+'_cpu_seconds'] += process_time()-start
            if factor is not None and factor not in (p,q):
                raise ArithmeticError(f'{label} returned a false factor')
            outcomes[label] = factor is not None
            group[label+'_splits'] += int(factor is not None)
            if work['source'] == 'complement product':
                if pow(3, (factor-1)//2, factor) != 1:
                    raise ArithmeticError('directed hit at the wrong prime')
                group['directed_gcd_hits'] += 1
        group['added'] += int(outcomes['folded'] and not outcomes['old'])
        group['lost'] += int(outcomes['old'] and not outcomes['folded'])
    for group in groups.values():
        for key in list(group):
            if key.endswith('_seconds'):
                group[key] = round(group[key],4)
    return dict(bits=bits, draws=draws, sample=sample, seed=86412, groups=groups)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, required=True)
    parser.add_argument('--draws', type=int, required=True)
    parser.add_argument('--sample', type=int, default=0)
    args = parser.parse_args()
    print(json.dumps(run(args.bits, args.draws, args.sample), indent=2, sort_keys=True))
