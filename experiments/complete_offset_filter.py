"""Measure the signed-square work saved by rejecting whole obstructed offsets."""

import argparse
from collections import Counter
import json
from pathlib import Path
from statistics import median
from time import perf_counter

from experiments.complete_offset_search import CONTROL_IDS, search
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
FILTER_PRIME_LIMIT = 251
FIELDS = ('covered_pairs', 'visited_pairs', 'skipped_pairs', 'skipped_rows', 'row_filter_tests', 'row_modulus_tests',
          'negative_discriminants', 'integer_square_roots', 'square_hits', 'proper_hits')


def comparison(n, budget, *, exhaust):
    original = search(n, budget, exhaust=exhaust)
    filtered = search(n, budget, exhaust=exhaust, filter_prime_limit=FILTER_PRIME_LIMIT)
    for key in ('covered_pairs', 'unvisited_pairs', 'next_pair', 'first_hit', 'square_hits', 'proper_hits', 'factor'):
        if original[key] != filtered[key]:
            raise AssertionError(f'offset filter changed {key} for {n}')
    for run in (original, filtered):
        if run['visited_pairs']+run['skipped_pairs'] != run['covered_pairs']:
            raise AssertionError('inconsistent skip accounting')
    return original, filtered


def panel(bits, *, timed=False):
    primes = [p for p in primes_through((1<<bits)-1) if p >= 1<<(bits-1)]
    totals = {'all_slots': [Counter(), Counter()], 'through_first_split': [Counter(), Counter()]}
    count = 0
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            n = p*q
            count += 1
            for label, results in totals.items():
                all_slots = label == 'all_slots'
                runs = comparison(n, 65536, exhaust=all_slots)
                for summary, run in zip(results, runs):
                    if run['factor'] not in (p, q) or (all_slots and run['unvisited_pairs']):
                        raise AssertionError(f'incomplete panel result for {n}')
                    summary.update({field:run[field] for field in FIELDS})
    result = dict(bits=bits, products=count, splits=count,
                  **{label:dict(original=values[0], filtered=values[1]) for label, values in totals.items()})
    if timed:
        inputs = [p*q for i,p in enumerate(primes) for q in primes[i+1:]]
        times = {}
        for label, exhaust in [('all_slots', True), ('through_first_split', False)]:
            samples = {'original': [], 'filtered': []}
            for repeat in range(5):
                order = ('original', 'filtered') if repeat % 2 == 0 else ('filtered', 'original')
                for method in order:
                    prime_limit = FILTER_PRIME_LIMIT if method == 'filtered' else None
                    start = perf_counter()
                    for n in inputs:
                        search(n, 65536, exhaust=exhaust, filter_prime_limit=prime_limit)
                    samples[method].append(perf_counter()-start)
            times[label] = {method:median(values) for method,values in samples.items()}
        result['median_seconds_5_rounds'] = times
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--controls', action='store_true', help='compare bounded scans of the two 2048-bit controls')
    parser.add_argument('--timings', action='store_true', help='time five matched rounds of each small panel')
    parser.add_argument('--max-pairs', type=int, default=64, help='raw-position cap on full-size controls')
    args = parser.parse_args()
    if args.controls:
        cases = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
        data = []
        for case in cases:
            if case['id'] in CONTROL_IDS:
                original, filtered = comparison(int(case['n']), args.max_pairs, exhaust=True)
                data.append(dict(id=case['id'], original=original, filtered=filtered))
    else:
        data = [panel(bits, timed=args.timings) for bits in (7,8,9)]
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
