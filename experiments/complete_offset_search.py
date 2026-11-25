"""Search Gauss's complete offset rectangle with a cap on raw (j,k) visits."""

import argparse
from collections import Counter
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.modular_hyperbola import Work, floor_sum
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
CONTROL_IDS = ('grouped-norm-fresh-2048', 'grouped-norm-crossed-2048')


def slot_count(T, h, max_offset):
    """Count k=1,...,floor(T*j/h)+1 over 1<=j<=max_offset, without visiting offsets."""
    work = Work()
    count = max_offset+floor_sum(max_offset, h, T, T, work)
    return count, work.euclidean_steps


def search(n, max_pairs, *, exhaust=False):
    """Return a verified proper split or the unspent space and work completed.

    One visit is one raw (j,k) slot, before the coprimality test. With exhaust
    set, continue after the first split and count all hits up to the same cap.
    Neither completing a scan nor returning a split certifies primality.
    """
    if n < 4 or max_pairs < 0:
        raise ValueError('expected an integer >= 4 and a nonnegative raw-pair budget')
    T = isqrt(n)
    h = n-T*T
    max_offset = isqrt(4*h//3)
    work = dict(raw_pairs=0, loose_raw_pairs=0, count_euclidean_steps=0, visited_pairs=0,
                coprime_pairs=0, negative_discriminants=0, integer_square_roots=0,
                square_hits=0, proper_hits=0, last_slot_hits=0, interior_hits=0)
    result = dict(status='partial', factor=None, remaining=n, root=T, offset=h, max_offset=max_offset,
                  max_pairs=max_pairs, first_hit=None, next_pair=None, unvisited_pairs=0, **work)
    if h == 0:
        result.update(status='split', factor=T, remaining=n//T)
        return result

    raw, steps = slot_count(T, h, max_offset)
    loose, loose_steps = slot_count(T, h, isqrt(4*h))
    result.update(raw_pairs=raw, loose_raw_pairs=loose, count_euclidean_steps=steps+loose_steps,
                  unvisited_pairs=raw)
    for j in range(1, max_offset+1):
        last = T*j//h+1
        for k in range(1, last+1):
            if result['visited_pairs'] == max_pairs:
                result['next_pair'] = [j, k]
                return result
            result['visited_pairs'] += 1
            result['unvisited_pairs'] -= 1
            if gcd(j, k) != 1:
                continue
            result['coprime_pairs'] += 1
            residual = T*j-h*k
            delta = j*j+4*k*residual
            if delta < 0:
                result['negative_discriminants'] += 1
                continue
            result['integer_square_roots'] += 1
            d = isqrt(delta)
            if d*d != delta:
                continue
            result['square_hits'] += 1
            factor = gcd(n, (j+2*T*k-d)//2)
            if not 1 < factor < n:
                continue
            result['proper_hits'] += 1
            result['last_slot_hits' if k == last else 'interior_hits'] += 1
            if result['factor'] is None:
                result.update(status='split', factor=factor, remaining=n//factor,
                              first_hit=dict(j=j, k=k, residual=residual, delta=delta,
                                             square_root=d, last_slot=k == last))
            if not exhaust:
                return result
    if result['unvisited_pairs'] != 0:
        raise AssertionError('floor-sum count disagrees with exhaustive search')
    if result['factor'] is None:
        result['status'] = 'exhausted'
    return result


def census(bits, *, witnesses=None):
    """Test every unordered pair of distinct primes of the same specified bit width."""
    primes = [p for p in primes_through((1 << bits)-1) if p >= 1 << (bits-1)]
    totals = Counter()
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            n = p*q
            run = search(n, 65_536, exhaust=True)
            if run['unvisited_pairs'] or run['factor'] not in (p, q) or run['factor']*run['remaining'] != n:
                raise AssertionError(f'no verified complete census result for {n}')
            if witnesses is not None:
                hit = run['first_hit']
                witnesses.append((n, hit['j'], hit['k'], run['factor']))
            totals['products'] += 1
            totals['only_last_slot'] += int(run['interior_hits'] == 0)
            for field in ('raw_pairs', 'loose_raw_pairs', 'integer_square_roots', 'square_hits', 'proper_hits'):
                totals[field] += run[field]
    return dict(bits=bits, primes=len(primes), **totals)


def render_census_certificate(witnesses):
    """Emit bounded kernel checks on every recorded probe output, product and prime."""
    lines = [
        'import PrimeFactors.CompleteOffsetSearch',
        'import Mathlib.Data.Nat.Prime.Basic',
        '',
        'namespace PrimeFactors.GeneratedCompleteOffsetCensus',
        'open CompleteOffsetSearch',
        '',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 2000000',
        '',
        'private structure Witness where',
        '  n : ℕ',
        '  j : ℕ',
        '  k : ℕ',
        '  d : ℕ',
        '',
        'private def checked (w : Witness) : Bool :=',
        '  let t := w.n.sqrt',
        '  let h := w.n-t^2',
        '  decide (w.d.Prime ∧ (w.n/w.d).Prime ∧ w.d*(w.n/w.d)=w.n ∧',
        '    0<w.j ∧ 3*w.j^2≤4*h ∧ 0<w.k ∧ w.k≤t*w.j/h+1 ∧ w.j.Coprime w.k ∧',
        '    probe w.n t w.j w.k=some w.d)',
        '',
    ]
    for offset in range(0, len(witnesses), 32):
        chunk = witnesses[offset:offset+32]
        values = ',\n  '.join(f'⟨{n},{j},{k},{d}⟩' for n, j, k, d in chunk)
        lines.extend([f'example : ([{values}] : List Witness).all checked = true := by decide +kernel', ''])
    lines.append('end PrimeFactors.GeneratedCompleteOffsetCensus')
    return '\n'.join(lines)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--census', action='store_true', help='all same-width distinct 7-, 8-, 9-bit prime pairs')
    modes.add_argument('--controls', action='store_true', help='two public 2048-bit controls')
    parser.add_argument('--max-pairs', type=int, default=64)
    parser.add_argument('--exhaust', action='store_true', help='continue after a split up to the same budget')
    parser.add_argument('--census-certificate', type=Path, help='write a Lean proof of each census witness')
    args = parser.parse_args()
    if args.census_certificate and not args.census:
        parser.error('--census-certificate requires --census')
    if args.census:
        witnesses = [] if args.census_certificate else None
        rows = [census(bits, witnesses=witnesses) for bits in (7, 8, 9)]
        if args.census_certificate:
            args.census_certificate.write_text(render_census_certificate(witnesses))
    elif args.controls:
        controls = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
        rows = [dict(id=row['id'], **search(int(row['n']), args.max_pairs, exhaust=args.exhaust))
                for row in controls if row['id'] in CONTROL_IDS]
    elif args.n is not None:
        rows = [search(args.n, args.max_pairs, exhaust=args.exhaust)]
    else:
        parser.error('provide an integer, --census or --controls')
    print(json.dumps(rows, indent=2))


if __name__ == '__main__':
    main()
