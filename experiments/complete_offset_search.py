"""Search Gauss's complete offset rectangle with a cap on raw (j,k) visits."""

import argparse
from collections import Counter
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.grouped_offset_rows import local_failures
from experiments.modular_hyperbola import Work, floor_sum
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
CONTROL_IDS = ('grouped-norm-fresh-2048', 'grouped-norm-crossed-2048')


def slot_count(T, h, max_offset):
    """Count k=1,...,floor(T*j/h)+1 over 1<=j<=max_offset, without visiting offsets."""
    work = Work()
    count = max_offset+floor_sum(max_offset, h, T, T, work)
    return count, work.euclidean_steps


def search(n, max_pairs, *, exhaust=False, filter_prime_limit=None):
    """Return a verified proper split or the unspent space and work completed.

    The cap is on raw positions covered. A filtered block consumes its full
    position count but uses no gcd tests. With exhaust set, continue after
    the first split and count all hits up to the same cap.
    Neither completing a scan nor returning a split certifies primality.
    """
    if filter_prime_limit is not None and filter_prime_limit < 0:
        raise ValueError('filter prime limit must be nonnegative')
    if n < 4 or max_pairs < 0:
        raise ValueError('expected an integer >= 4 and a nonnegative raw-pair budget')
    T = isqrt(n)
    h = n-T*T
    max_offset = isqrt(4*h//3)
    work = dict(raw_pairs=0, loose_raw_pairs=0, count_euclidean_steps=0, visited_pairs=0,
                covered_pairs=0, skipped_pairs=0, skipped_rows=0, row_filter_tests=0, row_modulus_tests=0,
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
    powers = []
    if filter_prime_limit is not None:
        primes = primes_through(min(max_offset, filter_prime_limit))
        ordinary, higher = local_failures(-h, primes, max_offset)
        powers = ordinary+higher
        result['obstruction_powers'] = powers
    for j in range(1, max_offset+1):
        last = T*j//h+1
        remaining_budget = max_pairs-result['covered_pairs']
        if not remaining_budget:
            result['next_pair'] = [j, 1]
            return result
        if powers:
            result['row_filter_tests'] += 1
            forbidden = False
            for power in powers:
                result['row_modulus_tests'] += 1
                if j % power == 0:
                    forbidden = True
                    break
            if forbidden:
                skipped = min(last, remaining_budget)
                result['covered_pairs'] += skipped
                result['unvisited_pairs'] -= skipped
                result['skipped_pairs'] += skipped
                result['skipped_rows'] += 1
                if skipped < last:
                    result['next_pair'] = [j, skipped+1]
                    return result
                continue
        for k in range(1, last+1):
            if result['covered_pairs'] == max_pairs:
                result['next_pair'] = [j, k]
                return result
            result['visited_pairs'] += 1
            result['covered_pairs'] += 1
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
                witnesses.append((n, run['root'], hit['j'], hit['k'], hit['square_root'], run['factor']))
            totals['products'] += 1
            totals['only_last_slot'] += int(run['interior_hits'] == 0)
            for field in ('raw_pairs', 'loose_raw_pairs', 'integer_square_roots', 'square_hits', 'proper_hits'):
                totals[field] += run[field]
    return dict(bits=bits, primes=len(primes), **totals)


def render_census_certificate(witnesses):
    """Emit bounded kernel checks on every recorded probe output, product and prime."""
    primes = sorted({prime for n, _, _, _, _, f in witnesses for prime in (f, n//f)})
    lines = ["""import PrimeFactors.CompleteOffsetSearch
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.GeneratedCompleteOffsetCensus
open CompleteOffsetSearch

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def primePool : List ℕ := [@@PRIMES@@]

private theorem poolPrimes (p : ℕ) (member : p ∈ primePool) : p.Prime := by
  simp only [primePool,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with @@CASES@@ <;> norm_num

private structure Witness where
  n : ℕ
  t : ℕ
  j : ℕ
  k : ℕ
  d : ℕ
  f : ℕ

private def checked (w : Witness) : Bool :=
  let S := w.j+2*w.t*w.k
  let h := w.n-w.t^2
  decide (w.t*w.t≤w.n ∧ w.n<(w.t+1)*(w.t+1) ∧
    S^2=4*w.k^2*w.n+w.d^2 ∧ w.n.gcd ((S-w.d)/2)=w.f ∧ 1<w.f ∧ w.f<w.n ∧
    w.f ∈ primePool ∧ w.n/w.f ∈ primePool ∧ w.f*(w.n/w.f)=w.n ∧
    0<w.j ∧ 3*w.j^2≤4*h ∧ 0<w.k ∧ w.k≤w.t*w.j/h+1 ∧ w.j.Coprime w.k)

private def correct (w : Witness) : Prop :=
  probe w.n w.n.sqrt w.j w.k=some w.f ∧ w.f.Prime ∧ (w.n/w.f).Prime ∧ w.f*(w.n/w.f)=w.n ∧
    0<w.j ∧ 3*w.j^2≤4*(w.n-w.n.sqrt^2) ∧ 0<w.k ∧ w.k≤w.n.sqrt*w.j/(w.n-w.n.sqrt^2)+1 ∧
    w.j.Coprime w.k

private theorem sound (w : Witness) (yes : checked w=true) : correct w := by
  simp only [checked,decide_eq_true_eq] at yes
  obtain ⟨lo,hi,square,g,proper,below,p,q,mul,rest⟩ := yes
  have root := (Nat.eq_sqrt.mpr ⟨lo,hi⟩).symm
  have gap : (w.j+2*w.t*w.k)^2-4*w.k^2*w.n=w.d*w.d := by rw [square,Nat.add_sub_cancel_left,pow_two]
  unfold correct
  rw [root]
  refine ⟨?_,poolPrimes _ p,poolPrimes _ q,mul,rest⟩
  unfold probe
  dsimp only
  rw [gap,Nat.sqrt_eq,g,if_pos]
  exact ⟨by omega,pow_two _,proper,below⟩

private theorem checkRows (rows : List Witness) (ok : rows.all checked=true) :
    ∀ w ∈ rows, correct w := fun w hw => sound w (List.all_eq_true.mp ok w hw)
""".replace('@@PRIMES@@', ','.join(map(str, primes))).replace('@@CASES@@', ' | '.join(['rfl']*len(primes)))]
    for offset in range(0, len(witnesses), 32):
        chunk = witnesses[offset:offset+32]
        values = ',\n  '.join('⟨'+','.join(map(str, w))+'⟩' for w in chunk)
        lines.extend([f'example : ∀ w ∈ ([{values}] : List Witness), correct w :=',
                      '  checkRows _ (by decide +kernel)', ''])
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
