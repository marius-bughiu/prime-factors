"""Search nearby public integers for a divisor giving the sum of two same-width odd primes."""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import isqrt
from pathlib import Path

from experiments.intermediate_totient_rows import product_band, search as intermediate_search, verify
from experiments.neighbor_smooth_sum import search as neighbor_smooth_search
from scripts.factor import fermat_split, primes_through

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / 'research' / 'shifted-sum-divisors.json'
SMALL_PRIMES = tuple(primes_through(31))
MAX_SHIFT = 64


def smooth_divisors(powers):
    """List each divisor of the peeled part once, using one multiplication per new entry."""
    divisors = [1]
    for prime, exponent in powers:
        old_size = len(divisors)
        for index in range(old_size):
            value = divisors[index]
            for _ in range(exponent):
                value *= prime
                divisors.append(value)
    return divisors


def _candidates(neighbor, lower, upper, work, two_parts):
    """Yield (divisor, complement if already known), treating the unpeeled residual as one factor."""
    residual = neighbor
    powers = []
    complements = {}
    for prime in SMALL_PRIMES:
        exponent = 0
        while True:
            work['division_checks'] += 1
            quotient, remainder = divmod(residual, prime)
            if remainder:
                break
            work['exact_divisions'] += 1
            exponent += 1
            residual = quotient
        if exponent:
            powers.append((prime, exponent))
        if two_parts and prime in (5, 31):
            work['cofactor_divisions'] += 1
            smooth = neighbor//residual
            complements[residual] = smooth
            complements[smooth] = residual
    if two_parts:
        yield from sorted(complements.items())
        return

    work['cofactor_divisions'] += 1
    smooth = neighbor//residual
    if smooth < lower and residual >= upper:
        work['shifts_skipped_by_interval'] += 1
        return
    divisors = smooth_divisors(powers)
    work['smooth_divisors_generated'] += len(divisors)
    work['divisor_multiplications'] += len(divisors)-1
    for divisor in divisors:
        yield divisor, None
        # All peeled divisors are coprime to the residual. The two lists
        # are disjoint unless the residual is one.
        if residual > 1:
            work['divisor_multiplications'] += 1
            yield divisor*residual, None


def search(n, bits, *, two_parts=False):
    """Use only N and its advertised factor width, finishing every shift even after a split."""
    if bits < 2 or n < 3 or n % 2 == 0:
        raise ValueError('expected an odd product and a common factor width of at least two')
    low, high = product_band(n, bits)
    work = dict(shifts=0, setup_roots=1, setup_divisions=2, division_checks=0,
                exact_divisions=0, cofactor_divisions=0, divisors_proposed=0,
                candidate_roots=0, witness_divisibility_checks=0)
    if not two_parts:
        work.update(shifts_skipped_by_interval=0, smooth_divisors_generated=0,
                    divisor_multiplications=0, witness_complement_divisions=0)
    pair, first, first_later = [], None, None
    at_one = False
    for shift in range(1, min(MAX_SHIFT, low)+1):
        neighbor = n+shift
        lower, upper = low+shift, high+shift
        work['shifts'] += 1
        for divisor, complement in _candidates(neighbor, lower, upper, work, two_parts):
            work['divisors_proposed'] += 1
            deficit = divisor-shift
            if not low <= deficit < high or deficit % 2 != 1:
                continue
            total = deficit+1
            discriminant = total*total-4*n
            work['candidate_roots'] += 1
            gap = isqrt(discriminant)
            if gap*gap != discriminant:
                continue
            p, q = (total-gap)//2, (total+gap)//2
            if p <= 1 or p*q != n:
                continue
            pair = [str(p), str(q)]
            if shift == 1:
                at_one = True
            if complement is None:
                work['witness_complement_divisions'] += 1
                complement = neighbor//divisor
            witness = dict(shift=shift, divisor=str(divisor), complement=str(complement))
            if first is None:
                first = witness
            # A proper divisor of the complement gives a later intermediate
            # row. On large inputs this trial-prime check can miss such a divisor.
            for d in SMALL_PRIMES:
                if d >= complement:
                    break
                work['witness_divisibility_checks'] += 1
                a, remainder = divmod(complement, d)
                if remainder == 0:
                    if first_later is None:
                        first_later = dict(**witness, d=d, exponent=str(divisor*a),
                                           numerator=str(a), denominator=str(complement-1))
                    break
    return dict(work=work, pair=pair, first=first, first_later=first_later, shift_one=at_one)


def nine_bit_ceiling(prime_pairs):
    """Retrospective only: use the *known* sum to test every shift and every possible later witness."""
    counts = Counter(products=0, shifts=0, qualifying_shifts=0, recovered=0, shift_one=0,
                     later=0, later_beyond_one=0)
    for p, q in prime_pairs:
        n, deficit = p*q, p+q-1
        any_shift = at_one = later = False
        counts['products'] += 1
        for shift in range(1, min(MAX_SHIFT, deficit)+1):
            counts['shifts'] += 1
            complement, remainder = divmod(n+shift, deficit+shift)
            if remainder:
                continue
            counts['qualifying_shifts'] += 1
            any_shift = True
            at_one |= shift == 1
            # Exact compositeness here, independently of the search's cutoff of 31.
            later |= any(complement % d == 0 for d in range(2, isqrt(complement)+1))
        counts['recovered'] += any_shift
        counts['shift_one'] += at_one
        counts['later'] += later
        counts['later_beyond_one'] += later and not at_one
    return dict(counts)


def _add_run(record, run, first_midpoint):
    totals = record['totals']
    totals['products'] += 1
    totals['recovered'] += bool(run['pair'])
    totals['shift_one'] += run['shift_one']
    totals['later'] += run['first_later'] is not None
    totals['later_beyond_one'] += bool(run['first_later']) and not run['shift_one']
    totals['recovered_at_first_fermat_midpoint'] += bool(run['pair']) and first_midpoint
    record['work'].update(run['work'])


def summarize(inputs, solutions, *, compare_cf=False):
    def empty():
        return dict(totals=Counter(products=0, recovered=0, shift_one=0, later=0, later_beyond_one=0,
                                   recovered_at_first_fermat_midpoint=0), work=Counter())
    primary, baseline = empty(), empty()
    matched = Counter(fermat=0, both=0, shifted_only=0, fermat_only=0, setup_roots=0, midpoints=0)
    cf = Counter()
    recoveries = []
    for n, bits in inputs:
        run, old = search(n,bits), search(n,bits,two_parts=True)
        first_midpoint = fermat_split(n,1)[0] is not None
        _add_run(primary, run, first_midpoint)
        _add_run(baseline, old, first_midpoint)
        if old['pair'] and run['pair'] != old['pair']:
            raise AssertionError('all-divisor search lost a two-parts split')
        if old['first_later'] and not run['first_later']:
            raise AssertionError('all-divisor search lost a two-parts later witness')
        found = bool(run['pair'])
        if found:
            solutions[n] = list(map(int, run['pair']))
            if not compare_cf:
                recoveries.append(dict(n=str(n), pair=run['pair'], first=run['first'],
                                       first_later=run['first_later'], first_fermat_midpoint=first_midpoint))
        budget = run['work']['candidate_roots']
        divisor, spent = fermat_split(n,budget) if budget else (None,0)
        matched['setup_roots'] += int(budget>0)
        matched['midpoints'] += spent
        matched['fermat'] += bool(divisor)
        matched['both'] += found and bool(divisor)
        matched['shifted_only'] += found and not divisor
        matched['fermat_only'] += not found and bool(divisor)
        if divisor:
            solutions[n] = [divisor, n//divisor]
        if compare_cf:
            # Different exponent menu and budget. Evaluate both on precisely the same census products.
            cf_work, cf_hits, _ = intermediate_search(n,bits,price_full=False)
            cf['exponents'] += cf_work['exponents']
            cf['blocks_visited'] += cf_work['visited_blocks']
            cf['candidate_roots'] += cf_work['discriminant_roots']
            cf['setup_roots'] += cf_work['band_setup_roots']
            canonical = 'ordinary' in cf_hits
            intermediate = any(name in cf_hits for name in ('ordinary','first_block','later_intermediate'))
            cf['canonical'] += canonical
            cf['canonical_and_shifted'] += canonical and found
            cf['all_intermediates'] += intermediate
            cf['all_intermediates_and_shifted'] += intermediate and found
            if intermediate:
                source = next(cf_hits[name] for name in ('ordinary','first_block','later_intermediate') if name in cf_hits)
                p = int(source['factor'])
                solutions[n] = sorted([p,n//p])
    result = dict(**primary, two_parts=baseline, matched_total_roots_fermat=matched)
    if compare_cf:
        result['prefix_lcm_comparison'] = cf
    else:
        result['recoveries'] = recoveries
    return result


def measure():
    solutions = {}
    small_primes = [p for p in primes_through(511) if p >= 256]
    small_pairs = list(combinations(small_primes, 2))
    nine_bit = summarize(((p*q,9) for p,q in small_pairs), solutions, compare_cf=True)
    nine_bit['known_factor_ceiling'] = nine_bit_ceiling(small_pairs)
    original = json.loads((ROOT/'research/scaled-power-menu.json').read_text())
    holdout = [dict(factor_bits=block['factor_bits'], **summarize(
        ((int(row['n']),block['factor_bits']) for row in block['rows']), solutions))
        for block in original['small']]
    controls = [dict(id=c['id'], n=c['n'], **search(int(c['n']),1024),
                     two_parts=search(int(c['n']),1024,two_parts=True)) for c in original['controls']]
    known_n = 7687946879999
    known = dict(n=str(known_n), factor_bits=22, **search(known_n,22))
    # The published one-neighbor comparison uses the input and prime cutoff 5.
    published = neighbor_smooth_search(known_n,5)
    factor = published.pop('factor')
    known['published_shift_one'] = dict(**published, pair=[str(factor),str(known_n//factor)] if factor else [])
    if known['pair'] != known['published_shift_one']['pair']:
        raise AssertionError('the two searches disagree on the published comparison')
    for row in [*controls, known]:
        if row['pair']:
            solutions[int(row['n'])] = list(map(int,row['pair']))
    return dict(shifts=[1,MAX_SHIFT], extraction_cutoffs=[5,31],
                menu='Peel all prime powers through 31. Enumerate d and d*R for every divisor d of the peeled part H, with R the residual. There is no divisor-count cutoff. For R=1, enumerate d only. When H<lower+k and R>=upper+k both lists miss the interval and are skipped.',
                work_units='division_checks counts divmod attempts, including the exact_divisions subset. cofactor_divisions forms H. divisor_multiplications counts construction of both lists. divisors_proposed counts interval/parity checks. witness_complement_divisions and witness_divisibility_checks occur only after a verified numerical split.',
                two_parts_rule='Earlier baseline proposes only the peeled part and its complement at cutoffs 5 and 31.',
                later='A proper trial-prime divisor through 31 of the complement certifies a later intermediate row. The separately labelled ceiling allows every divisor of N+k and tests the known complementary quotient for compositeness exactly.',
                matched_budget='One setup root and at most candidate_roots midpoints for Fermat on each input. Skip Fermat entirely when that midpoint budget is zero. The shifted search also pays for peeling and divisor enumeration.',
                cf_comparison='The nine-bit census independently reruns the published width-scaled prefix-LCM menu. Its exponents and work differ from the neighboring-divisor search.',
                nine_bit=nine_bit, holdout=holdout, controls=controls, known_43_bit=known), solutions


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--write', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    record, pairs = measure()
    if args.check:
        if record != json.loads(RECORD.read_text()):
            raise ValueError('shift census changed')
    elif args.write:
        RECORD.write_text(json.dumps(record,indent=2)+'\n')
    else:
        print(json.dumps(record,indent=2))
    if args.verify:
        verify(pairs, panel_name='ShiftedSumDivisorsPanel')
        print(f'Lean verified {len(pairs)} distinct recovered pairs across the searches.')
