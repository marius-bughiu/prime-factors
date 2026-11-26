"""Compare a Knuth–Schroeppel score with fixed multipliers in the same polynomial sieve.

For Q(x)=((Ax+B)^2-kN)/A, at an odd prime l not dividing A or N the
mean valuation for uniform x is 2/(l-1) for a unit square, 1/l for l|k
(k squarefree), and zero otherwise. At 2, A is odd and the means at
kN=1,3,5,7 mod 8 are 2,1/2,1,1/2. These are full-period means, not a
guarantee on a finite interval. On a scaled full-size polynomial, primes
dividing A can have a different mean. The half-log penalty approximates
growth in the norms. Historical method: Silverman, Math. Comp. 48
(1987), 329–339; https://flintlib.org/doc/qsieve/qsieve_knuth_schroeppel.html .
The score and its integer weights here are specified independently.

Replay the frozen panel with --panel --verify. Factor labels are used
only to validate independently discovered gcds.
"""

import argparse
from decimal import Decimal, localcontext
from functools import lru_cache
import json
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from .gap_coverage import primes_through
from .polynomial_relations import BLOCKS, BOUND, RADIUS, search as polynomial_search

ROOT = Path(__file__).resolve().parents[1]
SEED = b'mpqs-multiplier-2026-11-26-v1'
SCALE = 1_000_000
ARMS = ('one', 'three', 'selected', 'matched_one', 'extra_one')


@lru_cache(maxsize=1)
def score_tables():
    """Input-independent weights rounded to the nearest millionth of a bit."""
    candidates = tuple(k for k in range(1, 64, 2) if
                       all(k % (d*d) for d in range(3, isqrt(k)+1, 2)))
    primes = tuple(primes_through(97)[1:])
    with localcontext() as context:
        context.prec = 48
        log2 = Decimal(2).ln()

        def weight(n, numerator, denominator):
            value = Decimal(n).ln()/log2 * numerator * SCALE / denominator
            return int(value.to_integral_value(rounding='ROUND_HALF_EVEN'))

        penalties = {k: weight(k, -1, 2) for k in candidates}
        values = {p: (weight(p, 1, p), weight(p, 2, p-1)) for p in primes}
    # Euler's criterion gives 0, 1 or p-1; multiply two signs below.
    signs = {k: tuple(pow(k, (p-1)//2, p) for p in primes) for k in candidates}
    return candidates, primes, penalties, values, signs


def select(n):
    if n <= 2 or n % 2 == 0:
        raise ValueError('expected an odd integer greater than two')
    candidates, primes, penalties, values, signs = score_tables()
    work = dict(input_residues=1, input_euler_powers=0, candidate_gcds=0,
                candidate_scores=0, odd_score_terms=0)
    two_weights = {1: 2*SCALE, 3: SCALE//2, 5: SCALE, 7: SCALE//2}
    residue8 = n % 8
    input_signs = []
    for p in primes:
        residue = n % p
        work['input_residues'] += 1
        if residue == 0 and p < n:
            return dict(k=None, factor=p, score=None, one_score=None, work=work)
        input_signs.append(pow(residue, (p-1)//2, p))
        work['input_euler_powers'] += 1
    scores = {}
    for k in candidates:
        work['candidate_gcds'] += 1
        if gcd(n, k) != 1:
            continue
        score = penalties[k] + two_weights[k*residue8 % 8]
        for p, sign_n, sign_k in zip(primes, input_signs, signs[k]):
            work['odd_score_terms'] += 1
            if sign_n:
                ramified, split = values[p]
                if sign_k == 0:
                    score += ramified
                elif sign_k == sign_n:
                    score += split
        scores[k] = score
        work['candidate_scores'] += 1
    k = max(scores, key=lambda m: (scores[m], -m))
    return dict(k=k, factor=None, score=scores[k], one_score=scores[1], work=work)


def search(n, arm='selected', *, bound=BOUND, radius=RADIUS, blocks=BLOCKS):
    if arm not in ARMS:
        raise ValueError('unknown comparison arm')
    if n <= 2 or n % 2 == 0 or min(radius, blocks) <= 0 or bound < 2:
        raise ValueError('expected an odd integer and positive sieve dimensions')
    scored = select(n) if arm in ('selected', 'matched_one') else None
    budget = blocks + int(arm == 'extra_one')
    k = scored['k'] if arm == 'selected' else (3 if arm == 'three' else 1)
    if scored and scored['factor'] is not None:
        return dict(multiplier=None, block_budget=budget, selection=scored, factor=scored['factor'],
                    outcome='score_gcd', blocks=0, positions=0)
    run = polynomial_search(n, 'square', bound, radius, budget, multiplier=k)
    stats = run.pop('policies').get('base', {})
    stats.pop('factor', None)
    return dict(run, **stats, multiplier=k, block_budget=budget, selection=scored)


def matched_prefixes(n, selected, baseline, extra, *, bound=BOUND, radius=RADIUS,
                     max_blocks=4*BLOCKS):
    """Retrospective k=1 prefixes; the first whole block crossing each target is kept."""
    metrics = ('sieve_marks', 'prime_divisions')
    if max_blocks < 1 or any(r['blocks'] != r['block_budget'] for r in (baseline, extra, selected)):
        raise ValueError('expected completed positive-budget sieve runs')
    cache = {run['block_budget']: run for run in (baseline, extra)}
    calibration = []

    def at(b):
        if b not in cache:
            run = search(n, 'one', bound=bound, radius=radius, blocks=b)
            if run['blocks'] != b:
                raise ArithmeticError('cost comparison needs complete sieve prefixes')
            cache[b] = run
            calibration.append(b)
        return cache[b]

    def first_crossing(keys):
        def fits(b):
            return all(at(b)[key] >= selected[key] for key in keys)

        original = baseline['block_budget']
        # Start near the observed mean cost; brackets and the adjacent prefix
        # decide the answer using exact counts, independently of that estimate.
        guess = max((original*selected[key] + max(1, baseline[key])-1)//max(1, baseline[key])
                    for key in keys)
        guess = min(max_blocks, max(1, guess))
        if fits(guess):
            lo, hi = guess-1, guess
            while lo > 0 and fits(lo):
                lo, hi = max(0, lo-2*(guess-lo)), lo
        else:
            lo, hi = guess, min(max_blocks, guess+1)
            while hi < max_blocks and not fits(hi):
                lo, hi = hi, min(max_blocks, hi+max(1, hi-guess)*2)
            if not fits(hi):
                return at(hi), False
        while hi-lo > 1:
            mid = (lo+hi)//2
            if fits(mid):
                hi = mid
            else:
                lo = mid
        return at(hi), True

    matches = {}
    for name, keys in [('marks', metrics[:1]), ('marks_and_divisions', metrics)]:
        run, crossed = first_crossing(keys)
        matches[name] = dict(run, reached_cost=crossed)
    effort = dict(additional_runs=len(calibration), block_budgets=calibration,
                  **{key: sum(cache[b][key] for b in calibration)
                     for key in ('blocks', 'positions', *metrics)})
    return matches, effort


def inputs():
    from .crt_holdout import draw_sample
    for filename in ('factor-sum-quantile.json', 'lifted-period-join.json'):
        for case in json.loads((ROOT/'benchmarks'/filename).read_text()):
            n = int(case['n'])
            if n.bit_length() < 100:
                yield case['id'], n, case['factors']
    for attempt, n, primes in draw_sample(SEED, 8):
        yield f'fresh-79-draw-{attempt}', n, list(map(str, primes))
    cases = json.loads((ROOT/'benchmarks'/'near-smooth-sum.json').read_text())
    for case in cases[-2:]:
        yield case['id'], int(case['n']), []


def panel(verify=False, timings=None):
    from scripts.factor import render_certificate, verify_file
    cases = []
    for name, n, expected in inputs():
        methods, found, raw = {}, [], {}
        for arm in ARMS:
            start = process_time_ns()
            run = search(n, arm)
            if timings is not None:
                timings.setdefault(name, {})[arm] = process_time_ns()-start
            raw[arm] = run
        start = process_time_ns()
        matches, calibration = matched_prefixes(n, raw['selected'], raw['one'], raw['extra_one'])
        if timings is not None:
            timings[name]['matching_calibration'] = process_time_ns()-start
            for key, run in matches.items():
                start = process_time_ns()
                replay = search(n, 'one', blocks=run['block_budget'])
                timings[name][key] = process_time_ns()-start
                if any(replay[m] != run[m] for m in ('positions', 'sieve_marks', 'prime_divisions', 'factor')):
                    raise ArithmeticError('independent timed replay of the prefix disagrees')
        sensitivity = {}
        for arm, run in {**raw, **matches}.items():
            run = run.copy()
            f = run.pop('factor')
            factors = []
            if f is not None:
                if not (1 < f < n and n % f == 0):
                    raise ArithmeticError('improper reported divisor')
                found = sorted((f, n//f))
                factors = list(map(str, found))
                if expected and factors != expected:
                    raise ArithmeticError('independent factor labels disagree')
            section = sensitivity if arm in matches else methods
            section[arm] = dict(run, factors=factors, remaining=[] if f else [str(n)])
        if found and verify:
            path = ROOT/'build'/'multiplier-polynomials'/f'{name}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(render_certificate(n, found, certificate_trial_limit=2_000_000))
            verify_file(path)
        cases.append(dict(id=name, n=str(n), bits=n.bit_length(), methods=methods,
                          post_primary_cost_sensitivity=sensitivity, calibration=calibration))
    return dict(seed=SEED.decode(), score_bound=97, multiplier_bound=63,
                score_units_per_bit=SCALE, bound=BOUND, radius=RADIUS, blocks=BLOCKS,
                sources=['benchmarks/factor-sum-quantile.json (eight small cases)',
                         'benchmarks/lifted-period-join.json (six small cases)',
                         'crt_holdout.draw_sample(seed, 8)',
                         'benchmarks/near-smooth-sum.json (last two cases)'],
                selection_table=dict(candidates=26, odd_primes=24, fixed_euler_powers=624,
                                     rounded_log_weights=74),
                cost_sensitivity=dict(fixed_multiplier=1, maximum_blocks=4*BLOCKS,
                                      measured_after_primary=True,
                                      include_first_whole_crossing_block=True),
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--arm', choices=ARMS, default='selected')
    parser.add_argument('--timings', type=Path, help='optional diagnostic process CPU times in ns')
    args = parser.parse_args()
    if args.panel:
        timings = {} if args.timings else None
        report = panel(args.verify, timings)
        path = ROOT/'research'/'multiplier-polynomials-panel.json'
        path.write_text(json.dumps(report, indent=2)+'\n')
        if args.timings:
            args.timings.write_text(json.dumps(timings, indent=2)+'\n')
        for section in ('methods', 'post_primary_cost_sensitivity'):
            print(json.dumps({a: sum(bool(c[section][a]['factors']) for c in report['cases'])
                              for a in report['cases'][0][section]}))
    elif args.n is not None and not (args.verify or args.timings):
        print(json.dumps(search(args.n, args.arm)))
    else:
        parser.error('supply a product, or --panel [--verify] [--timings PATH]')


if __name__ == '__main__':
    main()
