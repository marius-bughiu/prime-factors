"""Count nonunits in a fractional prefix using gcds of wheel-coprime representatives."""

import json
from collections import Counter
from math import gcd
from pathlib import Path

from experiments.square_mask_digit_queries import odd_trial
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/fractional-prefix-wheel.json'
WHEELS = {1: (), 2: (2,), 6: (2, 3), 30: (2, 3, 5), 210: (2, 3, 5, 7)}


def smooth_factors(limit, primes, work):
    """Enumerate each permitted multiplier once without sorting or scanning the prefix."""
    values = [1]
    for p in primes:
        for index in range(len(values)):
            a = values[index]*p
            work['smooth_generation_multiplications'] += 1
            while a <= limit:
                values.append(a)
                a *= p
                work['smooth_generation_multiplications'] += 1
    work['smooth_entries'] = len(values)
    return values


def weighted_count(n, limit, wheel, residues):
    work = Counter(eligibility_gcds=1)
    common = gcd(wheel, n)
    if common != 1:
        return None, common, work
    values = smooth_factors(limit, WHEELS[wheel], work)
    hits = {}
    for base in range(0, limit, wheel):
        work['wheel_blocks_visited'] += 1
        for residue in residues:
            core = base+residue
            work['wheel_slots_examined'] += 1
            if core > limit:
                break
            work['cores_visited'] += 1
            if core == 1:
                continue
            work['core_gcds'] += 1
            if gcd(core, n) == 1:
                continue
            if not hits:
                work['core_gcds_to_first_or_exhaustion'] = work['core_gcds']
                work['first_hit_core'] = core
            bound = limit//core
            work['weight_divisions'] += 1
            hits[core] = sum(a <= bound for a in values)
            work['weight_comparisons'] += len(values)
    if not hits:
        work['core_gcds_to_first_or_exhaustion'] = work['core_gcds']
    return hits, common, work


def direct_counts(n, limit, primes):
    """Independent scan. Strip wheel primes from each nonunit to check each multiplicity."""
    groups = Counter()
    for t in range(1, limit+1):
        if gcd(t, n) != 1:
            core = t
            for p in primes:
                while core % p == 0:
                    core //= p
            groups[core] += 1
    return groups


def sampling(n, m, h):
    limit = n//m
    if limit == 0:
        raise ArithmeticError('This cohort requires a nonempty sampling interval')
    variance = m*m*h*(limit-h)
    if not variance:
        without = 1
    else:
        without = variance*limit//(variance+limit-1)+1
        if not (variance*(limit-without) < without*(limit-1)
                and variance*(limit-without+1) >= (without-1)*(limit-1)):
            raise ArithmeticError('Incorrect distinct-draw threshold')
    return dict(prefix_length=limit, nonunits=h, single_draw_variance=variance,
                first_iid_draws=variance+1, first_distinct_draws=without)


def study():
    primes = [p for p in primes_through(63) if p % 2]
    residues = {w: [x for x in range(1, w+1) if gcd(x, w) == 1] for w in WHEELS}
    pooled = {cohort: {mode: {str(w): Counter() for w in WHEELS} for mode in ('half', 'greatest')}
              for cohort in ('all_balanced', 'equal_prime_width')}
    population = Counter()
    examples = []
    for q in primes:
        for p in primes:
            if not (3 <= q.bit_length() <= 6 and p < q < 2*p):
                continue
            n = p*q
            cohorts = ['all_balanced']
            if p.bit_length() == q.bit_length():
                cohorts.append('equal_prime_width')
            population.update(cohorts)
            trial_p, trial = odd_trial(n)
            if trial_p != p:
                raise ArithmeticError(f'Trial division disagrees at {n}')
            for mode, m in [('half', 2), ('greatest', gcd(24, n+1))]:
                limit = n//m
                direct = direct_counts(n, limit, ())
                h = sum(direct.values())
                moments = sampling(n, m, h)
                if m*(h+1) != p+q or moments['single_draw_variance'] != (p+q-m)*(p-1)*(q-1):
                    raise ArithmeticError(f'Count or variance disagrees at {n}, m={m}')
                control = dict(product=str(n), denominator=m, choice=mode, reference_factors=[str(p), str(q)],
                               trial=trial, sampling=moments, wheels={})
                for wheel, prime_list in WHEELS.items():
                    hits, common, work = weighted_count(n, limit, wheel, residues[wheel])
                    row = dict(**work)
                    stats = Counter(products=1, eligibility_gcds=1)
                    if hits is None:
                        if common not in (p, q, n):
                            raise ArithmeticError(f'Unexpected wheel gcd {common} at {n}')
                        stats['eligibility_gcd_whole_product' if common == n else 'eligibility_gcd_proper'] += 1
                        row['eligibility_gcd'] = str(common)
                    else:
                        if hits != direct_counts(n, limit, prime_list) or sum(hits.values()) != h:
                            raise ArithmeticError(f'Multiplicities disagree at {n}, m={m}, W={wheel}')
                        for key, count in work.items():
                            if key not in ('eligibility_gcds', 'first_hit_core'):
                                stats[key] += count
                        stats.update(eligible=1, prefix_nonunits=h, distinct_hit_cores=len(hits),
                                     direct_count_gcds=limit,
                                     direct_gcds_to_first_or_exhaustion=next(iter(direct), limit),
                                     ascending_trial_divisions=trial['ascending_divisibility_checks'],
                                     descending_trial_divisions=trial['descending_divisibility_checks'],
                                     iid_draws=moments['first_iid_draws'], distinct_draws=moments['first_distinct_draws'])
                        row['nonunits_reconstructed'] = sum(hits.values())
                        if mode == 'greatest':
                            row['hit_core_multiplicities'] = {str(b): count for b, count in hits.items()}
                    control['wheels'][str(wheel)] = row
                    for cohort in cohorts:
                        pooled[cohort][mode][str(wheel)].update(stats)
                if n in (15, 2183) or (n == 3233 and mode == 'greatest'):
                    examples.append(control)
    return dict(population='All distinct odd p < q < 2p with larger prime of 3–6 bits. Equal-width cases are a subset.',
                cohort_sizes=dict(population),
                counting='Each core b contributes the number of wheel-smooth a with ab inside the prefix. Only nonunit cores need weights. Gcd(1,N) is known. The totals include all other visited cores.',
                setup='Each wheel table is prepared once for the cohort; smooth multipliers are generated afresh for each eligible prefix. Each successful or overflowing prime multiplication is counted.',
                wheel_setup={str(w):dict(one_time_residue_gcds=w, residue_classes=len(rs)) for w, rs in residues.items()},
                thresholds='RMS error below one in the usual unbiased prime-sum estimator. First positive draw count, including the zero-variance case.',
                cohorts=pooled, examples=examples)


if __name__ == '__main__':
    output = study()
    if output != json.loads(FIXTURE.read_text()):
        raise SystemExit('Wheel prefix counts differ from their reviewed fixture')
    print(f"Checked five wheels at two denominator choices on {output['cohort_sizes']['all_balanced']} products.")
