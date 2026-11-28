"""Bounded comparison of congruence-covered product lifts and balanced trial division."""

import json
from collections import Counter
from math import gcd, isqrt, prod
from pathlib import Path

from experiments.fractional_matched_divisors import check as check_matched_divisors, direct_pairs
from experiments.square_mask_digit_queries import odd_trial
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/fractional-rough-lifts.json'


def wheel(h, r):
    primes = primes_through(h+1)
    p = prod(primes)
    if r <= h+1 or r not in primes_through(r):
        raise ValueError('The auxiliary prime must exceed H+1')
    # c = 1 mod P and 2c = 1 mod r. One small inverse per reusable wheel.
    c = 1 + p * (-pow(2*p, -1, r) % r)
    return dict(h=h, primorial=p, auxiliary_prime=r, period=p*r, crt_multiplier=c)


def select(n, setup):
    h, p, r, period = (setup[key] for key in ('h', 'primorial', 'auxiliary_prime', 'period'))
    low = n//(8*(h+1))+1
    first = low + (setup['crt_multiplier']*n-low) % period
    rejected = []
    for i in range(3):
        m = first+i*period
        if (m-n) % p or (2*m-n) % r:
            raise ArithmeticError('Incorrect CRT representative')
        d = gcd(n, m)
        if d == 1:
            return m, rejected
        rejected.append(d)
    raise ArithmeticError(f'All three representatives share a divisor with {n}')


def predicted_gcd(j, setup):
    return gcd(abs(j+1), setup['primorial']) * gcd(abs(j+2), setup['auxiliary_prime'])


def check_pattern(n, m, setup, indices):
    """Compare the gcd computed on the actual product lift with the shifted-index formula."""
    period = setup['period']
    if gcd(n, period) != 1:
        raise ValueError('The gcd pattern requires a unit input')
    units = 0
    for j in indices:
        actual = gcd(n+j*m, period)
        if actual != predicted_gcd(j, setup):
            raise ArithmeticError(f'Shifted gcd disagrees at index {j}')
        units += actual == 1
    return units


def first_rough_neighbours(setup):
    stop = setup['auxiliary_prime']+2
    negative = next(-j for j in range(1, stop) if predicted_gcd(-j, setup) == 1)
    positive = next(j for j in range(1, stop) if predicted_gcd(j, setup) == 1)
    return [negative, positive]


def full_width_pattern():
    setup = wheel(999, 1009)
    period = setup['period']
    n = period*((2**2047)//period+1)+1
    m, rejected = select(n, setup)
    neighbours = first_rough_neighbours(setup)
    indices = range(neighbours[0], neighbours[1]+1)
    units = check_pattern(n, m, setup, indices)
    if neighbours != [-1010, 1008] or units != 3 or not 7992*m <= n <= 8000*m:
        raise ArithmeticError('Full-width gcd pattern or modulus bounds failed')
    return dict(h=999, auxiliary_prime=1009, period_bits=period.bit_length(),
                input='1 + period*(floor(2^2047/period)+1), a chosen wheel unit',
                input_bits=n.bit_length(), modulus_bits=m.bit_length(),
                selection_gcds=1+len(rejected), first_rough_neighbours=neighbours,
                lift_gcds_compared=len(indices), coprime_indices=units)


def divisors_in_window(n, m, target, odd_only, work):
    """The smaller entry obeys sqrt(target/2) < x <= sqrt(target)."""
    first = max(2, isqrt(target//2)+1)
    step = 2 if odd_only else 1
    if odd_only and first % 2 == 0:
        first += 1
    pairs = []
    for x in range(first, isqrt(target)+1, step):
        work['divisions'] += 1
        y, rem = divmod(target, x)
        if rem == 0 and y < m and 4*n <= (x+y)**2 and 2*(x+y)**2 < 9*n:
            if odd_only and not pairs:
                work['divisions_to_first'] = work['divisions']
            pairs.append((x, y))
    return pairs


def wheel_trial(n, period, allowed):
    """Use gcd(N, period)=1 to skip all nonunit trial divisors from the outset."""
    first = isqrt(n//2)+1
    stop = isqrt(n)+1
    hits = []
    divisions = 0
    lookups = 0
    for x in range(first if first % 2 else first+1, stop, 2):
        lookups += 1
        if x % period in allowed:
            divisions += 1
            if n % x == 0:
                hits.append((x, divisions, lookups))
    if len(hits) != 1:
        raise ArithmeticError(f'Expected a unique wheel trial hit at {n}')
    x, to_hit, to_hit_lookups = hits[0]
    return x, dict(wheel_divisions=divisions, wheel_lookups=lookups,
                   wheel_divisions_to_first=to_hit, wheel_lookups_to_first=to_hit_lookups)


def check(n, setup, allowed):
    m, rejected = select(n, setup)
    h, period = setup['h'], setup['period']
    first, last = -((n-1)//(9*m)), (n-1)//(8*m)
    offset_range = range(-period//2, period//2)
    unit_offsets = check_pattern(n, m, setup, offset_range)
    if unit_offsets != len(allowed):
        raise ArithmeticError('Wrong number of units in a full period')
    work = Counter(products=1, selection_gcds=1+len(rejected), selection_factor_hits=len(rejected),
                   modulus_below_original_cutoff=int(8*m<n), modulus_in_scaled_interval=int(8*h*m<=n),
                   validation_period_gcds=len(offset_range), validation_period_units=unit_offsets)
    unfiltered, screened = Counter(), Counter()
    lifts, pairs, survivors = [], set(), set()
    for j in range(first, last+1):
        target = n+j*m
        d = gcd(target, period)
        found = divisors_in_window(n, m, target, False, unfiltered)
        pairs.update(found)
        lifts.append(dict(index=j, product=target, wheel_gcd=d, pairs=[list(z) for z in found]))
        if d == 1:
            work['coprime_lifts'] += 1
            survivors.update(divisors_in_window(n, m, target, target % 2 == 1, screened))
        if abs(j) > h or (d == 1) != (j == 0):
            raise ArithmeticError(f'Lift cover failed at {n}, {m}, {j}')
    supplied = direct_pairs(n, m)
    exact = {(x, y) for x, y in supplied if x*y == n}
    factor, trial = odd_trial(n)
    wheel_factor, wheel_work = wheel_trial(n, period, allowed)
    if wheel_factor != factor:
        raise ArithmeticError(f'Wheel and odd trial disagree at {n}')
    work.update(wheel_work)
    if (pairs != supplied or survivors != exact or exact != {(factor, n//factor)} or
            screened['divisions'] != trial['odd_interval_candidates'] or
            screened['divisions_to_first'] != trial['ascending_divisibility_checks']):
        raise ArithmeticError(f'Independent pair or search-cost comparison failed at {n}, {m}')
    work.update(lift_gcds=len(lifts), matched_pairs=len(pairs),
                supplied_pair_product_equalities=len(supplied), surviving_pairs=len(survivors),
                unfiltered_divisions=unfiltered['divisions'], screened_divisions=screened['divisions'],
                screened_divisions_to_first=screened['divisions_to_first'],
                direct_odd_candidates=trial['odd_interval_candidates'],
                direct_ascending_divisions=trial['ascending_divisibility_checks'],
                direct_descending_divisions=trial['descending_divisibility_checks'])
    return dict(product=str(n), h=h, modulus=m, rejected_selection_gcds=rejected,
                lifts=lifts, recovered=list(map(str, sorted(exact)[0])), work=dict(work))


def prime_lift_control():
    n, m = 4453, 139
    # This supplied modulus is below the selected-modulus guarantee at H=3.
    row = check_matched_divisors(n, m)
    first, last = row['index_range']
    rough = [j for j in range(first, last+1) if gcd(n+j*m, 30) == 1]
    lifted = n+4*m
    if ((m-n) % 6 or (2*m-n) % 5 or rough != [0, 4] or lifted not in primes_through(lifted)
            or any(pair['index'] == 4 for pair in row['pairs'])):
        raise ArithmeticError('The prime product at the first off-center index should have no pair')
    return dict(product=str(n), supplied_modulus=m, h=3, index_range=row['index_range'],
                coprime_indices=rough, prime_at_index_four=lifted, matched_pairs=row['pairs'])


def study():
    primes = [p for p in primes_through(127) if p >= 41]
    cohort = [(p, q) for p in primes for q in primes if p < q < 2*p]
    totals, controls = [], []
    for setup in (wheel(3, 5), wheel(4, 7)):
        counts = Counter()
        allowed = {i for i in range(setup['period']) if gcd(i, setup['period']) == 1}
        period = setup['period']
        indices = range(-period//2, period//2)
        for n in allowed:
            m = setup['crt_multiplier']*n % period
            if check_pattern(n, m, setup, indices) != len(allowed):
                raise ArithmeticError('Incorrect unit count for a product residue')
        for p, q in cohort:
            row = check(p*q, setup, allowed)
            if row['recovered'] != [str(p), str(q)]:
                raise ArithmeticError(f'Failed reference factor check at {p*q}')
            counts.update(row['work'])
            if (row['h'], p*q) in ((3, 12827), (4, 5353)):
                controls.append(row)
        totals.append(dict(wheel=setup, work=dict(counts),
                           first_rough_neighbours=first_rough_neighbours(setup),
                           validation_unit_input_residues=len(allowed),
                           validation_all_class_gcds=len(indices)*len(allowed)))
        if setup['h'] == 3:
            # The initial representative shares a prime with this extra product.
            extra = check(62113, setup, allowed)
            if extra['rejected_selection_gcds'] != [179] or extra['recovered'] != ['179', '347']:
                raise ArithmeticError('Expected the initial eligibility gcd to supply a factor')
            controls.append(extra)
    return dict(scope='All distinct prime pairs with 41 <= p < q <= 127 and q < 2p, at H=3 and H=4. The extra control 62113 is outside these totals.',
                costs='Unfiltered division visits every integer in each balanced lift interval. Screening checks a gcd per lift then visits odd trial divisors of the surviving product. Direct trial division starts from the same public balance bounds. The wheel trial works directly on N. Its reusable unit table costs one small gcd per residue of the period, and each visited odd x takes one lookup. Equality checks start with already supplied candidate pairs. Counts exclude the independent validation enumerations and are not elapsed times.',
                cohort=totals, controls=controls, supplied_modulus_control=prime_lift_control(),
                full_width_gcd_pattern=full_width_pattern())


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Rough lift results differ from the reviewed fixture')
    selections = sum(row['work']['products'] for row in result['cohort'])
    width_checks = result['full_width_gcd_pattern']['lift_gcds_compared']
    print(f"Verified {selections} selections, {len(result['controls'])} selection controls, one supplied-modulus control and {width_checks} full-width lift gcds.")
