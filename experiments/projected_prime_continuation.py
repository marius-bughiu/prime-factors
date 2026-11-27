"""Replay the bounded two-stage comparison on the three published weighted-crowding inputs."""
import json
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.reduced_smooth_readout import blocks
from experiments.shared_smooth_powers import batch_factor, window_power
from scripts.factor import primes_through


FIXTURES = Path(__file__).resolve().parents[1] / 'benchmarks' / 'weighted-crowding.json'
CASES = ('weighted-crowding-constructed-2048', 'weighted-crowding-fresh-2048',
         'weighted-crowding-crossed-2048')


def cumulative(n, start, plan):
    work = dict(squares=0, multiplies=0, powers=0, gcds=1)
    previous = z = start
    for prime, exponent in plan:
        previous = z
        z = window_power(z, exponent, n, work)
        work.update(powers=work['powers']+1, last_prime=prime)
        if z == 1:
            break
    work['identity'] = z == 1
    divisor = gcd((previous if work['identity'] else z)-1, n)
    work['divisor'] = str(divisor) if 1 < divisor < n else None
    return z, work


def independent(n, z, primes):
    work = dict(squares=0, multiplies=0, powers=1, batch_gcds=0)
    previous = primes[0]
    term = window_power(z, previous, n, work)
    values = [term]
    gaps = {}
    for prime in primes[1:]:
        gap = prime-previous
        if gap not in gaps:
            gaps[gap] = window_power(z, gap, n, work)
            work['powers'] += 1
        term = term*gaps[gap] % n
        work['multiplies'] += 1
        values.append(term)
        previous = prime
    divisor = batch_factor(n, values, work)
    work.update(primes_tested=len(primes), divisor=str(divisor) if divisor else None,
                gcds=work.pop('batch_gcds'))
    return work


def run(n, ordinary=False):
    initial = dict(squares=0, multiplies=0, powers=1, gcds=1)
    if gcd(2, n) != 1:
        raise ValueError('these pinned inputs require base 2 to be a unit')
    start = window_power(2, n-1, n, initial)
    if start == 1:
        raise ValueError('these pinned inputs require a nonidentity projected base')
    first = list(blocks(100, 1024))
    rest = [(p, e) for p, e in blocks(1000, 1024) if p > 100]
    primes = [p for p, _ in rest]
    z, stage_one = cumulative(n, start, first)
    if stage_one['identity'] or stage_one['divisor']:
        raise ValueError('the pilot compares continuations after a stage-one gcd of one')
    result = dict(projection=initial, stage_one=stage_one,
                  independent=independent(n, z, primes),
                  cumulative_once=cumulative(n, z, [(p, p) for p in primes])[1],
                  full_powers=cumulative(n, z, rest)[1])
    if ordinary:
        plain, result['ordinary_stage_one'] = cumulative(n, 2, first)
        result['ordinary_independent'] = independent(n, plain, primes)
    return z, result


def main():
    from scripts.benchmark import run_case

    cases = {c['id']: c for c in json.loads(FIXTURES.read_text())}
    outcomes = {}
    for case_id in CASES:
        outcomes[case_id] = run(int(cases[case_id]['n']), ordinary=case_id == CASES[0])
    # Replay the registered factorization certificate only after completing every search.
    positive = cases[CASES[0]]
    with TemporaryDirectory() as directory:
        certified = run_case(positive, 'weighted-crowding', Path(directory))
    if not certified['verified']:
        raise ValueError('the original prime factorization certificate failed')
    factors = sorted(map(int, certified['factors']))
    z, observed = outcomes[CASES[0]]
    primes = [p for p in primes_through(1000) if p > 100]
    matches = [[ell for ell in primes if pow(z, ell, factor) == 1] for factor in factors]
    if matches != [[521], [557]]:
        raise ValueError('the observed local matches differ from the pinned example')
    for case_id, (_, result) in outcomes.items():
        for method in ('independent', 'cumulative_once', 'full_powers'):
            expected = str(factors[0]) if case_id == CASES[0] else None
            if result[method]['divisor'] != expected:
                raise ValueError(f'{case_id} {method} disagrees with the expected outcome')
        print(json.dumps(dict(case=case_id, runs=result)))
    if observed['ordinary_stage_one']['divisor'] or observed['ordinary_independent']['divisor']:
        raise ValueError('the ordinary comparison unexpectedly split the example')
    print(json.dumps(dict(certificate='PrimeFactors.Generated.weightedCrowdingSplit',
                          prime_factors=certified['factors'], local_matches=matches)))


if __name__ == '__main__':
    main()
