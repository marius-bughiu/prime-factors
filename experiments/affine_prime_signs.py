"""Direct prime census for the affine Legendre tests and reproducible public label panels."""

import argparse
from hashlib import sha256, shake_256
import json
from math import isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.many_character_window import cases as full_size_cases
from experiments.mixed_ratio_heights import jacobi
from experiments.split_prime_holdout import certificate, interval_primes
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'research/affine-prime-signs.json'
DOMAIN = b'affine-prime-signs-v1'
METHODS = ('direct', 'streamed_signs', 'singleton_census')
REPEATS = 6


def draw_labels(n, count):
    """Separate label and rejection counters; mask to n.bit_length() before rejection."""
    bits = n.bit_length()
    size = (bits+7)//8
    prefix = DOMAIN+b'\0'+size.to_bytes(2,'big')+n.to_bytes(size,'big')
    mask = (1<<bits)-1
    labels = []
    attempts = 0
    for index in range(count):
        counter = 0
        while True:
            digest = shake_256(prefix+index.to_bytes(4,'big')+counter.to_bytes(4,'big')).digest(size)
            value = int.from_bytes(digest,'big') & mask
            attempts += 1
            if value < n:
                labels.append(value)
                break
            counter += 1
    return labels, attempts


def digest_labels(n, labels):
    size = (n.bit_length()+7)//8
    return sha256(b''.join(x.to_bytes(size,'big') for x in labels)).hexdigest()


def accepted(discriminant, prime):
    """Euler's criterion. Both zero and a negative Legendre symbol fail the test."""
    return pow(discriminant % prime, (prime-1)//2, prime) == 1


def verified_pair(n, prime):
    other, remainder = divmod(n,prime)
    if remainder or prime <= 1 or other <= 1:
        return None
    return [str(prime),str(other)]


def trial(n, bits, method):
    primes_through.cache_clear()
    start_cpu, start_wall = process_time_ns(), perf_counter_ns()

    def clocks():
        return dict(cpu_ns=process_time_ns()-start_cpu, wall_ns=perf_counter_ns()-start_wall)

    lo = max(1 << (bits-1),(n-1)//((1<<bits)-1)+1)
    hi = isqrt(n)
    labels, attempts = draw_labels(n,64) if method != 'direct' else ([],0)
    ds = [1-4*n*r for r in labels]
    result = dict(bounds=[lo,hi], label_count=len(labels), random_word_attempts=attempts)
    if method == 'singleton_census':
        remaining = list(interval_primes(lo,hi))
        sizes = [len(remaining)]
        checks = 0
        unique_at = unique_checks = None
        pair = None
        for k, delta in enumerate(ds,1):
            checks += len(remaining)
            remaining = [p for p in remaining if accepted(delta,p)]
            sizes.append(len(remaining))
            if len(remaining) == 1 and unique_at is None:
                unique_at, unique_checks = k, checks
                pair = verified_pair(n,remaining[0])
                if pair is None:
                    raise ArithmeticError('unique survivor does not divide the product')
                when_unique = clocks()
        if unique_at is None:
            raise ArithmeticError('the pinned panel did not reach uniqueness')
        timing = dict(first=when_unique, full=clocks())
        return dict(result, primes_sieved=sizes[0], survivors_by_prefix=sizes,
                    unique_after=unique_at, checks_to_unique=unique_checks, checks_full=checks,
                    division_tests=1, pair=pair, digest=digest_labels(n,labels)), timing

    visited = checks = divisions = 0
    for p in interval_primes(lo,hi):
        visited += 1
        for delta in ds:
            checks += 1
            if not accepted(delta,p):
                break
        else:
            divisions += 1
            pair = verified_pair(n,p)
            if pair is not None:
                timing = dict(first=clocks())
                return dict(result, primes_visited=visited, legendre_checks=checks,
                            division_tests=divisions, pair=pair), timing
    raise ArithmeticError('the search failed to factor a pinned product')


def small_cases():
    data = json.loads((ROOT / 'research/split-prime-holdout.json').read_text())
    return [(c['bits'],c['sample'],int(c['n'])) for c in data['cases']]


def small_report(bits, sample, n):
    methods = {}
    times = {m:[] for m in METHODS}
    for rep in range(REPEATS):
        order = METHODS[rep%3:]+METHODS[:rep%3]
        if rep >= 3:
            order = order[::-1]
        for m in order:
            result, timing = trial(n,bits,m)
            if m in methods and methods[m] != result:
                raise ArithmeticError('changed deterministic arithmetic in a repeated run')
            methods[m] = result
            times[m].append(timing)
    pair = methods['direct']['pair']
    if any(methods[m]['pair'] != pair for m in METHODS):
        raise ArithmeticError('the methods disagree on the public product')
    for m in METHODS:
        methods[m]['median_times'] = {phase:{clock:int(median(t[phase][clock] for t in times[m]))
                                             for clock in ('cpu_ns','wall_ns')}
                                      for phase in times[m][0]}
    return dict(bits=bits,sample=sample,n=str(n),methods=methods,certificate_sha256=certificate(n,pair))


def large_report(case):
    n = int(case['n'])
    samples = []
    for _ in range(REPEATS):
        cpu, wall = process_time_ns(), perf_counter_ns()
        labels, attempts = draw_labels(n,1100)
        samples.append((process_time_ns()-cpu,perf_counter_ns()-wall))
    return dict(id=case['id'],n=str(n),product_bits=n.bit_length(),labels=len(labels),
                random_word_attempts=attempts,distinct_labels=len(set(labels)),sha256=digest_labels(n,labels),
                median_label_cpu_ns=int(median(t[0] for t in samples)),
                median_label_wall_ns=int(median(t[1] for t in samples)),
                candidate_primes_visited=0,legendre_checks=0,division_tests=0)


def nonsquare_report(bits, sample, n):
    """Cold, single-run comparison on the whole odd nonsquare interval, with no primality sieve."""
    lo = max(1 << (bits-1), (n-1)//((1<<bits)-1)+1)
    hi = isqrt(n)
    odds = range(lo|1, hi+1, 2)

    def candidates():
        return (x for x in odds if isqrt(x)**2 != x)

    def elapsed(cpu, wall):
        return dict(cpu_ns=process_time_ns()-cpu, wall_ns=perf_counter_ns()-wall)

    methods = {}
    for name in ('direct', 'streamed_jacobi'):
        cpu, wall = process_time_ns(), perf_counter_ns()
        labels = draw_labels(n,64)[0] if name == 'streamed_jacobi' else []
        ds = [1-4*n*r for r in labels]
        checks = divisions = 0
        for visited, x in enumerate(candidates(), 1):
            for delta in ds:
                checks += 1
                if jacobi(delta,x) != 1:
                    break
            else:
                divisions += 1
                pair = verified_pair(n,x)
                if pair is not None:
                    odd_seen = (x-odds.start)//2+1
                    methods[name] = dict(pair=pair, odd_square_tests=odd_seen, nonsquares_visited=visited,
                                         squares_skipped=odd_seen-visited, jacobi_checks=checks,
                                         division_tests=divisions, time=elapsed(cpu,wall))
                    break
        else:
            raise ArithmeticError('no proper factor in direct search')

    cpu, wall = process_time_ns(), perf_counter_ns()
    labels, _ = draw_labels(n,64)
    ds = [1-4*n*r for r in labels]
    remaining = list(candidates())
    sizes = [len(remaining)]
    checks = 0
    for delta in ds:
        checks += len(remaining)
        remaining = [x for x in remaining if jacobi(delta,x) == 1]
        sizes.append(len(remaining))
        if len(remaining) <= 1:
            break
    prefix = len(sizes)-1
    passing = [pair for x in remaining if (pair := verified_pair(n,x)) is not None]
    time_to_split = elapsed(cpu,wall)
    tail_checks = 0
    for delta in ds[prefix:]:
        tail_checks += len(remaining)
        remaining = [x for x in remaining if jacobi(delta,x) == 1]
    if passing != [methods['direct']['pair']] or methods['streamed_jacobi']['pair'] != passing[0]:
        raise ArithmeticError('the nonsquare lower-factor searches disagree')
    methods['census'] = dict(pair=passing[0], odd_square_tests=len(odds), squares_skipped=len(odds)-sizes[0],
                             survivors_by_prefix=sizes, unique_after=prefix if sizes[-1] == 1 else None,
                             jacobi_checks_to_split=checks, division_tests=sizes[-1], time=time_to_split,
                             additional_jacobi_checks=tail_checks, survivors_after_64=len(remaining))
    return dict(bits=bits,sample=sample,n=str(n),lower=lo,upper=hi,labels_sha256=digest_labels(n,labels),
                methods=methods,certificate_sha256=certificate(n,passing[0]))


def deterministic(value):
    if isinstance(value,list):
        return [deterministic(x) for x in value]
    if isinstance(value,dict):
        return {k:deterministic(v) for k,v in value.items()
                if k not in ('median_times','median_label_cpu_ns','median_label_wall_ns','platform','time')}
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='replace the recorded report')
    parser.add_argument('--nonsquares',action='store_true',help='check just the new odd nonsquare census')
    args = parser.parse_args()
    ns_cases = [nonsquare_report(*row) for row in small_cases()]
    nonsquares = dict(repetitions=1, timing='single run from the shared public endpoints through verified division; includes integer-square checks, candidate construction and label generation; excludes Lean',
                      cases=ns_cases)
    if args.nonsquares:
        saved = json.loads(RESULTS.read_text())
        if args.write:
            saved['odd_nonsquares'] = nonsquares
            RESULTS.write_text(json.dumps(saved,indent=2)+'\n')
        elif deterministic(saved['odd_nonsquares']) != deterministic(nonsquares):
            raise ArithmeticError('the odd nonsquare census changed')
        for row in ns_cases:
            c = row['methods']['census']
            print(row['bits'],c['survivors_by_prefix'][0],'nonsquares;',c['unique_after'],'labels to singleton')
        return
    report = dict(domain=DOMAIN.decode(), sampling='deterministic SHAKE256, separate index and rejection counters',
                  encoding='domain, NUL, 2-byte unsigned length of N, fixed-width unsigned N, 4-byte index, 4-byte attempt; all integers big endian',
                  digest='SHA-256 of the sampled labels in draw order, each padded to the byte length of N',
                  interpretation='The probability theorem assumes independent uniform draws. These published seeded labels are a reproducible experiment.',
                  timing='six method orders; cold prime cache; times to verified division include label generation and sieve, and exclude Lean',
                  platform=dict(python=platform.python_version(),machine=platform.machine(),os=platform.system()),
                  small=[small_report(*row) for row in small_cases()], large=[large_report(c) for c in full_size_cases()],
                  odd_nonsquares=nonsquares)
    if args.write:
        RESULTS.write_text(json.dumps(report,indent=2)+'\n')
    elif deterministic(report) != deterministic(json.loads(RESULTS.read_text())):
        raise ArithmeticError('counts, digests, or certified factors disagree with the stored panel')
    for row in report['small']:
        w = row['methods']['singleton_census']
        print(row['bits'],w['survivors_by_prefix'][0],'primes;',w['unique_after'],'labels;',w['checks_to_unique'],'checks;',*w['pair'])
    for row in report['large']:
        print(row['id'],row['labels'],'labels:',row['sha256'])


if __name__ == '__main__':
    main()
