"""Reproduce the fixed complete-search timing panel and its independent inputs."""
import argparse
import hashlib
import json
from math import isqrt
import platform
import sys
from time import perf_counter

from scripts.factor import primes_through
from .factorial_progressions import search as factorial
from .weighted_stride_search import search as weighted


SEED = b'weighted-stride-holdout-v1'
MAX_GIANTS = 262144


def sample_pair(suffix, trial_primes):
    """First 45-bit primes in the two independent side streams."""
    def draw(side):
        counter = 0
        while True:
            message = SEED + b'\0' + side + counter.to_bytes(8, 'big')
            digest = hashlib.shake_256(message).digest(6)
            x = int.from_bytes(digest, 'big') % (1 << 45) | (1 << 44) | 1
            bound = isqrt(x)
            for p in trial_primes:
                if p > bound:
                    return x, counter
                if x % p == 0:
                    break
            counter += 1
    p, i = draw(b'p'+suffix)
    q, j = draw(b'q'+suffix)
    return [p, q], [i, j]


def settings(n):
    lo, hi = 0, 1 << ((n.bit_length()+9)//10)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**10 <= n:
            lo = mid
        else:
            hi = mid
    return (lo+1)//2, max(1,lo*lo//4)


def measure(run, repetitions):
    samples = []
    for _ in range(repetitions):
        start = perf_counter()
        result = run()
        samples.append(round(perf_counter()-start, 6))
    return dict(seconds=samples, factor=str(result['factor']), outcome=result['outcome'],
                complete=result.get('schedule_complete', result.get('interval_complete')),
                work=result['work'])


def compare(repetitions):
    trial_primes = primes_through(1 << 23)
    entries = [('previous-63',6091663632054090929,None), ('previous-79',543283139603355533096543,None)]
    for name, suffix in [('fresh-89-A',b''),('fresh-89-B',b'1')]:
        primes, counters = sample_pair(suffix, trial_primes)
        entries.append((name, primes[0]*primes[1],
                        dict(side_suffix=suffix.decode(), prime_labels=list(map(str,primes)), counters=counters)))
    cases = []
    for name, n, labels in entries:
        k, m = settings(n)
        row = dict(id=name, n=str(n), k=k, baby_steps=m, sampling=labels, measurements={})
        methods = row['measurements']
        if name != 'fresh-89-B':
            methods['factorial_wheel210'] = measure(lambda: factorial(n,None,wheel=210),repetitions)
            methods['weighted_stride1'] = measure(lambda: weighted(n,k,m,MAX_GIANTS,stride=1),repetitions)
        methods['weighted_stride24'] = measure(lambda: weighted(n,k,m,MAX_GIANTS),repetitions)
        cases.append(row)
    return dict(seed=SEED.decode(), repetitions=repetitions, max_giants=MAX_GIANTS, beta=2,
                platform=platform.platform(), machine=platform.machine(), python=sys.version, cases=cases)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repetitions', type=int, default=3)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('--repetitions must be positive')
    print(json.dumps(compare(args.repetitions), indent=2))
