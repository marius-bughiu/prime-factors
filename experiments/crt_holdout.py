"""Compare three fixed public-product searches on a predeclared 79-bit sample."""

import argparse
from hashlib import shake_256
import json
from math import isqrt
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.crt_square_norms import search as crt_search
from experiments.pell_relations import search as cf_search
from scripts import factor as proof

SEED = b"crt-screen-holdout-v1"
COUNT = 64


def draw_prime(seed, side, attempt, trial_primes):
    counter = 0
    while True:
        message = seed + b"\0" + side + attempt.to_bytes(8, 'big') + counter.to_bytes(8, 'big')
        candidate = int.from_bytes(shake_256(message).digest(5), 'big') | (1 << 39) | 1
        limit = isqrt(candidate)
        for p in trial_primes:
            if p > limit:
                return candidate
            if candidate % p == 0:
                break
        else:
            return candidate
        counter += 1


def draw_sample(seed=SEED, count=COUNT):
    """Certify primality of each proposed 40-bit prime by exact trial division."""
    trial_primes = proof.primes_through(1 << 20)
    products = set()
    attempt = 0
    while len(products) < count:
        p = draw_prime(seed, b'p', attempt, trial_primes)
        q = draw_prime(seed, b'q', attempt, trial_primes)
        attempt += 1
        n = p * q
        if p == q or n.bit_length() != 79 or n in products:
            continue
        products.add(n)
        yield attempt - 1, n, sorted((p, q))


def run_methods(n):
    """Each search receives just n and its public parameters."""
    return {
        'A': crt_search(n, prime_count=12, threshold_bits=-4, hit_cap=1001, subset_size=3),
        'B': crt_search(n, prime_count=12, threshold_bits=-2, hit_cap=10000, subset_size=3),
        'C': cf_search(n, multiplier=1, max_steps=5138),
    }


def record(n, work):
    f = work['factor']
    if f is not None and not (1 < f < n and n % f == 0):
        raise ValueError('search returned an invalid divisor')
    keys = ['windows', 'total_windows', 'interval_hits', 'materialized_hits', 'visited_hits',
            'hit_cap_reached', 'square_tests', 'steps', 'rows', 'private_pruned',
            'dependencies', 'tested']
    return dict(outcome=work['outcome'],
                factors=[] if f is None else [str(x) for x in sorted((f, n // f))],
                remaining=[str(n)] if f is None else [],
                work={key: work[key] for key in keys if key in work})


def summarize(cases):
    patterns = {}
    for row in cases:
        pattern = ''.join(key for key in 'ABC' if row['methods'][key]['factors']) or 'none'
        patterns[pattern] = patterns.get(pattern, 0) + 1
    return dict(sorted(patterns.items()))


def evaluate():
    cases = []
    for attempt, n, primes in draw_sample():
        methods = {key: record(n, val) for key, val in run_methods(n).items()}
        expected = [str(p) for p in primes]
        for run in methods.values():
            if run['factors'] and run['factors'] != expected:
                raise ValueError('incorrect factorization')
        cases.append(dict(attempt=attempt, n=str(n), expected_factors=expected, methods=methods))
    return dict(seed=SEED.decode(), count=COUNT, patterns=summarize(cases), cases=cases)


def verify_cases(cases, directory):
    """Replay one exact Lean prime-factor certificate for each generated product."""
    directory.mkdir(parents=True, exist_ok=True)
    # A 40-bit prime's predecessor can be completely trial-factored through 2^20.
    # This only extends the proof generator's trial table in this verification process.
    original_primes = proof.TRIAL_PRIMES
    try:
        proof.TRIAL_PRIMES = proof.primes_through(1 << 20)
        proof.prime_witness.cache_clear()
        for i, case in enumerate(cases):
            n = int(case['n'])
            factors = list(map(int, case['expected_factors']))
            source = directory / f'holdout-{i:02d}.lean'
            source.write_text(proof.render_certificate(n, factors))
            proof.verify_file(source)
    finally:
        proof.TRIAL_PRIMES = original_primes
        proof.prime_witness.cache_clear()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'research' / 'crt-holdout.json')
    parser.add_argument('--verify', action='store_true',
                        help='certify both hidden primes and every product in the saved report')
    args = parser.parse_args()
    report = evaluate()
    if args.verify:
        verify_cases(report['cases'], ROOT / 'build' / 'crt-holdout')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['patterns']))


if __name__ == '__main__':
    main()
