"""Exact finite checks for estimating unsigned mask counts and their additive transform."""

import json
from collections import Counter
from itertools import combinations
from math import comb, gcd, isqrt
from pathlib import Path

from experiments.mixed_ratio_heights import jacobi
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/changed-mask-frequency.json'


def sample_thresholds(n, p, q, d, hits):
    """Return the first sample size with RMS prime-sum error strictly below one."""
    h = len(hits)
    if h != d*(p+q-2-d):
        raise ArithmeticError(f'Unexpected prefix count for {n}, d={d}')
    # Center the N-scaled indicator at H and sum over its measured population.
    variance = (h*(n-h)**2+(n-h)*h**2)//n
    if variance != h*(n-h):
        raise ArithmeticError('Inconsistent population variance')
    independent = variance//(d*d)+1
    distinct = variance*n//(variance+d*d*(n-1))+1
    if not (d*d*(independent-1) <= variance < d*d*independent):
        raise ArithmeticError('Incorrect independent sampling threshold')
    def distinct_passes(k):
        return variance*(n-k) < d*d*k*(n-1)
    if not (1 <= distinct <= n and distinct_passes(distinct) and not distinct_passes(distinct-1)):
        raise ArithmeticError('Incorrect distinct sampling threshold')
    return dict(d=d, changed=h, count_variance=variance, first_iid_draws=independent,
                first_distinct_draws=distinct, unseen_at_first_distinct=n-distinct)


def small_sampling_check(hits, n):
    """Exhaust the sample sets at N=15 independently of the variance derivation."""
    h = len(hits)
    for k in range(1, n+1):
        squared = sum((n*sum(t in hits for t in subset)-k*h)**2
                      for subset in combinations(range(n), k))
        if squared*(n-1) != comb(n, k)*k*h*(n-h)*(n-k):
            raise ArithmeticError(f'Distinct subset census failed for {k} draws')
    iid = sum((n*((a in hits)+(b in hits))-2*h)**2 for a in range(n) for b in range(n))
    if iid != n*n*2*h*(n-h):
        raise ArithmeticError('Two independent draws disagree with exact variance')


def prefix_census(n, p, q):
    limit = (p-1)//2
    public_length = isqrt(n//2)//2
    thresholds = []
    singleton = set()
    hits = set()
    plain = [jacobi(t, n) for t in range(n)]
    values = [1]*n
    for d in range(1, limit+1):
        for t in range(n):
            values[t] = values[t]*(t-d*d) % n
            if jacobi(t*values[t]*values[t], n) != plain[t]:
                hits.add(t)
        if d == 1:
            singleton = hits.copy()
        thresholds.append(sample_thresholds(n, p, q, d, hits))
    if n == 15:
        small_sampling_check(singleton, n)
    return singleton, [thresholds[j-1] for j in sorted({1, public_length, limit})]


def fourier_check(n, p, q, hits):
    """Verify every coefficient exactly as an identity at a primitive Nth root."""
    # Identify the mixed CRT idempotents independently of the observed mask scores.
    mixed = [x for x in range(2, n) if x*x % n == x]
    if len(mixed) != 2 or sum(mixed) != n+1:
        raise ArithmeticError(f'Unexpected idempotents at {n}')
    e = mixed[0]
    if {gcd(x, n) for x in mixed} != {p, q}:
        raise ArithmeticError(f'Idempotent divisors disagree at {n}')
    half = pow(2, -1, n)
    root = (2*e-1) % n
    classes = Counter()
    for k in range(n):
        g = gcd(k, n)
        classes[g] += 1
        # Coefficients of sum over changed t of X^(kt), with X^N = 1.
        difference = Counter(k*t % n for t in hits)
        # Subtract the proposed answer: the two lines collapse only at the
        # corresponding nonunit frequencies; the three excluded points remain.
        for exponent in (k, k*e % n, k*(1-e) % n):
            difference[exponent] += 1
        for r in (p, q):
            if k % r == 0:
                difference[k] -= r
        # Each uncollapsed geometric line vanishes after multiplying it by
        # 1-X^step. Nonzero shifts make those factors nonzero at a primitive root.
        for step in (k*p % n, k*q % n):
            if step:
                old = {i: value for i, value in difference.items() if value}
                difference = Counter(old)
                for i, value in old.items():
                    difference[(i+step) % n] -= value
        if any(difference.values()):
            raise ArithmeticError(f'Group-ring cancellation failed at {n}, frequency {k}')
        if g == 1:
            t = half*k % n
            rotated = {(k*x-t) % n for x in mixed}
            if rotated != {t*root % n, -t*root % n}:
                raise ArithmeticError(f'Cosine phase disagrees at {n}, frequency {k}')
    return dict(mixed_idempotents=mixed, mixed_square_root=root,
                frequency_counts_by_gcd={str(g): c for g, c in sorted(classes.items())})


def square_draws(n, p, q, hits):
    """Sample t=x² for uniform x and classify all singleton changes."""
    total = proper = mixed = trivial = 0
    for x in range(n):
        if x*x % n not in hits:
            continue
        total += 1
        d = gcd(x*x-1, n)
        if d in (p, q):
            proper += 1
        elif d == n and gcd(x-1, n) in (p, q):
            mixed += 1
        elif x in (1, n-1):
            trivial += 1
        else:
            raise ArithmeticError(f'Unexplained square draw at {n}, root {x}')
    if total != (p-1)*(q-1)-(p-3)*(q-3) or mixed != 2 or trivial != 2:
        raise ArithmeticError(f'Square-draw partition disagrees at {n}')
    return dict(changed_square_draws=total, proper_gcd_of_square_minus_one=proper,
                mixed_roots_requiring_gcd_of_x_minus_one=mixed, trivial_roots=trivial)


def study():
    primes = [p for p in primes_through(31) if p % 2]
    pairs = [(p, q) for q in primes for p in primes if p < q < 2*p and q.bit_length() >= 3]
    pairs.append((37, 59))
    totals = Counter()
    examples = []
    for p, q in pairs:
        n = p*q
        hits, thresholds = prefix_census(n, p, q)
        fourier = fourier_check(n, p, q, hits)
        squares = square_draws(n, p, q, hits)
        totals.update(products=1, exact_frequencies=n, eligible_prefix_lengths=(p-1)//2,
                      ordinary_changed=len(hits), square_changed=squares['changed_square_draws'])
        if n in (15, 299, 589, 2183):
            examples.append(dict(product=str(n), reference_primes=[str(p), str(q)],
                                 sampling=thresholds, fourier=fourier, square_sampling=squares))
    return dict(population='All distinct odd p < q < 2p with q of 3–5 bits, plus 37×59.',
                error='Each threshold is the first positive draw count with RMS error below one in the even prime sum.',
                transform='Exact integer cyclic-polynomial cancellations at every frequency.',
                totals=dict(totals), examples=examples)


if __name__ == '__main__':
    actual = study()
    if actual != json.loads(FIXTURE.read_text()):
        raise SystemExit('Unsigned sampling and Fourier checks disagree with the recorded fixture')
    print(f"Checked {actual['totals']['exact_frequencies']} exact additive coefficients on "
          f"{actual['totals']['products']} products.")
