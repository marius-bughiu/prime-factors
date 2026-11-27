"""Test one unfiltered square for every unordered pair of weights from 512 to 575."""
import argparse
import json
from itertools import combinations
from math import gcd, isqrt
from time import perf_counter

from scripts.factor import TRIAL_LIMIT, prime_witness, primes_through, render_certificate, verify_file


def search(n):
    """Use only n. Stop at the first proper upper-root gcd."""
    if n < 2:
        raise ValueError('expected a product of at least two')
    squares = 0
    for tests, (a, b) in enumerate(combinations(range(512, 576), 2), 1):
        lower = 4*a*b*n
        s = isqrt(lower-1)+1
        d = isqrt(s*s-lower)
        if d*d != s*s-lower:
            continue
        squares += 1
        divisor = gcd(n, (s+d)//2)
        if 1 < divisor < n:
            return divisor, dict(tests=tests, integer_roots=2*tests, square_hits=squares,
                                 weights=[a,b], trace=str(s), root=str(d))
    return None, dict(tests=tests, integer_roots=2*tests, square_hits=squares,
                      weights=None, trace=None, root=None)


def construct():
    """Find the first p=521*2^512*k+1, q=557*2^512*k+1 with two prime witnesses."""
    grid = 1 << 512
    lower = 3*(1 << 1024)//4
    first = (lower-1 + 521*grid-1)//(521*grid)
    small = primes_through(1000)
    for offset in range(1_000_000):
        k = first + offset
        p, q = 521*grid*k+1, 557*grid*k+1
        if any(p % r == 0 or q % r == 0 for r in small):
            continue
        if prime_witness(p, 2) is not None and prime_witness(q, 2) is not None:
            return dict(offset=offset, k=str(k), n=str(p*q), factors=[str(p),str(q)])
    raise ValueError('bounded prime-pair construction exhausted')


def weighted_crowding_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    divisor, work = search(n)
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, None, elapsed, 'weighted_crowding', work)
    if divisor is None:
        return result
    start = perf_counter()
    p, q = sorted((divisor, n//divisor))
    a,b = work['weights']
    s,d = int(work['trace']),int(work['root'])
    limit = case.get('certificate_trial_limit', TRIAL_LIMIT)
    source = render_certificate(n, [p,q], certificate_trial_limit=limit)
    pool_claim = ''
    if case.get('construction'):
        pool_claim = f''' ∧
      (3*2^1024/4≤{p} ∧ {p}<{q} ∧ {q}≤7*2^1024/8 ∧
       ({b}*{p}-384*2^1024)/2^516=({a}*{q}-384*2^1024)/2^516)'''
    source += f'''
namespace PrimeFactors.Generated
private abbrev n : ℕ := {n}
private abbrev s : ℕ := {s}
private abbrev d : ℕ := {d}
theorem weightedCrowdingSplit :
    ExactFactorization n [{p},{q}] ∧
      (512≤{a} ∧ {a}<{b} ∧ {b}<576 ∧
      (s-1)^2 < 4*{a}*{b}*n ∧ s^2=4*{a}*{b}*n+d^2 ∧
      n.gcd ((s+d)/2)={divisor} ∧ 1<{divisor} ∧ {divisor}<n{pool_claim}) :=
  ⟨factorization, by decide +kernel⟩
#print axioms weightedCrowdingSplit
end PrimeFactors.Generated
'''
    proof.write_text(source)
    check = perf_counter()
    verify_file(proof, 'PrimeFactors.Generated.weightedCrowdingSplit')
    result.update(verified=True, status='complete', factors=[str(p),str(q)], remaining=[],
                  verification_seconds=perf_counter()-check, certificate_seconds=perf_counter()-start)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--construct', action='store_true', help='rebuild the deliberately ratio-matched prime pair')
    group.add_argument('--n', type=int, help='try the menu on a supplied product')
    args = parser.parse_args()
    if args.construct:
        result = construct()
    else:
        divisor, work = search(args.n)
        result = dict(divisor=str(divisor) if divisor else None, **work)
    print(json.dumps(result, indent=2))
