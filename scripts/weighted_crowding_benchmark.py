"""Test the first unfiltered square for each pair in a fixed menu starting at weight 512."""
import argparse
import json
from itertools import combinations
from math import gcd, isqrt
from time import perf_counter

from scripts.factor import TRIAL_LIMIT, fermat_split, prime_witness, primes_through, render_certificate, verify_file


def search(n, weight_count=64):
    """Use only n. Stop at the first proper upper-root gcd."""
    if n < 2:
        raise ValueError('expected a product of at least two')
    if weight_count not in (5, 64):
        raise ValueError('expected five or 64 public weights')
    squares = 0
    for tests, (a, b) in enumerate(combinations(range(512, 512+weight_count), 2), 1):
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


def construct(weight_count=64):
    """Choose the first certifiable pair at the prescribed ratio on the power-of-two grid."""
    a,b = {5: (513,515), 64: (521,557)}[weight_count]
    grid = 1 << 512
    lower = 3*(1 << 1024)//4
    first = (lower-1 + a*grid-1)//(a*grid)
    small = primes_through(1000)
    for offset in range(1_000_000):
        k = first + offset
        p, q = a*grid*k+1, b*grid*k+1
        if any(p % r == 0 or q % r == 0 for r in small):
            continue
        if prime_witness(p, 2) is not None and prime_witness(q, 2) is not None:
            return dict(offset=offset, k=str(k), n=str(p*q), factors=[str(p),str(q)])
    raise ValueError('bounded prime-pair construction exhausted')


def weighted_crowding_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    weight_count = case.get('weight_count', 64)
    divisor, work = search(n, weight_count)
    elapsed = perf_counter()-start
    work['available_tests'] = weight_count*(weight_count-1)//2
    if weight_count == 5:
        # Ten first-label tests cost twenty integer roots when the menu is exhausted.
        # One starting root leaves nineteen consecutive ordinary midpoint tests.
        ordinary_factor, ordinary_tests = fermat_split(n, 19)
        work['ordinary'] = dict(square_tests=ordinary_tests, integer_roots=1+ordinary_tests,
                                found=str(ordinary_factor) if ordinary_factor else None,
                                found_in_ten=ordinary_factor is not None and ordinary_tests <= 10)
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
    upper_weight = 512 + weight_count
    pool_claim = ''
    if case.get('construction'):
        pool_claim = f''' ∧
      (3*2^1024/4≤{p} ∧ {p}<{q} ∧ {q}≤7*2^1024/8 ∧
       ({b}*{p}-384*2^1024)/2^516=({a}*{q}-384*2^1024)/2^516)'''
    if case.get('construction') and weight_count == 5:
        midpoint = isqrt(n-1)+1
        pool_claim += f''' ∧
      (({midpoint}-1)^2<n ∧ n≤{midpoint}^2 ∧ 2*({midpoint}+18)<{p}+{q})'''
    source += f'''
namespace PrimeFactors.Generated
private abbrev n : ℕ := {n}
private abbrev s : ℕ := {s}
private abbrev d : ℕ := {d}
theorem weightedCrowdingSplit :
    ExactFactorization n [{p},{q}] ∧
      (512≤{a} ∧ {a}<{b} ∧ {b}<{upper_weight} ∧
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
    parser.add_argument('--weight-count', type=int, choices=(5,64), default=64,
                        help='number of consecutive weights starting at 512 (default 64)')
    args = parser.parse_args()
    if args.construct:
        result = construct(args.weight_count)
    else:
        divisor, work = search(args.n, args.weight_count)
        result = dict(divisor=str(divisor) if divisor else None, **work)
    print(json.dumps(result, indent=2))
