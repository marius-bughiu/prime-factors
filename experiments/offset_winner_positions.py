"""Locate every winning complete-schedule position using the already published factors."""

import argparse
import json
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.complete_offset_search import slot_count
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]


def winner_positions(n, p, q):
    """Retrospective on a known balanced product of distinct primes, both at least 17."""
    if p*q != n or not 17 <= p < q <= 2*p:
        raise ValueError('expected published distinct balanced prime factors in ascending order')
    t = isqrt(n)
    h = n-t*t
    limit = isqrt(4*h//3)

    def bilinear(x, y):
        return p*x[0]*y[0]-t*(x[0]*y[1]+x[1]*y[0])+q*x[1]*y[1]

    x, y = (1, 0), (0, 1)
    steps = 0
    while True:
        if bilinear(x, x) > bilinear(y, y):
            x, y = y, x
        a, b, c = bilinear(x, x), bilinear(x, y), bilinear(y, y)
        if 2*abs(b) <= a:
            break
        nearest = (2*b+a)//(2*a)
        y = (y[0]-nearest*x[0], y[1]-nearest*x[1])
        steps += 1

    # a*Q(m*x+l*y) = (a*m+b*l)^2+h*l^2. For |l|>=2, Q>=4h/a.
    # For |l|=1 and |m|>=2, |a*m+b*l|>=3a/2. Primitivity covers l=0.
    assert a > 0 and a <= c and a*c-b*b == h and abs(x[0]*y[1]-x[1]*y[0]) == 1
    assert 4*h > a*limit and 4*h+9*a*a > 4*a*limit
    directions = [x, y, (x[0]+y[0], x[1]+y[1]), (x[0]-y[0], x[1]-y[1])]
    raw_slots = slot_count(t, h, limit)[0]
    winners = []
    for vector in directions:
        j = bilinear(vector, vector)
        if j > limit:
            continue
        s, v = vector if vector[0] > 0 else (-vector[0], -vector[1])
        k = s*v
        # Accepted split -> primitive short vector by OffsetSquareWitness.exists_vector_of_hit.
        # On these balanced inputs every positive short vector conversely yields a split.
        assert s > 0 and v > 0 and gcd(s,v) == 1 and gcd(j,k) == 1 and 1 <= k <= t*j//h+1
        d = abs(p*s*s-q*v*v)
        assert d*d == j*j+4*k*(t*j-h*k)
        factor = gcd(n, (j+2*t*k-d)//2)
        assert factor in (p,q)
        rank = slot_count(t, h, j-1)[0]+k
        winners.append(dict(j=j, k=k, s=s, v=v, square_root=d, factor=factor, raw_rank=rank))
    winners.sort(key=lambda w: (w['j'], w['k']))
    assert len(winners) in (1,2) and len({(w['j'],w['k']) for w in winners}) == len(winners)
    return dict(raw_slots=raw_slots, reduction_steps=steps, first_norm=a, independent_values_above_limit=h>a*limit,
                winners=winners)


def published_controls():
    fresh = json.loads((ROOT/'research/certified-control.json').read_text())
    fresh_primes = sorted(int(chain[-1]['prime']) for chain in fresh['chains'].values())
    # The original fresh chain certificate is benchmarks/controls/PocklingtonControl.lean.
    # The crossed labels also appear in PrimeFactors/EuclideanHeightExample.lean's CRT receipt.
    fixtures = json.loads((ROOT/'benchmarks/unit-quartic.json').read_text())
    crossed = next(c for c in fixtures if c['id']=='unit-quartic-crossed-2048')
    return [('small',1891,31,61), ('fresh',int(fresh['product']),*fresh_primes),
            ('crossed',int(crossed['n']),*sorted(map(int,crossed['factors'])))]


def verify_winner(name, n, p, q, winner):
    """Compose the existing primality certificates with the kernel-checked uniqueness proof."""
    if name == 'fresh':
        primes_source = (ROOT/'benchmarks/controls/PocklingtonControl.lean').read_text()
    elif name == 'crossed':
        primes_source = render_certificate(n, [p,q])
    else:
        raise ValueError('unknown full-size control')
    source = 'import PrimeFactors.OffsetWinnerExamples\n' + primes_source + f"""
namespace PrimeFactors.Generated
open OffsetWinnerExamples CompleteOffsetSearch

theorem uniqueWinner (j k : ℕ) :
    (3*j^2≤4*{name}.h ∧ InSchedule {name}.N.sqrt {name}.h j k ∧
      ∃ f, probe {name}.N {name}.N.sqrt j k=some f) ↔ j={winner['j']} ∧ k={winner['k']} := by
  have primes : ExactFactorization {name}.N [{name}.p,{name}.q] := factorization
  have pp := primes.2 {name}.p (by simp)
  have qp := primes.2 {name}.q (by simp)
  have offset : {name}.j={winner['j']} := by decide +kernel
  have multiplier : {name}.k={winner['k']} := by decide +kernel
  simpa only [offset,multiplier] using winning_iff {name}_receipt pp qp j k

#print axioms uniqueWinner
end PrimeFactors.Generated
"""
    with TemporaryDirectory() as folder:
        certificate = Path(folder)/'Winner.lean'
        certificate.write_text(source)
        verify_file(certificate, 'PrimeFactors.Generated.uniqueWinner')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true',
                        help='kernel-check both unique positions and their prime certificates after lake build')
    args = parser.parse_args()
    report = {}
    for name,n,p,q in published_controls():
        result = winner_positions(n,p,q)
        if args.verify and name != 'small':
            if len(result['winners']) != 1:
                raise AssertionError('expected one winner on the recorded full-size control')
            verify_winner(name, n, p, q, result['winners'][0])
            result['unique_position_kernel_checked'] = True
        report[name] = result
    print(json.dumps(report, indent=2))
