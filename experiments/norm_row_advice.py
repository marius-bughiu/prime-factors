"""Count optimal row choices with prefix/suffix advice on an exhaustively labeled small population."""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import json
from math import isqrt

from .gap_coverage import primes_through


def canonical_row(p):
    """Offline label for one odd prime, with a direct check of uniqueness."""
    d = {1:-1, 3:-2, 5:-1, 7:2}[p % 8]
    rows = []
    for a in range(1,isqrt(p)+1):
        if a % 2 != int(d == -2):
            continue
        square = 2*a*a-p if d == 2 else p+d*a*a
        if square <= 0:
            continue
        t = isqrt(square)
        if t % 2 and t*t == square and (d != 2 or t<a):
            rows.append((d,a))
    if len(rows) != 1:
        raise ArithmeticError(f'expected one normalized representation for {p}')
    return rows[0]


def population(bits):
    if not 3 <= bits <= 16:
        raise ValueError('exhaustive analysis is bounded to 3–16 prime bits')
    x = 2**(bits-1)
    primes = [p for p in primes_through(2*x-1) if p >= x]
    rows = {p:canonical_row(p) for p in primes}
    return [(p*q,rows[p]) for i,p in enumerate(primes) for q in primes[i+1:] if p*q >= 2*x*x]


def optimal(pairs, bits, high_bits, low_bits, budgets):
    if min(high_bits,low_bits,*budgets) < 0 or high_bits+low_bits > 2*bits-2:
        raise ValueError('expected nonoverlapping variable prefix and suffix bits')
    start = 1 << (2*bits-1)
    groups = defaultdict(Counter)
    for n,row in pairs:
        key = ((n-start)*(1 << high_bits)//start, (n//2) % (1 << low_bits))
        groups[key][row] += 1
    ordered = [sorted(hist.values(),reverse=True) for hist in groups.values()]
    return dict(high_bits=high_bits,low_bits=low_bits,observed_buckets=len(groups),
                hits={str(k):sum(sum(counts[:k]) for counts in ordered) for k in budgets})


def target_bound(high_bits, low_bits, row_budget):
    """Upper bound when the fixed leading 1 and final odd bit are supplied for free."""
    if min(high_bits,low_bits,row_budget) < 0 or high_bits+low_bits > 2046:
        raise ValueError('invalid extent of advice or row budget')
    x = 2**1023
    # Only odd suffixes occur, so their number is half the arithmetic modulus.
    observed = 1 << (high_bits+low_bits)
    # The suffix modulus can be >X if many low bits are used; it remains coprime
    # to every odd hidden prime. The sum of all interval widths is 2 X².
    numerator = 2*row_budget*(2**511)*(observed+x)
    return min(Fraction(1), Fraction(numerator*710**2*10000,22**2*x*x))


def sample(bits):
    pairs = population(bits)
    sizes = ((0,0),(4,0),(0,4),(4,4),(8,0),(0,8),(8,4),(4,8))
    return dict(prime_bits=bits,products=len(pairs),
                results=[optimal(pairs,bits,h,k,[1,2,4,8]) for h,k in sizes if h+k<=2*bits-2])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits',type=int,default=12)
    args=parser.parse_args()
    print(json.dumps(sample(args.bits),indent=2))
