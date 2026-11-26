"""Find a proper gcd anywhere in a squaring chain by taking at most one gcd."""
from itertools import combinations
from math import gcd, isqrt

from scripts.factor import primes_through


def parameters(n, mode):
    if n < 3 or n % 2 == 0:
        raise ValueError('expected odd n >= 3')
    if mode == 'powers-of-two':
        # Assumes distinct primes of the same bit length.
        return 1, (n.bit_length()+1)//2-1
    if mode == 'product-minus-one':
        even = n-1
        twos = (even & -even).bit_length()-1
        return even >> twos, twos
    raise ValueError(f'unknown exponent chain {mode!r}')


def search(n, mode, *, every=False):
    """Scan from t^initial through t^(initial*2^height); t=floor(sqrt(n)).

    The comparison checks each non-whole value until the first proper divisor.
    The one-gcd search keeps only the last residue different from one.
    """
    initial, height = parameters(n,mode)
    base = isqrt(n)
    residue = base if initial == 1 else pow(base,initial,n)
    report = dict(mode=mode, base=str(base), initial_exponent=str(initial), height=height,
                  initial_powers=int(initial != 1), squarings=0, gcd_calls=0,
                  first_whole=None, checked_index=None, checked_residue=None,
                  checked_gcd=None)
    if residue == 1:
        report['first_whole'] = 0
        return None, report
    for index in range(height+1):
        candidate = None
        if every:
            candidate = gcd(residue-1,n)
            report.update(checked_index=index, checked_residue=str(residue), checked_gcd=str(candidate))
            report['gcd_calls'] += 1
            if candidate > 1:
                return candidate, report
        if index == height:
            break
        after = residue*residue % n
        report['squarings'] += 1
        if after == 1:
            report['first_whole'] = index+1
            break
        residue = after
    if not every:
        candidate = gcd(residue-1,n)
        report.update(checked_index=index, checked_residue=str(residue), checked_gcd=str(candidate),
                      gcd_calls=1)
    return candidate if candidate > 1 else None, report


def census(bits):
    lower = 1 << (bits-1)
    primes = [p for p in primes_through(2*lower-1) if p >= lower]
    counts = {}
    for mode in ('powers-of-two','product-minus-one'):
        totals = dict(pairs=0, splits=0, early_whole_splits=0, terminal_splits=0,
                      one_gcds=0, individual_gcds=0, one_squares=0, individual_squares=0)
        for p,q in combinations(primes,2):
            n = p*q
            if n.bit_length() != 2*bits:
                continue
            result, one = search(n,mode)
            earlier, individual = search(n,mode,every=True)
            assert result == earlier
            totals['pairs'] += 1
            if result is not None:
                assert result in (p,q)
                totals['splits'] += 1
                key = 'early_whole_splits' if one['first_whole'] is not None else 'terminal_splits'
                totals[key] += 1
            totals['one_gcds'] += one['gcd_calls']
            totals['individual_gcds'] += individual['gcd_calls']
            totals['one_squares'] += one['squarings']
            totals['individual_squares'] += individual['squarings']
        counts[mode] = totals
    return counts


if __name__ == '__main__':
    for bits in (8,10,12):
        print(bits,census(bits))
