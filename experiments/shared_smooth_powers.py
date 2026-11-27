"""Share terminal powers after a square-root prefix on reduced multiplicative orders."""
import argparse
import json
from math import gcd, isqrt, prod
from time import perf_counter

from scripts.factor import primes_through


def schedule(bound, factor_bits):
    cap = (1 << factor_bits) - 1
    threshold = isqrt(cap)
    result = []
    for prime in primes_through(min(bound, cap)):
        low = 1
        while low <= threshold // prime:
            low *= prime
        high = low
        while high <= cap // prime:
            high *= prime
        result.append((prime, low, high // low, high))
    return result


def accepted_seed(n, limit):
    work = dict(bases=0, initial_powers=0)
    for base in range(2, min(limit, n-1) + 1):
        work['bases'] += 1
        divisor = gcd(base,n)
        if divisor != 1:
            return divisor, None, None, work
        residue = pow(base,n-1,n)
        work['initial_powers'] += 1
        if residue != 1:
            return None, base, residue, work
    return None, None, None, work


def window_power(x, exponent, n, work):
    """Sliding odd windows, with a separately counted square or multiply at every step."""
    bits = bin(exponent)[2:]
    windows = []
    i = 0
    while i < len(bits):
        if bits[i] == '0':
            i += 1
            continue
        end = min(i+5, len(bits))
        while bits[end-1] == '0':
            end -= 1
        windows.append((end, int(bits[i:end], 2)))
        i = end

    largest = max(digit for _,digit in windows)
    odds = [x]
    if largest > 1:
        square = x*x % n
        work['squares'] += 1
        for _ in range(3, largest+1, 2):
            odds.append(odds[-1]*square % n)
            work['multiplies'] += 1
    previous, digit = windows[0]
    value = odds[digit//2]
    for end, digit in windows[1:]:
        for _ in range(end-previous):
            value = value*value % n
        work['squares'] += end-previous
        value = value*odds[digit//2] % n
        work['multiplies'] += 1
        previous = end
    for _ in range(len(bits)-previous):
        value = value*value % n
    work['squares'] += len(bits)-previous
    return value


def shared_powers(z, exponents, n, work):
    """For one radix position at a time, reuse digit powers across all exponents."""
    if not exponents:
        return []
    width = 4 if len(exponents) >= 64 else 3
    radix = 1 << width
    bits = max(exponents).bit_length()
    values = [None]*len(exponents)
    for shift in range(0, bits, width):
        digits = [(e >> shift) & (radix-1) for e in exponents]
        further = shift+width < bits
        largest = max(max(digits), radix//2 if further else 0)
        column = [1,z]
        for digit in range(2, largest+1):
            if digit % 2 == 0:
                half = column[digit//2]
                column.append(half*half % n)
                work['squares'] += 1
            else:
                column.append(column[-1]*z % n)
                work['multiplies'] += 1
        for j,digit in enumerate(digits):
            if digit:
                if values[j] is None:
                    values[j] = column[digit]
                else:
                    values[j] = values[j]*column[digit] % n
                    work['multiplies'] += 1
        if further:
            half = column[radix//2]
            z = half*half % n
            work['squares'] += 1
    return values


def batch_factor(n, values, work):
    """Products modulo n are retained for a possible descent after a saturated gcd."""
    if not values:
        return None
    levels = [[(v-1) % n for v in values]]
    while len(levels[-1]) > 1:
        row = levels[-1]
        parent = [row[i]*row[i+1] % n for i in range(0,len(row)-1,2)]
        work['multiplies'] += len(parent)
        if len(row) % 2:
            parent.append(row[-1])
        levels.append(parent)
    divisor = gcd(levels[-1][0],n)
    work['batch_gcds'] += 1
    if divisor == 1:
        return None
    index = 0
    for row in reversed(levels[:-1]):
        if divisor < n:
            return divisor
        index *= 2
        divisor = gcd(row[index],n)
        work['batch_gcds'] += 1
        if divisor == 1:
            index += 1
            divisor = n
    return divisor if divisor < n else None


def shared_scan(n, seed, plan, work):
    z = seed
    for prime,low,_,_ in plan:
        previous, z = z, window_power(z,low,n,work)
        work['prefix_blocks'] += 1
        if z == 1:
            work['prefix_gcds'] += 1
            divisor = gcd(previous-1,n)
            if 1 < divisor < n:
                return divisor, 'before prefix identity'
            return None, 'prefix identity without split'
    divisor = gcd(z-1,n)
    work['prefix_gcds'] += 1
    if 1 < divisor < n:
        return divisor, 'prefix gcd'
    powers = [tail for _,_,tail,_ in plan if tail > 1]
    values = shared_powers(z,powers,n,work)
    work['tail_powers'] = len(values)
    divisor = batch_factor(n,values,work)
    return divisor, 'terminal batch' if divisor else 'exhausted'


def classical_scan(n, seed, plan, fused):
    """Full public exponent, either fused or checked after each prime power."""
    work = dict(pow_calls=0, gcds=0, exponent_bits=0)
    z = seed
    if fused:
        e = prod(high for _,_,_,high in plan)
        z = pow(seed,e,n)
        work.update(pow_calls=1, gcds=1, exponent_bits=e.bit_length())
        divisor = gcd(z-1,n)
        if divisor != n:
            return divisor if divisor != 1 else None, work
        z = seed
    for _,_,_,high in plan:
        previous, z = z, pow(z,high,n)
        work['pow_calls'] += 1
        work['exponent_bits'] += high.bit_length()
        divisor = gcd(z-1,n)
        work['gcds'] += 1
        if divisor == n:
            divisor = gcd(previous-1,n)
            work['gcds'] += 1
        if divisor != 1:
            return divisor if divisor < n else None, work
    return None, work


def compare(n, bound, factor_bits, base_limit):
    if n < 3 or bound < 2 or factor_bits < 1 or base_limit < 2:
        raise ValueError('expected modulus at least 3, positive width, and bounds at least 2')
    start = perf_counter()
    plan = schedule(bound,factor_bits)
    immediate, base, seed, setup = accepted_seed(n,base_limit)
    setup['seconds'] = perf_counter()-start
    work = dict(bound=bound, factor_bits=factor_bits, base_limit=base_limit, accepted_base=base,
                setup=setup, squares=0, multiplies=0, prefix_blocks=0, tail_powers=0,
                prefix_gcds=0, batch_gcds=0)
    if seed is None:
        work.update(outcome='base gcd' if immediate else 'base budget exhausted', seconds=0)
        return immediate, work
    start = perf_counter()
    divisor, work['outcome'] = shared_scan(n,seed,plan,work)
    work['seconds'] = perf_counter()-start
    work['full_chain_lower_bound'] = (prod(high for _,_,_,high in plan)-1).bit_length()
    for label, fused in [('checkpoint',False),('fused',True)]:
        start = perf_counter()
        other, control = classical_scan(n,seed,plan,fused)
        control.update(divisor=str(other) if other else None, seconds=perf_counter()-start)
        work[label] = control
    return divisor, work


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--bound', type=int, default=100)
    parser.add_argument('--factor-bits', type=int)
    parser.add_argument('--base-limit', type=int, default=64)
    args = parser.parse_args()
    bits = args.factor_bits or (args.n.bit_length()+1)//2
    divisor, work = compare(args.n,args.bound,bits,args.base_limit)
    print(json.dumps(dict(divisor=str(divisor) if divisor else None, work=work), indent=2))
