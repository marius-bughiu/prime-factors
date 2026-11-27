"""Find and check two square roots for a divisor and factor-sum residue filter."""
from math import gcd, isqrt

from experiments.factor_sum_quantile import sum_bounds
from experiments.mixed_ratio_heights import jacobi
from experiments.pell_pairs import convergents
from scripts.factor import primes_through


def convergent_mod(radicand, steps, modulus):
    """Recover the indicated numerator and denominator only modulo the chosen modulus."""
    base = isqrt(radicand)
    offset, denominator, quotient = 0, 1, base
    old_a, a, old_m, m = 0, 1, 1, 0
    for _ in range(steps):
        old_a, a = a, (quotient*a+old_a) % modulus
        old_m, m = m, (quotient*m+old_m) % modulus
        offset = quotient*denominator-offset
        denominator = (radicand-offset**2)//denominator
        quotient = (base+offset)//denominator
    return a, m


def collect_anchors(n, steps=32768, wheel=60, count=1, *, negative_only=False, stats=None):
    """Select coprime periods in increasing order. Negative-only skips numerator/denominator replay."""
    if steps < 1 or count < 1:
        raise ValueError('the convergent and anchor budgets must be positive')
    candidates = {}
    squares = [(p, p*p) for p in primes_through(251) if p != 2]
    for index, norm, sign, numerator, _ in convergents(n, 4, steps):
        if sign != -1 or norm % 4 != 3:
            continue
        shared = gcd(norm, n)
        if 1 < shared < n:
            if stats is not None:
                stats.update(cf_steps=index, distinct_candidates=len(candidates), examined=0,
                             coprimality_rejections=0, replay_steps=0)
            return [dict(setup_factor=shared, step=index)]
        d, b = norm, 1
        for prime, square in squares:
            while d % square == 0:
                d //= square
                b *= prime
        if shared == 1 and gcd(d, wheel) == 1:
            candidates.setdefault(d, (index, b, numerator))
    anchors = []
    combined = 1
    examined = replays = 0
    for d in sorted(candidates):
        examined += 1
        if gcd(d, combined) != 1:
            continue
        index, b, numerator = candidates[d]
        minus_root = numerator * pow(b, -1, n) % n
        if (minus_root**2+d) % n or d % 4 != 3:
            raise ArithmeticError('continued-fraction square-root certificate failed')
        anchor = dict(period=d, step=index, removed_square_root=b, minus_root=minus_root)
        if not negative_only:
            a, m = convergent_mod(4*n, index, d)
            replays += index
            anchor['root'] = a * pow(2*m, -1, d) % d
            if (anchor['root']**2-n) % d:
                raise ArithmeticError('continued-fraction square-root certificate failed')
        anchors.append(anchor)
        combined *= d
        if len(anchors) == count:
            break
    if stats is not None:
        stats.update(cf_steps=steps, distinct_candidates=len(candidates), examined=examined,
                     coprimality_rejections=examined-len(anchors), replay_steps=replays)
    return anchors


def find_anchor(n, steps=32768, wheel=60):
    anchors = collect_anchors(n, steps, wheel)
    return anchors[0] if anchors else None


def oriented(s, d, e):
    """Read the Jacobi sign on the smaller of a nonzero residue and its negative."""
    s %= d
    if s == 0:
        return False
    t = min(s, d-s)
    minus, plus = t-2*e, t+2*e
    shared = gcd(minus, d)
    if shared == 1:
        tag = jacobi(minus, d)
    else:
        # V contains each entire prime power of d whose prime divides minus.
        v = gcd(pow(minus, d.bit_length(), d), d)
        tag = jacobi(minus, d//v)*jacobi(plus, v)
    if tag not in (-1, 1):
        raise ArithmeticError('one of the chosen local offsets is a nonunit')
    return (tag == 1) == (s == t)


def progressions(low, high, residue_classes, wheel):
    for residue in sorted(residue_classes):
        first = low + (residue-low) % wheel
        if first <= high:
            yield first, 1+(high-first)//wheel


def candidate_cap(rows, period, local_cap):
    """Count full periods with the sharper of a final whole period and its actual tail."""
    total = 0
    for _, length in rows:
        blocks, tail = divmod(length, period)
        total += blocks*local_cap + min(tail, local_cap)
    return total


def compare(n, bits, steps=32768, prefix=128):
    wheel = 60
    if bits < 4 or gcd(n, wheel) != 1 or prefix < 0:
        raise ValueError('expected a product coprime to 60 and a nonnegative prefix')
    anchor = find_anchor(n, steps, wheel)
    if not anchor:
        return dict(anchor=None, unresolved=str(n))
    if 'setup_factor' in anchor:
        factor = anchor['setup_factor']
        return dict(anchor=anchor, steps=steps, factor_bits=bits, wheel=wheel,
                    pairs=[[str(p) for p in sorted((factor, n//factor))]], unresolved=None)
    d, e = anchor['period'], anchor['root']
    low, _, high = sum_bounds(n, bits)
    units = [i for i in range(wheel) if gcd(i, wheel) == 1]
    classes = {(i+n*pow(i,-1,wheel)) % wheel for i in units}
    sums = list(progressions(low, high, classes, wheel))
    cap = 2**bits-1
    divisors = list(progressions((n+cap-1)//cap, isqrt(n), units, wheel))
    # Count successful tests on the same first positions in each admissible class.
    candidates = [first+wheel*i for first, length in sums for i in range(min(prefix,length))]
    passes = [s for s in candidates if jacobi(s-2*e,d) >= 0 and jacobi(s+2*e,d) >= 0]
    oriented_passes = {s for s in candidates if oriented(s, d, e)}
    survivors = [s for s in passes if s in oriented_passes]
    hits = []
    for s in survivors:
        gap = isqrt(s*s-4*n)
        if gap*gap == s*s-4*n:
            p, q = (s-gap)//2, (s+gap)//2
            if 1 < p and p*q == n:
                hits.append([str(p),str(q)])
    # All unit square-root fibers have the same size as the roots of one.
    # The Lean torsion bound applies to every odd period through 2**1024.
    # For small periods, count the actual attainable sums for a sharper result.
    if d <= 10000:
        image = {(x+n*pow(x,-1,d)) % d for x in range(d) if jacobi(x,d) == 1}
        class_cap = len(image)
    elif d <= 2**1024:
        class_cap = (d+2**130)//4
    else:
        raise ValueError('the published fixed-root bound requires a period at most 1024 bits')
    return dict(anchor={k: str(v) if k in ('period','root','minus_root') else v
                        for k,v in anchor.items()}, steps=steps, factor_bits=bits, wheel=wheel,
                factor_positions=str(sum(t for _,t in divisors)),
                possible_factor_positions_at_most=str(candidate_cap(divisors,d,d//2)),
                sum_positions=str(sum(t for _,t in sums)),
                possible_sum_positions_at_most=str(candidate_cap(sums,d,class_cap)),
                local_sum_cap=str(class_cap), sum_classes=sorted(classes),
                complete_sum_periods=min(t//d for _,t in sums) if sums else 0,
                examined=len(candidates),
                passed_two_signs=len(passes), passed_orientation=len(oriented_passes),
                square_tests=len(survivors), pairs=hits,
                unresolved=None if hits else str(n))
