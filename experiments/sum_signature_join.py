"""Join two CRT lists by public modular powers and count matches in a sum interval."""

from bisect import bisect_left, bisect_right
from collections import defaultdict
from hashlib import shake_256
from itertools import accumulate, count
from math import gcd, isqrt

from .midpoint_slope_batches import half_sums


def replay_bases(n, size=2):
    """Reproducible illustration. The sampling theorem assumes independent uniform draws."""
    if n < 2 or size < 1:
        raise ValueError("expected n at least 2 and at least one base")
    length = (n.bit_length() + 7) // 8
    ceiling = 1 << (length * 8)
    cutoff = ceiling - ceiling % n
    bases = []
    for counter in count():
        seed = f"prime-factors, sum-join v1, unit/{n}/{counter}".encode()
        value = int.from_bytes(shake_256(seed).digest(length), "big")
        if value < cutoff and gcd(value % n, n) == 1:
            bases.append(value % n)
            if len(bases) == size:
                return tuple(bases)


def _moduli():
    """Start with the exact sum condition at 4, then use consecutive odd primes."""
    yield 4
    primes = []
    for value in count(3, 2):
        root = isqrt(value)
        if any(value % p == 0 for p in primes if p <= root):
            continue
        primes.append(value)
        yield value


def _incremental_entries(groups, period, start, subtract, signature, multiply, inverse_period, work):
    """Carry a power alongside each partial CRT residue; each digit wraps at most once."""
    entries = [(0, start)]
    for digits in sorted(groups, key=len):
        if digits == [0]:
            continue
        # Precompute the two multipliers for every nonzero digit. The left
        # target decreases with its residue, and the right power increases.
        has_zero = 0 in digits
        powers = []
        for d in digits:
            if d == 0:
                continue
            power = signature(period-d if subtract else d)
            work["digit_powers"] += len(power)
            adjusted = multiply(power, inverse_period)
            plain, wrapped = (adjusted, power) if subtract else (power, adjusted)
            powers.append((d, plain, wrapped))
        children = []
        for previous, prev_power in entries:
            if has_zero:
                children.append((previous, prev_power))
            for d, plain, wrapped in powers:
                value = previous+d
                wrap = value >= period
                if wrap:
                    value -= period
                children.append((value, multiply(prev_power, wrapped if wrap else plain)))
        entries = children
    return entries


def search(n, *, bases=None, max_half_entries=65536, incremental=False):
    """Count matching sums; recover a unique sum or test their common exponent.

    Bounds use p≤q≤2p. Planning and both list sizes are reported even when the
    size cap stops construction. Explicit bases need only be coprime to n.
    Incremental mode precomputes the signed CRT digit powers on each side.
    """
    if n < 9 or n % 2 == 0 or max_half_entries < 1:
        raise ValueError("expected an odd integer at least 9 and a positive list cap")
    bases = tuple(replay_bases(n) if bases is None else bases)
    if not bases or any(not 0 < g < n or gcd(g, n) != 1 for g in bases):
        raise ValueError("bases must be units in [1,n)")
    left = isqrt(4*n)
    left += left*left != 4*n
    right = isqrt(9*n//2)
    width = right-left
    work = dict(width=width, period=1, left_entries=0, right_entries=0,
                local_sites=0, local_inverses=0, local_moduli=0,
                raw_interval_survivors=None, signature_matches=None,
                modular_powers=0, digit_powers=0, signature_multiplications=0,
                signature_inversions=0, crt_inverses=0, lookups=0, square_tests=0,
                unvisited_half_entries=0, raw_range_queries=0, matched_range_queries=0,
                aggregate_exponent=None, halving_squares=0, halving_gcds=0)

    def result(status, factor=None):
        factors = [] if factor is None else list(map(str, sorted((factor, n//factor))))
        return dict(outcome=status, factors=factors, bases=list(map(str, bases)), work=work)

    # The modulus must strictly exceed the span, including for a span of zero.
    period = 1
    local = []
    moduli = _moduli()
    while period <= width:
        m = next(moduli)
        work["local_moduli"] += 1
        common = gcd(m, n)
        if 1 < common < n:
            return result("factor", common)
        sums = set()
        for x in range(1, m):
            work["local_sites"] += 1
            if gcd(x, m) == 1:
                work["local_inverses"] += 1
                sums.add((x+n*pow(x, -1, m)-left) % m)
        local.append((m, sums))
        period *= m
        work["period"] = period

    halves = [[], []]
    sizes = [1, 1]
    for m, sums in sorted(local, key=lambda group: -len(group[1])):
        side = int(sizes[1] < sizes[0])
        halves[side].append((m, sums))
        sizes[side] *= len(sums)
    work.update(left_entries=sizes[0], right_entries=sizes[1])
    if max(sizes) > max_half_entries:
        work["unvisited_half_entries"] = sum(sizes)
        return result("half_list_limit")

    def contributions_for(groups):
        contributions = []
        for m, residues in groups:
            other = period//m
            work["crt_inverses"] += 1
            basis = other*pow(other, -1, m)
            contributions.append([basis*r % period for r in sorted(residues)])
        return contributions

    def signature(exponent):
        work["modular_powers"] += len(bases)
        if exponent < 0:
            work["signature_inversions"] += len(bases)
        return tuple(pow(g, exponent, n) for g in bases)

    def multiply(first, second):
        work["signature_multiplications"] += len(bases)
        return tuple(x*y % n for x, y in zip(first, second))

    left_digits, right_digits = map(contributions_for, halves)
    wrap_signature = signature(period)
    if incremental:
        work["signature_inversions"] += len(bases)
        inverse_period = tuple(pow(x, -1, n) for x in wrap_signature)
        left_records = _incremental_entries(left_digits, period, signature(n+1-left), True,
                                            signature, multiply, inverse_period, work)
        right_records = _incremental_entries(right_digits, period, (1,)*len(bases), False,
                                             signature, multiply, inverse_period, work)
        right_records.sort()
        beta = [b for b, _ in right_records]
    else:
        alpha = half_sums(left_digits, period)
        beta = sorted(half_sums(right_digits, period))
        left_records = ((a, signature(n+1-left-a)) for a in alpha)
        right_records = ((b, signature(b)) for b in beta)
    buckets = defaultdict(list)
    for b, key in right_records:
        buckets[key].append(b)
    del right_records
    moments = {key: list(accumulate(values, initial=0)) for key, values in buckets.items()}
    hits = raw = total = 0
    for a, target in left_records:
        for wrap in (0, 1):
            lower, upper = max(0, wrap*period-a), min(period-1, wrap*period+width-a)
            if lower > upper:
                continue
            work["raw_range_queries"] += 1
            raw += bisect_right(beta, upper) - bisect_left(beta, lower)
            if wrap:
                key = multiply(target, wrap_signature)
            else:
                key = target
            work["lookups"] += 1
            values = buckets.get(key)
            if values is None:
                continue
            work["matched_range_queries"] += 1
            start, stop = bisect_left(values, lower), bisect_right(values, upper)
            number = stop-start
            hits += number
            total += (left+a-wrap*period)*number + moments[key][stop]-moments[key][start]
    work.update(raw_interval_survivors=raw, signature_matches=hits)
    if hits == 0:
        return result("no_match")
    if hits > 1:
        # Every matched exponent n+1-s annihilates each base, as does their sum.
        exponent = hits*(n+1)-total
        work["aggregate_exponent"] = str(exponent)
        twos = (exponent & -exponent).bit_length()-1
        for g in bases:
            if g in (1, n-1) or twos == 0:
                continue
            x = pow(g, exponent >> twos, n)
            work["modular_powers"] += 1
            for _ in range(twos):
                if x in (1, n-1):
                    break
                work["halving_gcds"] += 1
                factor = gcd(x-1, n)
                if 1 < factor < n:
                    return result("factor", factor)
                x = x*x % n
                work["halving_squares"] += 1
        return result("ambiguous_signature")
    delta = total*total-4*n
    work["square_tests"] += 1
    gap = isqrt(delta)
    factor = (total-gap)//2
    if gap*gap == delta and (total-gap) % 2 == 0 and 1 < factor < n and n % factor == 0:
        return result("factor", factor)
    return result("no_match")
