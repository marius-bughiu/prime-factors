"""Recover factors from one directly evaluated, interval-certified Salié sum.

search takes only N and a unit-term budget. decode_seed takes only N and the
signed integer encoding the rounded full sum at the public seed frequency.
The direct sum scans the public residues, retaining only unit membership.
"""
from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt, prod

if __package__:
    from .divisor_samples import MAX_PRODUCT
    from .midpoint_readings import reading
    from .salie_reference import SCALE, ceil_div, cosine_bounds, folded_phase
    from .salie_residues import decode_phases, precision_bits, prime_schedule
else:
    from divisor_samples import MAX_PRODUCT
    from midpoint_readings import reading
    from salie_reference import SCALE, ceil_div, cosine_bounds, folded_phase
    from salie_residues import decode_phases, precision_bits, prime_schedule


def seed_parameters(primes):
    """U = 1/product mod N and degree product/ell reproduce 1/ell mod N."""
    modulus = prod(primes)
    degrees = [modulus // prime for prime in primes]
    target_bits = max(16, max(map(precision_bits, primes)))
    seed_bits = target_bits + (max(degrees)**2 - 1).bit_length() + 1
    return modulus, degrees, seed_bits


def rounded_sum(n, frequency, bits, max_terms, work):
    """Enclose the real component after normalization and certify one dyadic word."""
    a = frequency * ((n + 1) // 2) % n
    low = high = 0
    for x in range(1, n):
        work["unit_gcds"] += 1
        if gcd(x, n) != 1:
            continue
        if work["terms"] == max_terms:
            return None
        phase = a * (x + pow(x, -1, n)) % n
        sign = reading(x, n)
        work["unit_inverses"] += 1
        work["jacobi_evaluations"] += 1
        work["terms"] += 1
        # For N = 3 mod 4 the Gauss unit is i. Its real projection after
        # normalization is the sine, expressed as a shifted cosine.
        left, right = (cosine_bounds(phase, n) if n % 4 == 1
                       else cosine_bounds(n - 4*phase, 4*n))
        if sign < 0:
            left, right = -right, -left
        low, high = low + left, high + right

    if reading(a, n) < 0:
        low, high = -high, -low
    work["jacobi_evaluations"] += 1
    work["sums"] = 1
    lower_sqrt = isqrt(n*SCALE*SCALE)
    denominators = (lower_sqrt, lower_sqrt + 1)
    low = min(low*SCALE // den for den in denominators)
    high = max(ceil_div(high*SCALE, den) for den in denominators)
    grid = SCALE >> bits
    word = (low + grid//2) // grid
    if not (2*word-1)*grid < 2*low <= 2*high < (2*word+1)*grid:
        raise ValueError("raw interval does not certify a unique rounded sum")
    return word


def chebyshev_bounds(low, high, degree):
    """Enclose T_degree by T_(2j), T_(2j+1) doubling with directed rounding."""
    def twice_product(a, b):
        endpoints = [2*x*y for x in a for y in b]
        return min(endpoints)//SCALE, ceil_div(max(endpoints), SCALE)

    def subtract(a, b):
        # Every exact value after subtraction is a Chebyshev cosine.
        return max(-SCALE, a[0]-b[1]), min(SCALE, a[1]-b[0])

    # Evaluate at a point to avoid repeated use of the seed uncertainty.
    # |T'_k(x)| <= k^2 on [-1,1] then encloses the entire seed interval.
    midpoint = (low+high)//2
    x = (midpoint, midpoint)
    one = (SCALE, SCALE)
    curr, nxt = one, x
    for digit in bin(degree)[2:]:
        odd = subtract(twice_product(curr, nxt), x)
        if digit == '0':
            curr, nxt = subtract(twice_product(curr, curr), one), odd
        else:
            curr, nxt = odd, subtract(twice_product(nxt, nxt), one)
    error = degree**2 * (high-midpoint)
    return max(-SCALE, curr[0]-error), min(SCALE, curr[1]+error)


def decode_seed(n, word):
    """Replay the single rounded full sum under the distinct odd semiprime promise."""
    if n < 9 or n > MAX_PRODUCT or n % 2 == 0:
        raise ValueError("expected a bounded odd product")
    primes = prime_schedule(n)
    modulus, degrees, bits = seed_parameters(primes)
    if not isinstance(word, int) or abs(word) > (4 << bits) or gcd(n, modulus) != 1:
        raise ValueError("invalid Salié seed word or schedule")
    frequency = pow(modulus, -1, n)
    grid = SCALE >> bits
    public_low, public_high = cosine_bounds(frequency, n)
    low = max(-SCALE, (word*grid - grid//2)//2 - public_high)
    high = min(SCALE, ceil_div(word*grid + grid//2, 2) - public_low)
    if low > high:
        raise ValueError("raw word and public cosine have disjoint bounds")

    images = [chebyshev_bounds(low, high, k) for k in degrees]
    samples = []
    for prime, (left, right) in zip(primes, images):
        midpoint = (left+right)//2
        if (right-midpoint)*64*prime**2 > SCALE:
            raise ValueError("propagated cosine exceeds the decoding tolerance")
        samples.append((prime, folded_phase(midpoint)))

    result = decode_phases(n, samples)
    rounded = []
    if result["factor"] is not None:
        for (prime, phase), (left, right) in zip(samples, images):
            span = result["multiplier"]*prime
            j = round(span*phase)
            # Certify this nearest integer for the whole rounded seed cell.
            if 2*j-1 >= 0 and cosine_bounds(2*j-1, 2*span)[0] <= right:
                raise ValueError("left rounding boundary intersects a cosine enclosure")
            if 2*j+1 <= span and cosine_bounds(2*j+1, 2*span)[1] >= left:
                raise ValueError("right rounding boundary intersects a cosine enclosure")
            rounded.append(j)
    return dict(**result, chebyshev_steps=sum(k.bit_length() for k in degrees),
                certified_cells=len(rounded), rounded_numerators=rounded,
                square_residues=[(j*n)**2 % p for p, j in zip(primes, rounded)])


def search(n, max_terms):
    """Return a measured product-only split, or leave the input unresolved."""
    if n < 3 or n % 2 == 0 or max_terms < 0:
        raise ValueError("expected an odd product and a nonnegative term budget")
    result = dict(outcome="unresolved", factor=None, root=None, multiplier=None,
                  coefficient=None, terms=0, sums=0, unit_gcds=0, unit_inverses=0,
                  jacobi_evaluations=0, prime_gcds=0, seed_frequency=None,
                  seed_bits=None, seed_word=None, max_degree=0, chebyshev_steps=0,
                  certified_cells=0, rounded_numerators=[], square_residues=[],
                  crt_updates=0, square_tests=0)
    if n > MAX_PRODUCT:
        result["outcome"] = "size_limit"
        return result
    primes = prime_schedule(n)
    for prime in primes:
        result["prime_gcds"] += 1
        common = gcd(prime, n)
        if 1 < common < n:
            result.update(outcome="prime_gcd", factor=min(common, n//common))
            return result
    if not primes:
        return result
    modulus, degrees, bits = seed_parameters(primes)
    frequency = pow(modulus, -1, n)
    result.update(seed_frequency=frequency, seed_bits=bits, max_degree=max(degrees))
    if max_terms == 0:
        result["outcome"] = "budget"
        return result
    try:
        word = rounded_sum(n, frequency, bits, max_terms, result)
    except ValueError:
        result["outcome"] = "uncertified"
        return result
    if word is None:
        result["outcome"] = "budget"
        return result
    result["seed_word"] = word
    try:
        decoded = decode_seed(n, word)
    except ValueError:
        result["outcome"] = "uncertified"
        return result
    result.update(decoded)
    return result


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-terms", type=int, default=65535)
    args = parser.parse_args()
    print(dumps(search(args.n, args.max_terms)))
