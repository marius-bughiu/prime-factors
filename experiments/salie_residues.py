"""Recover a mixed square root from one bounded Salié sample per small prime.

The direct complex-sum evaluation uses binary64 and is limited to MAX_PRODUCT.
The CRT reconstruction checks its eventual factor with integer arithmetic.
Projection computes only the schedule and its precision, at any requested width.
"""

from argparse import ArgumentParser
from json import dumps
from math import acos, gcd, isfinite, isqrt, prod, tau

if __package__:
    from .divisor_samples import MAX_PRODUCT, ObservationStop, prepare_observer
    from .sieve_forecast import primes_through
else:
    from divisor_samples import MAX_PRODUCT, ObservationStop, prepare_observer
    from sieve_forecast import primes_through


# The descending projection only forecasts samples. Its width cap also bounds
# the number of selected terms: every additional modulus at least doubles M.
MAX_CAPPED_WIDTH = 16_384
MAX_FRACTION_BITS = 53
PRIME_SEGMENT_SIZE = 8192


def prime_schedule(n):
    """The shortest initial prime list whose product times nine exceeds n."""
    if n < 1:
        raise ValueError("expected a positive product")
    if n < 9:
        return []
    limit = max(8, n.bit_length())
    while True:
        primes = primes_through(limit)
        modulus = 1
        for index, prime in enumerate(primes):
            modulus *= prime
            if 9 * modulus > n:
                return primes[:index + 1]
        limit *= 2


def precision_bits(prime):
    """Round the normalized full sum on a dyadic grid of spacing at most 1/(128 p²)."""
    return (128 * prime * prime - 1).bit_length()


def descending_primes(limit):
    """Sieve one block at a time starting at the public modulus cap."""
    base_primes = primes_through(isqrt(limit))
    high = limit
    while high >= 2:
        low = max(2, high - PRIME_SEGMENT_SIZE + 1)
        flags = bytearray([1]) * (high - low + 1)
        for prime in base_primes:
            if prime*prime > high:
                break
            first = max(prime*prime, ((low + prime - 1)//prime)*prime)
            if first <= high:
                count = (high - first)//prime + 1
                flags[first-low::prime] = bytes(count)
        for offset in range(len(flags) - 1, -1, -1):
            if flags[offset]:
                yield low + offset
        high = low - 1


def projection(bits, precision_budget=None):
    """Forecast the initial prime schedule or take largest primes fitting a precision cap.

    The constrained experiment admits widths through 16,384 and up to 53
    fractional bits per observation. At most 8,388,608 modulus candidates
    are available, in segments of 8,192. No direct sums are evaluated.
    """
    if bits < 1:
        raise ValueError("expected a positive bit length")
    details = {}
    if precision_budget is None:
        primes = prime_schedule((1 << bits) - 1)
    else:
        if bits > MAX_CAPPED_WIDTH or not 0 <= precision_budget <= MAX_FRACTION_BITS:
            raise ValueError(f"constrained projection supports widths 1..{MAX_CAPPED_WIDTH} "
                             f"and precision budgets 0..{MAX_FRACTION_BITS}")
        n = (1 << bits) - 1
        cap = isqrt((1 << precision_budget) // 128)
        primes = []
        modulus = 1
        if 9*modulus <= n:
            for prime in descending_primes(cap):
                primes.append(prime)
                modulus *= prime
                if 9*modulus > n:
                    break
            else:
                raise ValueError(f"precision budget {precision_budget} gives distinct primes "
                                 f"at most {cap}, insufficient for a {bits}-bit product")

        # Any r moduli d ≤ cap have product ≤ cap^r, even if composite.
        # The search uses strict inequality 9M > n, including exact powers.
        lower, upper = 0, len(primes)
        while lower < upper:
            middle = (lower + upper) // 2
            if 9 * pow(cap, middle) > n:
                upper = middle
            else:
                lower = middle + 1
        details = dict(precision_budget=precision_budget, modulus_cap=cap,
                       product_criterion_lower_bound=lower,
                       attains_product_lower_bound=len(primes) == lower,
                       max_covered_bits=(9*modulus).bit_length() - 1)

    precisions = [precision_bits(p) for p in primes]
    modulus = prod(primes)
    whole_width = not primes or 9*(modulus//primes[-1]) <= 1 << (bits - 1)
    return dict(bits=bits, primes=primes, prime_count=len(primes),
                last_prime=primes[-1] if primes else None, precision_bits=precisions,
                max_precision_bits=max(precisions, default=0),
                total_precision_bits=sum(precisions), modulus_bits=modulus.bit_length(),
                same_schedule_for_entire_width=whole_width, **details)


def mixed_29_certificate():
    """Check the exact 197-modulus optimum at 2,048 bits and 29 fractional bits.

    Each composite d ≤ 2048 uses a prime ≤ floor(sqrt(2048)); pairwise
    coprimality means no two composite moduli can use the same small prime.
    The remaining moduli are distinct primes and their product is largest
    when choosing the largest available primes.
    """
    cap = isqrt((1 << 29) // 128)
    primes = primes_through(cap)[::-1]
    small = primes_through(isqrt(cap))
    extras = [2**11, 3*677, 5*409, 7*283, 11*181, 13*157, 17*113, 19*107,
              23*89, 29*67, 31*61, 37*53, 41*47, 43**2]
    moduli = primes[:183] + extras
    product = 1
    for modulus in moduli:
        if not 2 <= modulus <= cap or gcd(product, modulus) != 1:
            raise ArithmeticError("witness moduli must be admissible and pairwise coprime")
        product *= modulus

    count = len(moduli)
    excluded_count = count - 1
    composite_slots = len(small)
    # Reserving a D-slot for every possible composite only enlarges the bound,
    # even when the family contains fewer composites.
    upper = cap**composite_slots * prod(primes[:excluded_count-composite_slots])
    if 9*upper >= 1 << 2047 or 9*product < 1 << 2048:
        raise ArithmeticError("the proposed certificate does not cover the entire input width")
    return dict(bits=2048, precision_budget=29, modulus_cap=cap, optimal_count=count,
                moduli=moduli, composite_moduli=extras, small_primes=small,
                excluded_count=excluded_count, nine_times_excluded_upper=str(9*upper),
                nine_times_witness_product=str(9*product))


def decode_phases(n, samples):
    """Decode (prime, folded phase in turns) pairs, using only the supplied observations.

    With true hidden phase x and |a| ≤ n/3 for the correct b, b*p*x lies
    within 1/3 of an integer j and (j*n)² = a² mod p. Bounding the error
    in cos(2πx) by 1/(64 p²) keeps this rounding unambiguous for b ≤ 2.
    Each prime uses two modular inversions shared by the two CRT updates.
    """
    coefficients = {1: 0, 2: 0}
    modulus = 1
    updates = 0
    for prime, phase in samples:
        if prime < 2 or not isfinite(phase) or not 0 <= phase <= 0.5:
            raise ValueError("expected a modulus at least two and a folded phase in [0, 1/2]")
        inverse_n = pow(n, -1, prime)
        inverse_modulus = pow(modulus, -1, prime)
        for b, coefficient in coefficients.items():
            j = round(b * prime * phase)
            residue = ((j*n)**2-b*b) * inverse_n % prime
            digit = (residue-coefficient) * inverse_modulus % prime
            coefficients[b] = coefficient + modulus*digit
            updates += 1
        modulus *= prime
    if 9*modulus <= n:
        raise ValueError("insufficient product of phase moduli")

    result = dict(outcome="unresolved", factor=None, root=None, multiplier=None,
                  coefficient=None, crt_updates=updates, square_tests=0)
    for b, coefficient in coefficients.items():
        square = n*coefficient+b*b
        a = isqrt(square)
        result["square_tests"] += 1
        if a*a != square:
            continue
        root = a * pow(b, -1, n) % n
        if root in (1, n-1) or root*root % n != 1:
            continue
        common = gcd(root-1, n)
        if 1 < common < n and n % common == 0 and result["factor"] is None:
            result.update(outcome="crt_split", factor=min(common, n//common), root=root,
                          multiplier=b, coefficient=coefficient)
    return result


def search(n, max_terms):
    """Prepare a public unit table, observe only inverse-prime frequencies and decode."""
    if n < 3 or n % 2 == 0 or max_terms < 0:
        raise ValueError("expected an odd integer at least three and a nonnegative cap")
    result = dict(outcome="unresolved", factor=None, root=None, multiplier=None,
                  coefficient=None, terms=0, sums=0, unit_gcds=0, inverses=0,
                  jacobi_evaluations=0, frequency_gcds=0, prime_gcds=0,
                  frequency_inverses=0, crt_updates=0, square_tests=0,
                  prime_count=0, last_prime=None, max_precision_bits=0)
    if n > MAX_PRODUCT:
        result["outcome"] = "size_limit"
        return result
    primes = prime_schedule(n)
    result.update(prime_count=len(primes), last_prime=primes[-1] if primes else None,
                  max_precision_bits=max(map(precision_bits, primes), default=0))
    for prime in primes:
        result["prime_gcds"] += 1
        common = gcd(prime, n)
        if 1 < common < n:
            result.update(outcome="prime_gcd", factor=min(common, n//common))
            return result
    if not primes:
        return result
    if max_terms == 0:
        result["outcome"] = "budget"
        return result

    observe = prepare_observer(n, max_terms, result)
    samples = []
    try:
        for prime in primes:
            frequency = pow(prime, -1, n)
            result["frequency_inverses"] += 1
            cosine = observe(frequency, 1 << precision_bits(prime))
            phase = acos(max(-1.0, min(1.0, cosine))) / tau
            samples.append((prime, phase))
    except ObservationStop as stop:
        result.update(outcome=stop.outcome, factor=stop.factor)
        return result
    result.update(decode_phases(n, samples))
    return result


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("n", type=int, nargs="?")
    choice.add_argument("--project-bits", type=int)
    choice.add_argument("--certify-mixed-29", action="store_true",
                        help="verify the exact 197-modulus certificate for 2048 bits")
    parser.add_argument("--max-terms", type=int, default=100_000)
    parser.add_argument("--precision-bits", type=int, metavar="B",
                        help="for a projection, take largest primes with 128 d² ≤ 2^B "
                             "(0..53 bits, widths through 16384)")
    args = parser.parse_args()
    if args.precision_bits is not None and args.project_bits is None:
        parser.error("--precision-bits requires --project-bits")
    if args.certify_mixed_29:
        result = mixed_29_certificate()
    elif args.project_bits is not None:
        try:
            result = projection(args.project_bits, args.precision_bits)
        except ValueError as error:
            parser.error(str(error))
    else:
        result = search(args.n, args.max_terms)
    print(dumps(result))
