"""Look for equal-width odd factors whose sum is within a tolerance of 2**a * 3**b.

The even centers have a >= 1 and b >= 0. Choose each divisor interval and its
solver from the product, the sum tolerance and the public interval endpoints.
A local height miss is counted as unresolved, even if every center was visited.
"""

from collections import Counter
from dataclasses import dataclass
from math import gcd, isqrt

from .arbitrary_divisor_window import search as trace_window
from .binomial_divisor_window import search as sifted_window
from .higher_divisor_window import search as polynomial_window


@dataclass(frozen=True)
class Band:
    two: int
    three: int
    center: int
    first_sum: int
    last_sum: int
    lower: int
    upper: int


def ceil_sqrt(n):
    return 0 if n == 0 else 1 + isqrt(n - 1)


def sum_bands(n, tolerance):
    """Return viable smooth centers in order of increasing 3-exponent, then 2-exponent."""
    bits = (n.bit_length() + 1) // 2
    cap = (1 << bits) - 1
    lower_divisor = max(1 << (bits - 1), (n + cap - 1) // cap)
    upper_divisor = isqrt(n)
    lowest = ceil_sqrt(4 * n)
    # d + N/d decreases for d <= sqrt(N).
    highest = (lower_divisor**2 + n) // lower_divisor
    bands = []
    three, odd_part, roots = 0, 1, 2
    while lower_divisor <= upper_divisor and lowest <= highest and 2 * odd_part <= highest + tolerance:
        # The first positive exponent for which 2**two * odd_part >= lowest - tolerance.
        quotient = max(0, lowest - tolerance - 1) // odd_part
        two = max(1, quotient.bit_length())
        center = odd_part << two
        while center <= highest + tolerance:
            first = max(lowest, center - tolerance)
            last = min(highest, center + tolerance)
            # The smaller root of x²-S*x+N decreases with S. Round *inward*
            # toward possible integral divisors at these two real endpoints.
            lower = max(lower_divisor, (last - isqrt(last**2 - 4*n) + 1) // 2)
            upper = min(upper_divisor, (first - ceil_sqrt(first**2 - 4*n)) // 2)
            roots += 1 + int(first**2 != 4*n)
            if lower <= upper:
                bands.append(Band(two, three, center, first, last, lower, upper))
            two += 1
            center *= 2
        three += 1
        odd_part *= 3
    return bands, three, roots


def solve_band(n, band, work, exclusion_witnesses):
    """Return proposed divisors and whether the chosen solver covered this band."""
    lo, hi = band.lower, band.upper
    if lo == hi:
        work['singleton_tests'] += 1
        return [lo] if n % lo == 0 else [], True
    center = (lo + hi) // 2
    radius = hi - center
    # The convergent denominator is <= 2*radius. This sufficient curvature
    # test chooses the existing one-trace solver without an attempted reduction.
    scale = 12 if radius >= 6 else 1
    if 2*n*radius**3 <= scale*center**2*(center-radius):
        work['trace_windows'] += 1
        result = trace_window(n, center, radius, mod24=(scale == 12))
        for key in ('convergent_steps', 'endpoint_tests', 'square_tests', 'candidate_tests', 'divisor_tests'):
            work[key] += result[key]
        return result['divisors'], True

    # Every divisor is odd, so the signed index in this window has stride two.
    center |= 1
    radius = max(2, (max(center-lo, hi-center) + 1) // 2)
    radius += radius % 2
    if radius**5 <= n:
        work['quartic_windows'] += 1
        result = polynomial_window(n, center, radius, degree=4, depth=2,
                                modulus_limit=97, chebyshev=True)
        if exclusion_witnesses is not None and result['excluded']:
            exclusion_witnesses.append((band.three, result))
    else:
        # Use the larger root for the seven-row bound. A,B are the first and
        # last feasible integer half-sums. sqrt(A²−N) and sqrt(B²−N) increase.
        first_half, last_half = (band.first_sum + 1)//2, band.last_sum//2
        if first_half > last_half:
            return [], True
        lower = first_half + ceil_sqrt(first_half**2 - n)
        upper = last_half + isqrt(last_half**2 - n)
        work['geometry_sqrts'] += 1 + int(first_half**2 != n)
        if upper < lower:
            return [], True
        first_odd = lower | 1
        if first_odd > upper:
            return [], True
        span = max(6, 2*((upper - lower + 3)//4))
        work['sextic_windows'] += 1
        if gcd(n, 35) == 1:
            result = sifted_window(n, first_odd, span, degree=6, depth=3,
                                   centered=True, sifted=True, modulus_limit=97)
        else:
            # A factor 5 or 7 can belong to either cofactor, without being a
            # balanced divisor in this band. The ordinary jets need only odd N.
            radius = span//2
            radius += radius % 2
            work['ordinary_sextic_windows'] += 1
            result = polynomial_window(n, first_odd + 2*radius, radius, degree=6, depth=3,
                                       modulus_limit=97, chebyshev=True)
    work.update(result['work'])
    work['short_windows'] += int(result['short'])
    work['modular_exclusions'] += int(result['rootless_modulus'] is not None)
    return result['divisors'], result['short']


def search(n, tolerance, *, max_windows=None, exclusion_witnesses=None):
    """Search from N and the tolerance alone. The optional cap counts visited bands.

    direct_mod24_tests counts an alternative ascending scan, one square test
    per possible sum residue modulo 24 in each visited band, stopping at the
    recovered sum. This comparison count is computed arithmetically.
    Supply a fresh exclusion_witnesses list to collect (3-exponent, quartic
    solver result) pairs for separately kernel-checked interval exclusions.
    """
    if not isinstance(n, int) or not isinstance(tolerance, int):
        raise ValueError('expected integer input and tolerance')
    if n < 5 or gcd(n, 6) != 1 or tolerance < 0:
        raise ValueError('expected N >= 5 coprime to six and a nonnegative tolerance')
    if max_windows is not None and (not isinstance(max_windows, int) or max_windows < 0):
        raise ValueError('expected a nonnegative window budget')
    bands, exponents, roots = sum_bands(n, tolerance)
    work = Counter(dict.fromkeys(('trace_windows', 'quartic_windows', 'sextic_windows',
        'singleton_tests', 'convergent_steps', 'endpoint_tests', 'square_tests', 'candidate_tests',
        'divisor_tests', 'lll_calls', 'lll_swaps', 'lll_reductions', 'integer_root_nodes',
        'moduli_tested', 'modular_evaluations', 'short_windows', 'modular_exclusions'), 0))
    work['geometry_sqrts'] = roots
    residues = {r*(1+n) % 24 for r in range(24) if gcd(r, 24) == 1}
    bits = (n.bit_length() + 1) // 2
    found = winning = total = None
    unresolved = []
    checked = direct = even = 0
    for band in bands[:max_windows]:
        checked += 1
        candidates, covered = solve_band(n, band, work, exclusion_witnesses)
        if not covered:
            unresolved.append([band.two, band.three])
        for d in candidates:
            if not 1 < d < n:
                continue
            work['factor_confirmations'] += 1
            cofactor, remainder = divmod(n, d)
            if remainder:
                continue
            p, q = sorted((d, cofactor))
            if (p.bit_length() == q.bit_length() == bits and band.lower <= p <= band.upper
                    and band.first_sum <= p+q <= band.last_sum):
                found, winning, total = p, band, p+q
                break
        last = total if found else band.last_sum
        # For every unit r mod 24, r inverse = r. Thus p+N/p = p*(1+N) mod 24.
        direct += sum((last-r)//24 - (band.first_sum-1-r)//24 for r in residues)
        even += last//2 - (band.first_sum-1)//2
        if found:
            break
    return dict(factor=found, tolerance=tolerance, max_windows=max_windows,
                exponents_considered=exponents, viable_windows=len(bands), windows_checked=checked,
                windows_remaining=len(bands)-checked, unresolved_windows=unresolved,
                largest_divisor_window=max((b.upper-b.lower+1 for b in bands), default=0),
                direct_mod24_tests=direct, direct_even_tests=even,
                winning_exponent=winning.three if winning else None,
                winning_power_two=winning.two if winning else None,
                winning_center=winning.center if winning else None, winning_sum=total,
                sum_error=total-winning.center if winning else None, work=dict(work))
