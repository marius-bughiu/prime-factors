"""Generate a Lean certificate excluding a public interval using a binomial row."""

from math import factorial, gcd


def check_binomial_interval(n, work, proof, verify_interval):
    """Replay the basis conversion, factorial cancellation, height and modular tests."""
    degree, depth, span = work['degree'], work['depth'], work['span']
    first, last, anchor = work['lower'], work['upper'], work['anchor']
    height, modulus = work['height'], work['rootless_modulus']
    denominator, common = work['denominator'], work['denominator_gcd']
    row, cleared = work['coefficients'], work['cleared_coefficients']
    fields = (n, degree, depth, span, first, last, anchor, height, modulus,
              denominator, common, work['height_bound'])
    if any(type(x) is not int for x in fields):
        raise ValueError('Expected integer window data and a modular witness')
    if not 1 <= depth <= degree <= span or any(
            not isinstance(v, (tuple, list)) or len(v) != degree + 1
            or any(type(x) is not int for x in v) for v in (row, cleared)):
        raise ValueError('Expected binomial and ordinary integer rows of the declared degree')
    if n < 3 or first < 1 or n % 2 != 1 or first % 2 != 1 or last != first + 2*span:
        raise ValueError('Expected an odd input, odd first candidate, and matching right endpoint')
    if anchor != (n - first)//2 or denominator != factorial(degree) or common != gcd(n, denominator):
        raise ValueError('The anchor or denominator does not match the recorded run')
    if not (work['short'] and work['excluded'] and not work['divisors'] and modulus >= 2
            and common == 1 and 0 <= height < work['height_bound'] == first**depth):
        raise ValueError('Expected a short row excluding the interval with coprime denominator')

    coefficients = ', '.join(map(str, row))
    ordinary = ', '.join(map(str, cleared))
    return verify_interval(n, work, proof, 'BinomialWindowCertificate', f"""  apply PrimeFactors.BinomialWindowCertificate.excludes
    (k := {degree}) (v := ![{coefficients}]) (w := ![{ordinary}])
    (first := {first}) (span := {span}) (t := ({anchor})) (h := {height})
    (depth := {depth}) (modulus := {modulus})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.BinomialWindowCertificate.sampleChecks; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.jetChecks; decide +kernel)
    | (unfold PrimeFactors.BinomialWindowCertificate.height; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.rootChecks; decide +kernel)
    | decide +kernel""")
