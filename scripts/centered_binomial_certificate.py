"""Generate a kernel-checked exclusion on a signed binomial window."""


def check_centered_binomial_interval(n, work, proof, verify_interval):
    """Pass the measured rows, midpoint, inclusive endpoints and residue to the checker."""
    degree, depth, radius = work['degree'], work['depth'], work['radius']
    first, last, origin = work['lower'], work['upper'], work['origin']
    height, modulus = work['height'], work['rootless_modulus']
    row, ordinary = work['coefficients'], work['cleared_coefficients']
    if not (work.get('centered') and work['short'] and work['excluded'] and not work['divisors']
            and work['denominator_gcd'] == 1 and 1 <= depth <= degree <= work['span'] == 2*radius):
        raise ValueError('Expected a short centered binomial row and a coprime factorial denominator')
    if (origin != first + 2*radius or last != first + 4*radius or work['anchor'] != (n-origin)//2
            or len(row) != degree+1 or len(ordinary) != degree+1):
        raise ValueError('The measured basis, midpoint, anchor or endpoints are inconsistent')
    if not isinstance(modulus, int) or modulus < 2 or not 0 <= height < work['height_bound'] == first**depth:
        raise ValueError('Expected a checked height and a rootless modular witness')
    return verify_interval(n, work, proof, 'CenteredBinomialCertificate', f"""  apply PrimeFactors.CenteredBinomialCertificate.excludes
    (k := {degree}) (v := ![{', '.join(map(str, row))}]) (w := ![{', '.join(map(str, ordinary))}])
    (first := {first}) (r := {radius}) (t := ({work['anchor']})) (h := {height})
    (depth := {depth}) (modulus := {modulus})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.BinomialWindowCertificate.sampleChecks; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.jetChecks; decide +kernel)
    | (unfold PrimeFactors.CenteredBinomialCertificate.height PrimeFactors.CenteredBinomialCertificate.weight; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.rootChecks; decide +kernel)
    | decide +kernel""")
