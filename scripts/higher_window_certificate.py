"""Generate a Lean exclusion for a measured higher-degree divisor window."""


def check_higher_interval(n, work, proof, verify_interval):
    """Check the recorded coefficients, Taylor conditions, height and every residue."""
    degree, depth = work['degree'], work['depth']
    row = work['coefficients']
    center, radius, anchor = work['center'], work['radius'], work['anchor']
    lower, upper, height = work['lower'], work['upper'], work['height']
    modulus = work['rootless_modulus']
    values = [n, degree, depth, center, radius, anchor, lower, upper, height, modulus]
    if not isinstance(row, (list, tuple)) or any(type(v) is not int for v in [*values, *row]):
        raise ValueError('Expected integer window data and a modular exclusion witness')
    if not work['excluded'] or not 1 <= depth <= degree or len(row) != degree + 1:
        raise ValueError('Expected an excluded interval with a complete coefficient vector')
    if n < 3 or n % 2 != 1 or center % 2 != 1 or anchor != (n - center) // 2:
        raise ValueError('Expected the measured odd input, odd center and its anchor')
    if radius < 1 or lower < 1 or (lower, upper) != (center - 2*radius, center + 2*radius):
        raise ValueError('Interval endpoints do not match the measured center and radius')
    if modulus < 2:
        raise ValueError('Expected a modular absence-of-root witness of at least two')

    literals = ', '.join(map(str, row))
    return verify_interval(n, work, proof, 'HigherWindowCertificate', f"""  apply PrimeFactors.HigherWindowCertificate.excludes
    (r := {degree+1}) (v := ![{literals}]) (c := {center}) (W := {radius})
    (t := ({anchor})) (depth := {depth}) (m := {modulus}) (H := {height})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.HigherWindowCertificate.jetChecks; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.rootChecks; decide +kernel)
    | decide +kernel""")
