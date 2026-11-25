"""Render the measured degree-six divisor-window witness for the Lean kernel."""


def check_sifted_interval(n, work, proof, verify_interval):
    first, radius, shift = work['lower'], work['radius'], work['shift']
    origin, anchor = work['origin'], work['anchor']
    row, ordinary = work['coefficients'], work['cleared_coefficients']
    height, depth, modulus = work['height'], work['depth'], work['rootless_modulus']
    if not (work['sifted'] and work['centered'] and work['short'] and work['excluded']
            and not work['divisors'] and work['denominator'] == 45360 and work['denominator_gcd'] == 1
            and work['degree'] == 6 and 1 <= depth <= 6 and len(row) == len(ordinary) == 7):
        raise ValueError('Expected a short seven-row sifted exclusion witness')
    if not (work['span'] == 2 * radius and first + 2 * radius == origin
            and first + 4 * radius == work['upper'] and (origin - 2 * shift) % 105 == 0
            and anchor == (n - origin) // 2 and isinstance(modulus, int) and modulus >= 2
            and 0 <= height < work['height_bound'] == first ** depth):
        raise ValueError('Inconsistent sifted window, shift, modulus or height')
    return verify_interval(n, work, proof, 'SiftedDivisorWindow', f"""  apply PrimeFactors.SiftedDivisorWindow.excludes
    (v := ![{', '.join(map(str, row))}]) (w := ![{', '.join(map(str, ordinary))}])
    (first := {first}) (r := {radius}) (t := ({anchor})) (s := ({shift})) (h := {height})
    (depth := {depth}) (modulus := {modulus})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.SiftedDivisorWindow.sampleChecks; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.jetChecks; decide +kernel)
    | (unfold PrimeFactors.SiftedDivisorWindow.height; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.rootChecks; decide +kernel)
    | decide +kernel""")
