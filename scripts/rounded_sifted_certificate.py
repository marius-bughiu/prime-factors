"""Render a rounded seven-row interval proof with the measured polynomial corrections."""

from scripts.sifted_window_certificate import validate_sifted_interval


def check_rounded_interval(n, work, proof, verify_interval):
    validate_sifted_interval(n, work)
    first, radius, shift = work['lower'], work['radius'], work['shift']
    corrections = work['corrections']
    if (not work['rounded'] or radius % 2 or len(corrections) != 7
            or any(len(row) != 7 for row in corrections)):
        raise ValueError('Expected an even radius and seven correction rows of length seven')

    def vector(row):
        return '![' + ', '.join(map(str, row)) + ']'

    correction_matrix = '![' + ', '.join(map(vector, corrections)) + ']'
    return verify_interval(n, work, proof, 'RoundedSiftedWindow', f"""  apply PrimeFactors.RoundedSiftedWindow.excludes
    (v := {vector(work['coefficients'])}) (w := {vector(work['cleared_coefficients'])})
    (e := {correction_matrix}) (first := {first}) (U := {radius//2}) (s := ({shift}))
    (t := ({work['anchor']})) (h := {work['height']}) (depth := {work['depth']})
    (modulus := {work['rootless_modulus']}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.RoundedSiftedWindow.gridChecks; decide +kernel)
    | (unfold PrimeFactors.RoundedSiftedWindow.rowChecks; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.jetChecks; decide +kernel)
    | (unfold PrimeFactors.RoundedSiftedWindow.height; decide +kernel)
    | (unfold PrimeFactors.HigherWindowCertificate.rootChecks; decide +kernel)
    | decide +kernel""")
