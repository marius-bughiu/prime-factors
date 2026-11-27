"""Commands, repository inputs and published proof outputs for independent checks."""

from dataclasses import dataclass


# Opaque generators can construct filenames dynamically within either of these trees.
RESEARCH = ('research', 'benchmarks')


@dataclass(frozen=True)
class Check:
    name: str
    command: tuple
    data: tuple = ()
    lean: bool = False
    outputs: tuple = ()


def experiment(name, *args, data=RESEARCH, lean=False, proof=None):
    outputs = tuple(f'{proof}-{label}-2048.lean' for label in ('fresh', 'crossed')) if proof else ()
    return Check(name, ('python3', '-m', f'experiments.{name}', *args), data, lean, outputs)


# Complex commands compute input filenames across modules. These groups include every
# fixture and reference result, also when one is added, renamed or removed.
CHECKS = (
    Check('unit-tests', ('python3', '-m', 'unittest', 'discover', '-s', 'tests'), lean=True),
    experiment('certified_control', '--verify', lean=True, data=(
        'research/certified-control.json', 'benchmarks/controls/PocklingtonControl.lean',
        'benchmarks/quartic-factor-lanes.json')),
    experiment('many_character_receipt', '--verify', lean=True, data=(
        'research/many-character-windows.json', 'benchmarks/reciprocal-anchors.json')),
    experiment('split_prime_receipt', lean=True, data=(
        'research/split-prime-panel.json', 'benchmarks/reciprocal-anchors.json')),
    experiment('affine_prime_signs', data=RESEARCH, lean=True),
    experiment('projected_wheel_receipt', '--check', data=(
        'research/many-character-windows.json', 'benchmarks/controls/ProjectedWheelPrivate.lean')),
    Check('projected-wheel-lean', ('lake', 'env', 'lean', 'benchmarks/controls/ProjectedWheelPrivate.lean'),
          ('benchmarks/controls/ProjectedWheelPrivate.lean',), True),
    experiment('three_target_limits', lean=True, data=(
        'research/three-target-limits.json', 'research/certified-control.json')),
    experiment('negative_menu_control', '--check', data=('research/negative-menu-control.json',), lean=True),
    experiment('divisor_weight_sectors', '--check', data=RESEARCH, lean=True),
    experiment('rectangular_winner_receipt', data=RESEARCH, lean=True, proof='rectangular-exact'),
    experiment('trace_population_receipt', data=RESEARCH, lean=True, proof='trace-population'),
    experiment('intermediate_menu_receipt', '--check', data=('benchmarks/intermediate-totient-rows.json',), lean=True,
               proof='intermediate-menu-exclusion'),
    experiment('intermediate_private_shift_receipt', '--check', data=RESEARCH, lean=True,
               proof='intermediate-private-shift'),
    experiment('full_width_totient_divisor', '--check', data=RESEARCH, lean=True),
    experiment('fixed_window_digit_packing', '--check', data=(
        'research/fixed-window-digit-packing.json', 'benchmarks/intermediate-totient-rows.json',
        'benchmarks/fixed-window-digit-packing.json')),
    experiment('high_word_sum_ranking', '--check', data=('research/high-word-sum-ranking.json',)),
    experiment('high_word_suffix_ranking', '--check', data=('research/high-word-suffix-ranking.json',)),
    experiment('fractional_word_ranking', '--check', data=('research/fractional-word-ranking.json',)),
    experiment('word_ranking_tail', data=('benchmarks/high-word-suffix-ranking.json',)),
    experiment('rotated_coefficient_filter', data=('benchmarks/rotated-coefficient-filter.json',)),
    experiment('signed_index_notches', data=('benchmarks/signed-index-notches.json',)),
    experiment('jacobi_moment_periods', data=('benchmarks/jacobi-moment-periods.json',)),
    experiment('jacobi_stride_period_tests', data=('benchmarks/jacobi-stride-period-tests.json',)),
    experiment('jacobi_period_scale_compare', data=('benchmarks/jacobi-period-scales.json',
                                                   'benchmarks/predecessor-square.json')),
    experiment('jacobi_scalar_stride', data=('benchmarks/jacobi-scalar-stride.json',)),
    experiment('jacobi_square_period_family', data=('benchmarks/jacobi-square-period-family.json',)),
    experiment('jacobi_square_scale_sieve', data=('benchmarks/jacobi-square-scale-sieve.json',)),
    experiment('jacobi_scale_gcd_screen', data=('benchmarks/jacobi-scale-gcd-screen.json',)),
    experiment('jacobi_scale_valuations', '--check', lean=True, proof='jacobi-scale-valuations',
               data=('benchmarks/jacobi-scale-valuations.json', 'benchmarks/unit-quartic.json',
                     'research/certified-control.json')),
    experiment('neighboring_jacobi_samples', '--exhaustive', data=('benchmarks/neighboring-jacobi-samples.json',)),
    experiment('jacobi_four_width', data=('benchmarks/jacobi-four-width.json',)),
)
