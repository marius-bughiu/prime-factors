"""One lifted geometric grid for every admissible factor-sum residue modulo 32."""

from math import gcd

from .geometric_lifted_readout import _decode_samples
from .geometric_readout_blocks import _prepare_family, _setup, _shape
from .geometric_sum_readout import _binary_classes, _interval


def filtered_coefficients(n, g, target, lower, count):
    """Direct Taylor reference over admissible absolute indices, at the transported base."""
    accepted, _ = _binary_classes(n)
    constant = 1
    linear = [0, 0, 0]
    quadratic = [0, 0, 0]
    jump = pow(g, 32, n)
    for residue in accepted:
        first = (residue - lower) % 32
        power = pow(g, first, n)
        for index in range(first, count, 32):
            value = (target - power) % n
            slope = -index * power % n
            curvature = -(index * (index - 1) // 2) * power % n
            for direction, first_order in enumerate((slope, slope + target, slope - target)):
                quadratic[direction] = (quadratic[direction] * value
                                        + linear[direction] * first_order
                                        + constant * curvature) % n
                linear[direction] = (linear[direction] * value + constant * first_order) % n
            constant = constant * value % n
            power = power * jump % n
    return constant, linear, quadratic


def search(n, base, max_block_width, max_quotient=48, *, all_targets=False, reflected=False):
    """Measure the union of all admissible indices and decode at the original sum origin.

    The width cap precedes modular lifting or grid allocation. Up to one extra
    index per admissible residue is handled separately from the common grid.
    """
    if max_block_width < 0:
        raise ValueError("expected a nonnegative block-width cap")
    lower, upper = _interval(n, base, max_block_width**2, max_quotient)
    count = upper - lower + 1
    common_length, suffix = divmod(count, 32)
    width, _, _ = _shape(common_length)
    accepted, _ = _binary_classes(n)
    offsets = sorted((residue - lower) % 32 for residue in accepted)
    lanes = [(offset, common_length + int(offset < suffix)) for offset in offsets]
    retained = sum(length for _, length in lanes)
    work = dict(setup_roots=2, setup_gcds=1, setup_powers=0, terms=0,
                unvisited_terms=retained, sample_gcds=0, coefficient_gcds=0,
                inversions=0, square_tests=0, quotient_gcds=0,
                equal_denominator_gcds=0, equal_signs=0)
    wheel = dict(unit_residues=16, local_inversions=16, step_powers=0, offset_powers=0,
                 lane_inversions=0, correction_powers=0, extra_start_powers=0,
                 extra_terms=0, normalization_products=0, corrected_products=0,
                 lane_combinations=0)
    report = dict(origin=str(lower), last_sum=str(upper), dense_terms=str(count),
                  total_terms=str(retained), removed_terms=str(count - retained),
                  common_length=str(common_length), accepted_mod_32=accepted,
                  lanes=[dict(offset=offset, count=str(length)) for offset, length in lanes],
                  required_width=width, dense_required_width=_shape(count)[0],
                  base=base, max_block_width=max_block_width, max_quotient=max_quotient,
                  all_targets=all_targets, reflected=reflected, samples={}, reduced_base=None,
                  reduced_target=None, constant=None, linear_minus=None, linear=None,
                  quadratic=None, quadratic_A=None, quadratic_B=None, quadratic_D=None,
                  winning_index=None, readout_index=None, quotient_hits=[], equal_hits=[],
                  work=work, wheel_work=wheel)

    def finish(reason, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError("invalid split")
        return dict(report, outcome=reason, factor=factor)

    common = gcd(base, n)
    if common > 1:
        return finish('base_gcd', common)
    if width > max_block_width:
        return finish('block_width_limit')
    if not retained:
        return finish('empty_filtered_interval')

    modulus = n**3
    lifted = pow(base, n, modulus)
    target = pow(lifted, n + 1 - lower, modulus)
    root = lifted * (1 + n) % modulus
    report.update(reduced_base=lifted % n, reduced_target=target % n)
    work['setup_powers'] = 2
    shape, ops = _setup(n, lifted, common_length, 3)
    report['block_work'] = ops
    evaluate = None
    extra_root = None
    if common_length:
        step = pow(root, 32, modulus)
        wheel['step_powers'] = 1
        evaluate = _prepare_family(step, modulus, *shape, ops,
                                   reflected_modulus=n if reflected else None)
        if evaluate is None:
            return finish('reflected_denominator_gcd', int(ops['reflected_factor']))
        if any(length > common_length for _, length in lanes):
            extra_root = pow(step, common_length, modulus)
            wheel['extra_start_powers'] = 1

    prepared = []
    for offset, length in lanes:
        if length == 0:
            continue
        multiplier = pow(root, offset, modulus)
        wheel['offset_powers'] += 1
        if evaluate is None:
            # With no full wheel turn this lane contains only its first root.
            prepared.append((multiplier, None, True))
        else:
            inverse = pow(multiplier, -1, modulus)
            correction = pow(multiplier, length, modulus)
            wheel['lane_inversions'] += 1
            wheel['correction_powers'] += 1
            prepared.append((inverse, correction, length > common_length))
    work.update(terms=retained, unvisited_terms=0)

    def sample(direction):
        key = str(direction)
        if key in report['samples']:
            return report['samples'][key]
        point = target * (1 + direction * n) % modulus
        product = 1
        for multiplier, correction, has_extra in prepared:
            if evaluate is None:
                value = point - multiplier
            else:
                normalized = point * multiplier % modulus
                value = evaluate(normalized)
                wheel['normalization_products'] += 1
                if has_extra:
                    value = value * (normalized - extra_root) % modulus
                # Undo the change of variable for every absolute root in this lane.
                value = value * correction % modulus
                wheel['corrected_products'] += 1
            wheel['extra_terms'] += int(has_extra)
            product = product * value % modulus
            wheel['lane_combinations'] += 1
        report['samples'][key] = product
        return product

    return _decode_samples(n, lower, count, max_quotient, report, sample, finish, all_targets)
