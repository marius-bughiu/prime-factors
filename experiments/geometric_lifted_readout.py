"""One-grid product readings for the sum of two distinct, balanced odd primes."""

from math import gcd

from .geometric_readout_blocks import _prepare_family, _setup, _shape
from .geometric_sum_readout import _decode, _interval


def search(n, base, max_block_width, max_quotient=48, *, all_targets=False):
    """Evaluate signed directions on one grid, and check every reported divisor.

    The coefficient interpretation assumes n=p*q for distinct odd primes p≤q≤2p.
    The integer product and gcd checks are valid on arbitrary accepted inputs.
    """
    if max_block_width < 0:
        raise ValueError("expected a nonnegative block-width cap")
    lower, upper = _interval(n, base, max_block_width**2, max_quotient)
    count = upper-lower+1
    width, _, _ = _shape(count)
    work = dict(setup_roots=2, setup_gcds=1, setup_powers=0, terms=0, unvisited_terms=count,
                sample_gcds=0, coefficient_gcds=0, inversions=0, square_tests=0, quotient_gcds=0,
                equal_denominator_gcds=0, equal_signs=0)
    report = dict(origin=str(lower), last_sum=str(upper), total_terms=str(count), base=base,
                  required_width=width, max_block_width=max_block_width, max_quotient=max_quotient,
                  all_targets=all_targets, reduced_base=None, reduced_target=None, samples={},
                  linear_minus=None, constant=None, linear=None, quadratic=None, winning_index=None,
                  readout_index=None, quadratic_A=None, quadratic_B=None, quadratic_D=None,
                  quotient_hits=[], equal_hits=[], work=work)

    def finish(reason, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError("invalid split")
        return dict(report, outcome=reason, factor=factor)

    common = gcd(base, n)
    if common > 1:
        return finish('base_gcd', common)
    if width > max_block_width:
        return finish('block_width_limit')
    if count == 0:
        return finish('empty_interval')

    # Raising to n makes each congruent pair of powers modulo p coincide modulo p²
    # for both prime divisors. All evaluation uses the same perturbation t=n.
    mod = n**3
    lifted = pow(base, n, mod)
    target = pow(lifted, n+1-lower, mod)
    report.update(reduced_base=lifted % n, reduced_target=target % n)
    work.update(setup_powers=2, terms=count, unvisited_terms=0)
    shape, ops = _setup(n, lifted, count, 3)
    at = _prepare_family(lifted*(1+n) % mod, mod, *shape, ops)
    report['block_work'] = ops

    def sample(z):
        key = str(z)
        if key not in report['samples']:
            report['samples'][key] = at(target*(1+z*n) % mod)
        return report['samples'][key]

    if all_targets:
        for z in (-1, 0, 1):
            sample(z)

    def digit(z, divisor):
        value, remainder = divmod(sample(z), divisor)
        if not remainder:
            ops['exact_divisions'] += 1
        return value % n, remainder

    def failed_division(remainder):
        # A remainder divisible by n arises in the second-order check. Inspect
        # its next digit for a proper gcd as well.
        witness = remainder//n if remainder%n == 0 else remainder
        work['sample_gcds'] += 1
        common = gcd(witness, n)
        return finish('sample_gcd', common) if 1 < common < n else finish('inconsistent_sample')

    minus, remainder = digit(-1, n)
    if remainder:
        return failed_division(remainder)
    report.update(constant=0, linear_minus=minus)
    work['sample_gcds'] += 1
    common = gcd(minus, n)
    if 1 < common < n:
        return finish('minus_one_gcd', common)

    zero, remainder = digit(0, n)
    if remainder:
        return failed_division(remainder)
    linear = [zero, (2*zero-minus)%n, minus]
    quadratic = None
    if common == n:
        # The interval excludes the signed index -1 at each prime. Here each
        # prime therefore has at least two hits under the semiprime promise.
        quad = []
        for z in (0, 1, -1):
            value, remainder = digit(z, n*n)
            if remainder:
                return failed_division(remainder)
            quad.append(value)
        quadratic = quad

    # If the premise fails on a different input, a purported simple case may
    # still have zero slope. Any nonzero intercept is a unit or a gcd witness.
    if quadratic is None and linear[1] == linear[0]:
        report['linear'] = linear
        return finish('inconsistent_linear_reading')
    return _decode(n, lower, 1, count, max_quotient, report, 0, linear, quadratic)
