"""Replay the rational and exponential inverse-cyclotomic measurements on the fixed products 551 and 32,881.

Run python3 -m experiments.inverse_cyclotomic_measurements from the repository root.
The acquisition enumerates divisors and encounters the factors before decoding.
"""

import json
import sys
from fractions import Fraction
from math import ceil, floor, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.rotated_coefficient_filter import cyclotomic, divide_monic
from scripts.factor import fermat_split, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/inverse-cyclotomic-measurements.json"


def acquire(n):
    if n not in (551, 32881):
        raise ValueError("the polynomial acquisition is limited to the two teaching fixtures")
    orders = []
    divisions = 0
    phi_body = cyclotomic.__wrapped__.__code__

    # Count the existing recursive constructor's cold calls. Its loop executes
    # exactly one remainder test for every integer from 1 through order - 1.
    def observe(frame, event, _):
        nonlocal divisions
        if event == "call" and frame.f_code is phi_body:
            orders.append(frame.f_locals["order"])
        if event == "call" and frame.f_code is divide_monic.__code__:
            divisions += 1

    cyclotomic.cache_clear()
    previous = sys.getprofile()
    try:
        sys.setprofile(observe)
        phi = cyclotomic(n)
        psi, remainder = divide_monic([-1] + [0] * (n - 1) + [1], phi)
    finally:
        sys.setprofile(previous)
    if any(remainder):
        raise ArithmeticError("inexact inverse-cyclotomic quotient")
    work = {
        "divisor_trials_by_order": {str(j): j - 1 for j in sorted(orders)},
        "top_level_divisor_trials": n - 1,
        "all_divisor_trials": sum(j - 1 for j in orders),
        "monic_polynomial_divisions": divisions,
        "phi_degree": len(phi) - 1,
        "psi_degree": len(psi) - 1,
    }
    return psi, work


def scaled_value(psi, x):
    """Evaluate (x-1)Ψ(x) exactly by Horner's rule."""
    value = Fraction(psi[-1])
    for coefficient in reversed(psi[:-1]):
        value = x * value + coefficient
    return (x - 1) * value


def interval_product(left, right):
    endpoints = [a * b for a in left for b in right]
    return min(endpoints), max(endpoints)


def negative_exp_bounds(u, even_degree):
    """Consecutive odd/even Taylor sums enclose exp(-u) when 0 ≤ u ≤ 1."""
    if not 0 <= u <= 1 or even_degree % 2:
        raise ValueError("expected a unit-interval argument and an even truncation degree")
    term = partial = Fraction(1)
    for degree in range(1, even_degree + 1):
        term *= -u / degree
        partial += term
    return partial - term * u / (even_degree + 1), partial


def exponential_reading(psi, denominator):
    """Enclose (x-1)Ψ(x) at x=exp(-1/denominator) with its acquired coefficients."""
    u = Fraction(1, denominator)
    x = negative_exp_bounds(u, 4)
    value = (psi[-1], psi[-1])
    steps = 0
    for coefficient in reversed(psi[:-1]):
        lower, upper = interval_product(x, value)
        value = lower + coefficient, upper + coefficient
        steps += 1
    lower, upper = interval_product((x[0] - 1, x[1] - 1), value)
    scale = 10**12
    lower_tick, upper_tick = floor(scale * lower), ceil(scale * upper)
    return {
        "exponent": str(-u),
        "taylor_degrees_lower_upper": [5, 4],
        "point_lower_upper": [str(x[0]), str(x[1])],
        "interval_denominator": scale,
        "reading_lower_upper_numerators": [lower_tick, upper_tick],
        "additional_divisor_trials": 0,
        "interval_horner_steps": steps,
        "interval_products_including_outer_scale": steps + 1,
        "endpoint_products": 4 * (steps + 1),
    }


def factors_from_sum(n, total):
    delta = total**2 - 4*n
    if delta < 0:
        return None
    gap = isqrt(delta)
    factors = [(total - gap) // 2, (total + gap) // 2]
    if gap**2 != delta or sum(factors) != total or factors[0] * factors[1] != n:
        return None
    return factors


def square_screen(n, candidates, modulus):
    squares = {i*i % modulus for i in range(modulus)}
    return [s for s in candidates if (s*s - 4*n) % modulus in squares]


def trial_value(n, total, denominator):
    """Predict the reading for a candidate sum from N and an interval for sqrt(Δ)."""
    root_grid = 10**6
    root_tick = isqrt((total**2 - 4*n) * root_grid**2)
    root_lower = Fraction(root_tick, root_grid)
    root_upper = Fraction(root_tick + 1, root_grid)
    endpoints = [(total - root_upper, total - root_lower),
                 (total + root_lower, total + root_upper)]
    terms = []
    for twice_lower, twice_upper in endpoints:
        lower = 1 - negative_exp_bounds(twice_lower / (2*denominator), 6)[1]
        upper = 1 - negative_exp_bounds(twice_upper / (2*denominator), 6)[0]
        terms.append((lower, upper))
    return interval_product(*terms)


def filtered_comparison():
    n, bound = 32881, 128
    psi, acquisition = acquire(n)
    reading = exponential_reading(psi, 8*bound)

    # Both factors ≤ cap, so (cap-p)(cap-q) ≥ 0 gives the upper bound below.
    cap = 2*bound - 1
    low, high = isqrt(4*n - 1) + 1, cap + n // cap
    candidates = [s for s in range(low, high + 1) if s % 4 == (n+1) % 4]
    stages = {"sum_mod_4": candidates}
    for modulus in (16, 3, 5, 7):
        candidates = square_screen(n, candidates, modulus)
        stages[f"discriminant_mod_{modulus}"] = candidates
    if len(candidates) != 2:
        raise ArithmeticError("the worked example requires two surviving candidates")

    # A single false candidate trial suffices when only two remain. The
    # retained sum is checked with an exact integer square root afterwards.
    scale = reading["interval_denominator"]
    lower, upper = trial_value(n, candidates[0], 8*bound)
    false_interval = [floor(scale*lower), ceil(scale*upper)]
    if false_interval[0] <= reading["reading_lower_upper_numerators"][1]:
        raise ArithmeticError("the false trial is not separated above the measurement")
    total = candidates[1]
    factors = factors_from_sum(n, total)
    if factors is None:
        raise ArithmeticError("the selected sum failed its exact square test")

    # Independent checks of how much work the ordinary small-input alternatives use.
    filtered_tests = 0
    for s in candidates:
        filtered_tests += 1
        if factors_from_sum(n, s) is not None:
            break
    baseline, steps = fermat_split(n, 16)
    return {
        "n": str(n),
        "factor_width_bits": bound.bit_length(),
        "public_sum_bounds": [low, high],
        "public_screens": stages,
        "acquisition": acquisition,
        "single_exponential_reading": reading,
        "first_candidate_trial": {
            "sum": candidates[0],
            "discriminant": candidates[0]**2 - 4*n,
            "sqrt_enclosures": 1,
            "sqrt_grid_denominator": 10**6,
            "exp_enclosures": 4,
            "taylor_degrees_lower_upper": [7, 6],
            "interval_denominator": scale,
            "reading_lower_upper_numerators": false_interval,
        },
        "sum": total,
        "discriminant": total**2 - 4*n,
        "discriminant_square_tests_after_selection": 1,
        "ordinary_filtered_square_tests": filtered_tests,
        "ordinary_fermat_baseline": {"midpoints_tested": steps, "factor": str(baseline)},
        "extra_mod_11_screen": square_screen(n, candidates, 11),
        "factors": list(map(str, factors)),
    }


def measure():
    n, bound, grid = 551, 16, 4096
    x = 1 - Fraction(1, 8 * bound)
    tolerance = Fraction(1, 128 * bound)
    psi, acquisition = acquire(n)
    single_reading = exponential_reading(psi, 8 * bound)
    readings = [scaled_value(psi, x), scaled_value(psi, -x)]
    readings_on_grid = [round(grid * r) for r in readings]
    if any(abs(r - Fraction(a, grid)) > tolerance for r, a in zip(readings, readings_on_grid)):
        raise ArithmeticError("rounded measurement exceeds the proved tolerance")
    projection = Fraction(sum(readings_on_grid), 2 * grid) - 1

    # Mirror BoundedPowerMeasurement.read on the half-open interval [0, 4B).
    lo, hi = 0, 4 * bound
    exponents = []
    while lo < hi:
        mid = (lo + hi) // 2
        exponents.append(mid)
        approx = Fraction(round(grid * x**mid), grid)
        if approx <= projection + 2 * tolerance:
            hi = mid
        else:
            lo = mid + 1
    total = lo
    delta = total**2 - 4 * n
    factors = factors_from_sum(n, total)
    if factors is None:
        raise ArithmeticError("the measured sum failed the exact square test")

    baseline, steps = fermat_split(n, 1)
    result = {
        "n": str(n),
        "factor_width_bits": bound.bit_length(),
        "base": str(x),
        "grid_denominator": grid,
        "reading_tolerance": str(tolerance),
        "nearest_grid_error_bound": str(Fraction(1, 2 * grid)),
        "acquisition": acquisition,
        "single_exponential_reading": single_reading,
        "horner_steps_for_both_readings": 2 * (len(psi) - 1),
        "outer_scale_multiplications": 2,
        "reading_numerators": readings_on_grid,
        "projection": str(projection),
        "power_comparison_exponents": exponents,
        "sum": total,
        "discriminant": delta,
        "discriminant_square_tests": 1,
        "ordinary_fermat_baseline": {"midpoints_tested": steps, "factor": str(baseline)},
        "factors": list(map(str, factors)),
        "filtered_comparison": filtered_comparison(),
    }
    return result


def main():
    result = measure()
    expected = json.loads(FIXTURE.read_text())
    if result != expected:
        raise ValueError(f"measured receipt differs from fixture: {result}")
    with TemporaryDirectory() as temporary:
        for row in (result, result["filtered_comparison"]):
            certificate = Path(temporary) / f'InverseCyclotomic{row["n"]}.lean'
            certificate.write_text(render_certificate(int(row["n"]), list(map(int, row["factors"]))))
            verify_file(certificate)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
