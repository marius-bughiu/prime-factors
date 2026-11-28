"""Replay exact root-of-unity measurements on six fixed educational products.

Run python3 -m experiments.cyclotomic_root_readings from the repository root.
Each polynomial is constructed cold from its index. The separate census uses
known prime pairs to check the finite distribution of the readings.
Use --gate-width-14 to replay the separate, fixed 14-bit prime-pair holdout.
"""

import argparse
import json
from collections import Counter
from itertools import combinations
from math import isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.inverse_cyclotomic_measurements import acquire_polynomial
from scripts.factor import fermat_split, render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/cyclotomic-root-readings.json"
PRODUCTS = (14351, 11663, 9523, 11413, 9017, 8249)


def coefficient_bins(coefficients, modulus):
    """Evaluate reduction modulo X^modulus−1, including all zero input coefficients."""
    bins = [0] * modulus
    for degree, coefficient in enumerate(coefficients):
        bins[degree % modulus] += coefficient
    return bins


def seventh_root_value(bins):
    """Reduce at a primitive seventh root using 1+z+...+z^6=0."""
    return [coefficient-bins[6] for coefficient in bins[:6]]


def seventh_root_phase(bins):
    """Find k such that T(z)=z^k conjugate(T(z)) using exact basis coordinates."""
    value = seventh_root_value(bins)
    matches = []
    for shift in range(7):
        # The coefficient at j in z^shift T(z^-1) comes from shift-j.
        shifted_conjugate = [bins[(shift-j) % 7] for j in range(7)]
        if seventh_root_value(shifted_conjugate) == value:
            matches.append(shift)
    if len(matches) != 1:
        raise ArithmeticError("the control requires a unique nonzero seventh-root phase")
    return value, matches[0]


def gaussian_from_pair(p, q):
    """Evaluate the factored expression at i for an independently known odd pair."""
    if p % 4 != q % 4:
        return (2, 0)
    return (0, -2 if p % 4 == 1 else 2)


def measure_product(n):
    if n not in PRODUCTS:
        raise ValueError("acquisition is restricted to the six published educational controls")
    psi, construction = acquire_polynomial(n)
    # Ascending coefficients of T=(X-1)Ψ, without using the hidden exponents.
    scaled = [-psi[0], *(psi[i-1]-psi[i] for i in range(1, len(psi))), psi[-1]]
    seven = coefficient_bins(scaled, 7)
    four = coefficient_bins(scaled, 4)
    value, phase = seventh_root_phase(seven)
    gaussian = (four[0]-four[2], four[1]-four[3])
    if gaussian not in ((2, 0), (0, -2), (0, 2)):
        raise ArithmeticError("unexpected Gaussian value for odd prime factors")
    # (p−1)(q−1) is 4 mod 8 exactly when T(i)=+2i, and 0 otherwise.
    gaussian_sum = (n+1-(4 if gaussian == (0, 2) else 0)) % 8

    # Recover the factors independently by bounded ordinary Fermat. The
    # factorization check below audits the readings after their acquisition.
    divisor, midpoints = fermat_split(n, 64)
    if divisor is None or n % divisor:
        raise ArithmeticError("independent Fermat baseline failed")
    p, q = sorted((divisor, n//divisor))
    energy = sum(c*c for c in seven)
    reference_mean = 1 + int((p+q) % 7 == 0)
    reference_energy = 4 + 2*int((p+q) % 7 == 0) + 2*int((q-p) % 7 == 0)
    if (p*q != n or p % 7 == 0 or q % 7 == 0 or seven[0] != reference_mean
            or energy != reference_energy or phase != (p+q) % 7
            or gaussian != gaussian_from_pair(p, q) or gaussian_sum != (p+q) % 8
            or len(scaled)-1 != p+q):
        raise ArithmeticError("the readings disagree with the independently recovered pair")
    return {
        "n": str(n),
        "n_mod_256": n % 256,
        "n_mod_7": n % 7,
        "acquisition": construction,
        "cyclic_fold": {
            "coefficient_slots_per_modulus": len(scaled),
            "coefficient_additions_across_two_moduli": 2*len(scaled),
            "mod_7": seven,
            "mod_4": four,
        },
        "sum_already_given_by_polynomial_degree": len(scaled)-1,
        "mean_over_seventh_roots": seven[0],
        "mean_square_over_seventh_roots": energy,
        "primitive_seventh_root_basis": value,
        "phase_shifts_compared": 7,
        "sum_mod_7_from_phase": phase,
        "T_at_i_real_imaginary": list(gaussian),
        "sum_mod_8_from_gaussian": gaussian_sum,
        "fermat_midpoints": midpoints,
        "factors": [str(p), str(q)],
    }


def census():
    """Retrospective only. Generate every distinct seven-bit prime pair of full product width."""
    primes = [p for p in range(64, 128) if all(p % d for d in range(2, isqrt(p)+1))]
    outcomes = Counter()
    gaussians = Counter()
    residues = Counter()
    gaussian_names = {(2, 0): "2", (0, -2): "-2i", (0, 2): "+2i"}
    for p, q in combinations(primes, 2):
        n = p*q
        if n.bit_length() != 14:
            continue
        # Four exponents are known in this census population.
        bins = [0]*7
        for j, weight in ((0, 1), (p, -1), (q, -1), (p+q, 1)):
            bins[j % 7] += weight
        _, phase = seventh_root_phase(bins)
        if phase != (p+q) % 7:
            raise ArithmeticError("phase mismatch on the complete small population")
        mean, energy = bins[0], sum(c*c for c in bins)
        outcomes[f"{mean},{energy}"] += 1
        residues[str(phase)] += 1
        gaussians[gaussian_names[gaussian_from_pair(p, q)]] += 1
    return {
        "factor_bits": 7,
        "product_bits": 14,
        "eligible_distinct_unordered_pairs": sum(outcomes.values()),
        "count_by_mean_and_mean_square_at_7": dict(sorted(outcomes.items())),
        "count_by_phase_mod_7": dict(sorted(residues.items())),
        "count_by_gaussian_value": dict(sorted(gaussians.items())),
    }


GATE_MODULI = (256, 3, 5, 7, 11)
SQUARE_RESIDUES = {m: {j*j % m for j in range(m)} for m in GATE_MODULI}


def test_remainder(n, root, screened):
    """Return gate results and the lookup counts in the fixed short-circuit order."""
    remainder = n-root*root
    lookups = Counter()
    if screened:
        lookups["product_mod_4"] += 1
        if n % 4 != 1:
            return False, 0, lookups
        for modulus in GATE_MODULI:
            lookups[f"remainder_mod_{modulus}"] += 1
            if remainder % modulus not in SQUARE_RESIDUES[modulus]:
                return False, 0, lookups
    a = isqrt(remainder)
    return a*a == remainder, 1, lookups


def midpoint_scan(n, root, cap, stride, mod256):
    """Perform the exact square tests and return the first verified pair."""
    first = root+1
    first += ((n+1)//2-first) % stride
    tests = lookups = 0
    for h in range(first, cap, stride):
        delta = h*h-n
        if mod256:
            lookups += 1
            if delta % 256 not in SQUARE_RESIDUES[256]:
                continue
        tests += 1
        gap = isqrt(delta)
        if gap*gap == delta and h-gap > 1:
            p, q = h-gap, h+gap
            if p*q != n:
                raise ArithmeticError("midpoint verification failed")
            return (p, q), tests, lookups
    raise ArithmeticError("no factorization in the fixed small width")


def gate_work(n, width):
    if width not in (7, 9, 10, 11, 12, 13, 14) or not 2**(2*width-1) <= n < 2**(2*width):
        raise ValueError("the gate comparison covers only the fixed small populations")
    root = isqrt(n)
    if root*root == n:
        raise ValueError("distinct-prime products cannot be squares")
    passed, raw_tests, _ = test_remainder(n, root, False)
    checked, screened_tests, gates = test_remainder(n, root, True)
    if checked != passed:
        raise ArithmeticError("a modular prescreen excluded a valid representation")

    # On a failed gate the ordinary parity policy is retained. On a hit the
    # strongest lane doubles its stride once more for product remainder 5 mod 8.
    strongest = 16 if n % 8 == 5 else 8
    policies = {"consecutive": (1, False), "parity": (2, False),
                "switched_4": (4 if passed else 2, False),
                "switched_8": (8 if passed else 2, False),
                "switched_8_or_16": (strongest if passed else 2, False),
                "mod256": (2, True), "switched_4_mod256": (4 if passed else 2, True),
                "switched_8_mod256": (8 if passed else 2, True),
                "switched_8_or_16_mod256": (strongest if passed else 2, True)}
    scans = {}
    factors = None
    for label, (stride, screen) in policies.items():
        pair, tests, lookups = midpoint_scan(n, root, 2**width, stride, screen)
        if factors is not None and pair != factors:
            raise ArithmeticError("midpoint policies returned different factors")
        factors = pair
        scans[label] = {"exact_square_tests": tests}
        if screen:
            scans[label]["mod256_lookups"] = lookups
    return {
        "n": str(n), "factors": list(map(str, factors)),
        "floor_sqrt": root, "remainder": n-root*root, "gate_accepts": passed,
        "raw_gate_square_tests": raw_tests, "screened_gate_square_tests": screened_tests,
        "gate_lookups": dict(gates), "midpoint_scans": scans,
    }


def full_gate_population(width):
    """Discover each pair by the midpoint scans and verify it against the generated population."""
    lo, hi = 2**(width-1), 2**width
    primes = [p for p in range(lo, hi) if all(p % d for d in range(2, isqrt(p)+1))]
    pairs = accepted = raw_tests = screened_tests = 0
    gates = Counter()
    scans = {}
    accepted_sums = Counter()
    for p, q in combinations(primes, 2):
        n = p*q
        if n.bit_length() != 2*width:
            continue
        work = gate_work(n, width)
        if work["factors"] != [str(p), str(q)]:
            raise ArithmeticError("midpoint results disagree with the generated prime pair")
        pairs += 1
        accepted += work["gate_accepts"]
        raw_tests += work["raw_gate_square_tests"]
        screened_tests += work["screened_gate_square_tests"]
        gates.update(work["gate_lookups"])
        for policy, counts in work["midpoint_scans"].items():
            scans.setdefault(policy, Counter()).update(counts)
            if work["gate_accepts"]:
                accepted_sums[policy] += counts["exact_square_tests"]
    for policy, counts in scans.items():
        if policy.startswith("switched"):
            baseline = "mod256" if policy.endswith("mod256") else "parity"
            tests = counts["exact_square_tests"]
            counts["total_with_raw_gate"] = tests+raw_tests
            counts["total_with_screened_gate"] = tests+screened_tests
            counts["net_squares_saved_raw_gate"] = scans[baseline]["exact_square_tests"]-(tests+raw_tests)
            counts["net_squares_saved_screened_gate"] = scans[baseline]["exact_square_tests"]-(tests+screened_tests)
    return {
        "factor_bits": width, "product_bits": 2*width, "pairs": pairs, "accepted": accepted,
        "raw_gate_square_tests": raw_tests, "screened_gate_square_tests": screened_tests,
        "short_circuit_gate_lookups": dict(gates), "sum_of_gate_lookups": sum(gates.values()),
        "midpoint_scans": {policy: dict(counts) for policy, counts in scans.items()},
        "midpoint_square_tests_on_accepted_pairs": dict(accepted_sums),
    }


def square_remainder_study():
    positive = gate_work(525689, 10)
    negative = gate_work(8249, 7)
    negative["independent_two_squares_witness"] = [32, 85]
    if 32**2 + 85**2 != 8249 or negative["gate_accepts"] or not positive["gate_accepts"]:
        raise ArithmeticError("square-remainder controls failed")
    return {
        "gate_order": ["product_mod_4", *(f"remainder_mod_{m}" for m in GATE_MODULI)],
        "positive": positive, "representable_but_missed": negative,
        "complete_populations": [full_gate_population(w) for w in (9, 10, 11, 12, 13)],
    }


def measure():
    return {
        "controls": [measure_product(n) for n in PRODUCTS],
        "known_factor_census": census(),
        "square_remainder_study": square_remainder_study(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate-width-14", action="store_true",
                        help="replay only the 14-bit prime-pair square-remainder holdout")
    if parser.parse_args().gate_width_14:
        observed = full_gate_population(14)
        expected = json.loads(FIXTURE.read_text())["square_remainder_holdout_14"]
        if observed != expected:
            raise ValueError("14-bit holdout differs from the checked fixture")
        print(json.dumps(observed, indent=2))
        return
    observed = measure()
    expected = json.loads(FIXTURE.read_text())
    del expected["square_remainder_holdout_14"]
    if observed != expected:
        raise ValueError("root-of-unity measurements differ from the checked fixture")
    with TemporaryDirectory() as temporary:
        for row in [*observed["controls"], observed["square_remainder_study"]["positive"]]:
            certificate = Path(temporary) / f"RootReading{row['n']}.lean"
            factors = list(map(int, row["factors"]))
            certificate.write_text(render_certificate(int(row["n"]), factors))
            verify_file(certificate)
    print(json.dumps(observed, indent=2))


if __name__ == "__main__":
    main()
