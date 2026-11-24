"""Choose a lifted large-order element or search the balanced divisor interval.

The inputs are the product, the powering modulus, an inclusive order bound,
the largest base to try, the minimum divisor of m² to use, and a total cap on
progression gcds. Order discovery uses baby-step/giant-step. The finite local
certificate and the last progression search use explicit gcds and charge each
one. These two loops do not implement their asymptotically faster published
counterparts. No step receives the prime factors or their orders.
"""

import argparse
from collections import Counter
import json
from math import gcd, isqrt


def bounded_order(alpha, n, span, work):
    """Return the exact unit order if it is at most span, and None otherwise."""
    width = 1 + isqrt(span - 1)
    babies = {1: 0}
    power = 1
    work["bsgs_baby_entries"] += 1
    for exponent in range(1, width):
        power = power * alpha % n
        work["bsgs_multiplications"] += 1
        if power == 1:
            return exponent
        babies[power] = exponent
        work["bsgs_baby_entries"] += 1
    stride = power * alpha % n
    work["bsgs_multiplications"] += 1
    giant = 1
    for start in range(0, span, width):
        giant = giant * stride % n
        work["bsgs_multiplications"] += 1
        work["bsgs_giant_lookups"] += 1
        baby = babies.get(giant)
        if baby is not None:
            candidate = start + width - baby
            if candidate <= span:
                return candidate
    return None


def prime_powers(value, work):
    """Factor a public positive integer by bounded trial division."""
    powers = {}
    candidate = 2
    while candidate * candidate <= value:
        power = 1
        while True:
            work["trial_divisibility_tests"] += 1
            if value % candidate:
                break
            value //= candidate
            power *= candidate
            work["trial_divisions"] += 1
        if power > 1:
            powers[candidate] = power
        candidate = 3 if candidate == 2 else candidate + 2
    if value > 1:
        powers[value] = value
    return powers


def merge_orders(n, beta, old_order, components, base, new_order, work):
    """Keep the larger primary component at every prime, with its preimage."""
    replaced = 1
    selected = 1
    for prime, power in prime_powers(new_order, work).items():
        old_power = components.get(prime, 1)
        if power > old_power:
            replaced *= old_power
            selected *= power
            components[prime] = power
    # The powered images of these two terms have coprime orders.
    beta = pow(beta, replaced, n) * pow(base, new_order // selected, n) % n
    work["merge_modular_powers"] += 2
    work["order_merges"] += 1
    return beta, old_order // replaced * selected


def local_certificate(alpha, n, span, work):
    """Given global order above span, each failure produces a proper gcd."""
    power = 1
    for exponent in range(1, span + 1):
        power = power * alpha % n
        work["certificate_multiplications"] += 1
        divisor = gcd(power - 1, n)
        work["certificate_gcds"] += 1
        if divisor > 1:
            if divisor == n:
                raise ArithmeticError("global order is within the certification span")
            return divisor, exponent
    return None, None


def square_divisors(m, work):
    """Enumerate every divisor of m², including 1, once."""
    divisors = [1]
    for prime, maximal in prime_powers(m, work).items():
        prime_factors = [1]
        while prime_factors[-1] < maximal * maximal:
            prime_factors.append(prime_factors[-1] * prime)
        divisors = [d * e for d in divisors for e in prime_factors]
    work["square_divisors_generated"] += len(divisors)
    return sorted(divisors, reverse=True)


def search(n, m, span, base_cap, divisor_threshold, fallback_cap):
    if not (n >= 3 and 1 <= m < n and span >= 1 and 1 <= base_cap < n
            and divisor_threshold >= 1 and fallback_cap >= 0):
        raise ValueError("invalid product, powering modulus, order span or search budget")

    work = Counter(dict.fromkeys((
        "modulus_gcds", "base_gcds", "base_modular_powers", "bsgs_baby_entries",
        "bsgs_giant_lookups", "bsgs_multiplications", "small_orders_found",
        "trial_divisibility_tests", "trial_divisions", "order_merges", "merge_modular_powers",
        "lift_verification_powers", "certificate_multiplications", "certificate_gcds",
        "square_divisors_generated", "progressions_visited", "progression_gcds"), 0))
    result = {"span": span, "base_cap": base_cap, "divisor_threshold": divisor_threshold,
              "fallback_cap": fallback_cap, "small_order_lcm": 1, "lcm_updates": [], "work": work}

    def split(divisor, method, **details):
        factor = min(divisor, n // divisor)
        return dict(result, status="factor", method=method, factor=factor,
                    cofactor=n // factor, **details)

    def certify(beta, alpha, method):
        divisor, exponent = local_certificate(alpha, n, span, work)
        if divisor is not None:
            return split(divisor, "local_order_gcd", beta=beta, alpha=alpha,
                         base_source=method, certificate_exponent=exponent)
        return dict(result, status="certified_base", method=method, beta=beta,
                    alpha=alpha, local_order_lower_bound=span + 1)

    work["modulus_gcds"] += 1
    common = gcd(n, m)
    if common > 1:
        return split(common, "modulus_gcd")
    beta, order = 1, 1
    components = {}
    for base in range(2, base_cap + 1):
        work["base_gcds"] += 1
        common = gcd(base, n)
        if common > 1:
            return split(common, "base_gcd", base=base)
        alpha = pow(base, m*m, n)
        work["base_modular_powers"] += 1
        found = bounded_order(alpha, n, span, work)
        if found is None:
            return certify(base, alpha, "single_base")
        work["small_orders_found"] += 1
        if order % found == 0:
            continue
        beta, order = merge_orders(n, beta, order, components, base, found, work)
        result["small_order_lcm"] = order
        result["lcm_updates"].append({"base": base, "base_powered_order": found,
                                      "lcm": order, "beta": beta})
        if order > span:
            alpha = pow(beta, m*m, n)
            work["lift_verification_powers"] += 1
            return certify(beta, alpha, "lcm_merge")

    # The promised smaller factor of a balanced semiprime is in [lo, hi].
    lo, hi = 1 + isqrt((n-1)//2), isqrt(n)
    for d in square_divisors(m, work):
        if d < divisor_threshold:
            break
        work["progressions_visited"] += 1
        first = lo + (1-lo) % d
        for candidate in range(first, hi+1, d):
            if work["progression_gcds"] >= fallback_cap:
                return dict(result, status="unresolved", method="fallback_budget")
            divisor = gcd(candidate, n)
            work["progression_gcds"] += 1
            if 1 < divisor < n:
                return split(divisor, "divisor_progression", progression_modulus=d,
                             progression_candidate=candidate)
    return dict(result, status="unresolved", method="fallback_exhausted")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    for key in ("m", "span", "base-cap", "divisor-threshold", "fallback-cap"):
        parser.add_argument("--" + key, type=int, required=True)
    print(json.dumps(search(**vars(parser.parse_args())), indent=2))
