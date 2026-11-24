"""Decode bounded direct Salié sums using coarse observations and phase doubling."""

from argparse import ArgumentParser
from json import dumps
from math import atan2, cos, fsum, gcd, sin, sqrt, tau

if __package__:
    from .midpoint_readings import reading
else:
    from midpoint_readings import reading


# The direct table and double-precision phase unwrapping are for small examples.
MAX_PRODUCT = 65_535
QUANTIZATION = 256


class ObservationStop(Exception):
    """A frequency check split the input or the next full sum exceeds the cap."""

    def __init__(self, outcome, factor=None):
        super().__init__(outcome)
        self.outcome = outcome
        self.factor = factor


def prepare_observer(n, max_terms, result):
    """Prepare one public unit table; return quantized concealed-cosine observations."""
    units = []
    signs = {}
    for x in range(1, n):
        result["unit_gcds"] += 1
        if gcd(x, n) == 1:
            signs[x] = reading(x, n)
            units.append((signs[x], (x + pow(x, -1, n)) % n))
    result["inverses"] = result["jacobi_evaluations"] = len(units)
    trig = cos if n % 4 == 1 else sin
    scale = tau / n
    normalizer = sqrt(n)
    cached = {}

    def observe(frequency, quantization=QUANTIZATION):
        t = frequency % n
        if t == 0:
            return 1.0
        key = (t, quantization)
        if key in cached:
            return cached[key]
        result["frequency_gcds"] += 1
        common = gcd(t, n)
        if common > 1:
            raise ObservationStop("frequency_gcd", min(common, n // common))
        if result["terms"] + len(units) > max_terms:
            raise ObservationStop("budget")
        a = t * ((n + 1) // 2) % n
        total = fsum(sign * trig(scale * ((a * phase) % n)) for sign, phase in units)
        result["sums"] += 1
        result["terms"] += len(units)
        normalized = signs[a] * total / normalizer
        coarse = round(quantization * normalized) / quantization
        cached[key] = coarse / 2 - cos(scale * t)
        return cached[key]

    return observe


def search(n, max_terms):
    """Measure complete unit-sum terms and return a checked divisor when found.

    unit_gcds counts the explicit unit-table membership tests. jacobi_evaluations
    counts calls to the shared Jacobi routine, which performs its own gcd.
    frequency_gcds counts the gcd tests on new nonzero frequencies.
    """
    if n < 3 or n % 2 == 0 or max_terms < 0:
        raise ValueError("expected an odd integer at least three and a nonnegative cap")
    result = dict(outcome="unresolved", factor=None, root=None, anchor=None,
                  terms=0, sums=0, unit_gcds=0, inverses=0,
                  jacobi_evaluations=0, frequency_gcds=0)
    if n > MAX_PRODUCT:
        result["outcome"] = "size_limit"
        return result
    if max_terms == 0:
        result["outcome"] = "budget"
        return result
    observe = prepare_observer(n, max_terms, result)

    powers = [1 << j for j in range((n - 1).bit_length() + 1)]
    try:
        cosines = [observe(t) for t in powers]
        anchor_index = min(range(len(powers)), key=lambda j: abs(cosines[j]))
        anchor = powers[anchor_index]
        result["anchor"] = anchor % n
        cosine_anchor = cosines[anchor_index]
        if abs(cosine_anchor) >= 0.9:
            return result
        sine_anchor = sqrt(1 - cosine_anchor ** 2)
        estimate = 0.0
        for t, cosine in zip(powers, cosines):
            sine = (cosine * cosine_anchor - observe(t + anchor)) / sine_anchor
            measured = (atan2(sine, cosine) / tau) % 1
            estimate = (measured + round(t * estimate - measured)) / t
    except ObservationStop as stop:
        result.update(outcome=stop.outcome, factor=stop.factor)
        return result

    root = round(n * estimate) % n
    if root not in (1, n - 1) and pow(root, 2, n) == 1:
        factor = gcd(root - 1, n)
        if 1 < factor < n and n % factor == 0:
            result.update(outcome="phase_split", factor=min(factor, n // factor), root=root)
    return result


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-terms", type=int, default=100_000)
    args = parser.parse_args()
    print(dumps(search(args.n, args.max_terms)))
