"""Sharp finite cutoffs for consecutive omissions in regular weighted-sum images."""

from math import isqrt


def prime(value):
    return value >= 2 and all(value % d for d in range(2, isqrt(value) + 1))


def weil_guarantees(p, length):
    """Test the strict paper bound using integers only."""
    scale = 1 << length
    main = p + 1 - length * scale
    error = (length - 2) * scale + 2
    return length < p and main > 0 and main * main > p * error * error


def missing_discriminants(p, length):
    """List all nonzero c for which no cyclic interval has the required signs."""
    if not prime(p) or p == 2 or not 1 <= length < p:
        raise ValueError("expected an odd prime and a length between 1 and p-1")
    full = (1 << p) - 1
    packed = bytearray([255]) * ((p + 7) // 8)
    for x in range((p + 1) // 2):
        residue = -x * x % p
        packed[residue // 8] &= 255 ^ (1 << (residue % 8))
    # Bit c is set exactly when -c is a nonsquare.
    at_zero = int.from_bytes(packed, "little") & full

    def at(site):
        shift = site * site % p
        return ((at_zero << shift) | (at_zero >> (p - shift))) & full

    remaining = full ^ 1
    window = [at(site) for site in range(length)]
    for start in range(p):
        covered = window[0]
        for mask in window[1:]:
            covered &= mask
        remaining &= ~covered
        if not remaining:
            return []
        window = window[1:] + [at(start + length)]
    return [c for c in range(1, p) if remaining >> c & 1]


def finite_cutoffs():
    """Exhaust the finite gap before the analytic guarantee, for lengths 1 to 5."""
    for length in range(1, 6):
        last_prime = None
        exceptions = []
        for p in range(3, 10_001, 2):
            if p <= length or not prime(p):
                continue
            if weil_guarantees(p, length):
                yield length, p, last_prime, exceptions
                break
            missing = missing_discriminants(p, length)
            if missing:
                last_prime, exceptions = p, missing
        else:
            raise RuntimeError("finite window did not reach the analytic guarantee")


if __name__ == "__main__":
    for length, cutoff, last_prime, exceptions in finite_cutoffs():
        print(f"k={length}  Weil from {cutoff}  last failing prime {last_prime}  c={exceptions}")
