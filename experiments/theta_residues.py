"""Read a factor residue from the first Rogers–Ramanujan series on bounded inputs."""

from math import isqrt


def coefficient_mod(n, modulus):
    """Return [x^n] xG'/G using the sum side, without testing any divisors."""
    # At step j, partitions[t] is [x^t] 1 / ((1-x)...(1-x^j)).
    partitions = [1] + [0] * n
    series = [1] + [0] * n
    for j in range(1, isqrt(n) + 1):
        shift = j * j
        for t in range(j, n - shift + 1):
            partitions[t] = (partitions[t] + partitions[t - j]) % modulus
        for t in range(n - shift + 1):
            series[t + shift] = (series[t + shift] + partitions[t]) % modulus

    # In G * A = xG', the constant coefficient of G is one.
    logarithmic = [0] * (n + 1)
    for i in range(1, n + 1):
        previous = sum(logarithmic[d] * series[i - d] for d in range(1, i))
        logarithmic[i] = (i * series[i] - previous) % modulus
    return logarithmic[n]


def search(n, max_index):
    """Try the character modulo five and a bounded completion for balanced factors."""
    if n < 3 or n % 2 == 0 or max_index < 0:
        raise ValueError("n must be odd and at least three, and max_index nonnegative")
    modulus = 1 << ((n.bit_length() + 3) // 4)
    result = dict(outcome="character", factor=None, modulus=modulus,
                  coefficient_mod=None, factor_mod=None, convolution_terms=0,
                  candidates_tested=0)
    if n % 5 not in (2, 3):
        return result
    if n > max_index:
        result["outcome"] = "budget"
        return result

    coefficient = coefficient_mod(n, modulus)
    residue = (coefficient - 1) % modulus
    result.update(outcome="exhausted", coefficient_mod=coefficient, factor_mod=residue,
                  convolution_terms=n * (n - 1) // 2)
    lower = isqrt((n - 1) // 2) + 1
    upper = isqrt(2 * n)
    start = lower + (residue - lower) % modulus
    for candidate in range(start, upper + 1, modulus):
        result["candidates_tested"] += 1
        if 1 < candidate < n and n % candidate == 0:
            result.update(outcome="factor", factor=candidate)
            break
    return result
