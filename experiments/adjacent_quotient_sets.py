"""Compare adjacent quotient sets, two cached totient sums, and balanced odd trial division."""
import json
from math import isqrt
from pathlib import Path

FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks" / "adjacent-quotient-sets.json"


def compare(n):
    """All three methods receive only the integer n and the balanced-semiprime promise."""
    cap = isqrt(n)
    current = {n // k for k in range(2, cap + 1)}
    previous = {(n - 1) // k for k in range(2, cap + 1)}
    larger, = current - previous
    if previous - current != {larger - 1} or n % larger:
        raise ValueError("unexpected quotient-set difference")
    discovered = [n // larger, larger]

    prefix = list(range(cap + 1))
    sieve_updates = 0
    for prime in range(2, cap + 1):
        if prefix[prime] == prime:
            for j in range(prime, cap + 1, prime):
                prefix[j] -= prefix[j] // prime
                sieve_updates += 1
    for j in range(2, cap + 1):
        prefix[j] += prefix[j - 1]

    cache = {}
    blocks = 0

    def summatory(x):
        nonlocal blocks
        if x <= cap:
            return prefix[x]
        if x in cache:
            return cache[x]
        total = x * (x + 1) // 2
        k = 2
        while k <= x:
            quotient = x // k
            last = x // quotient
            blocks += 1
            total -= (last - k + 1) * summatory(quotient)
            k = last + 1
        cache[x] = total
        return total

    upper = summatory(n)
    first_blocks = blocks
    first_states = set(cache)
    lower = summatory(n - 1)
    prime_sum = n + 1 - (upper - lower)
    discriminant = prime_sum**2 - 4 * n
    root = isqrt(discriminant)
    recovered = [(prime_sum - root) // 2, (prime_sum + root) // 2]
    if root**2 != discriminant or recovered != discovered:
        raise AssertionError("summatory result disagrees with quotient exchange")
    new_states = set(cache) - first_states
    if new_states != {n - 1, larger - 1}:
        raise AssertionError("unexpected large cache states")

    lo = isqrt((n - 1) // 2) + 1
    attempts = 0
    for trial in range(lo | 1, cap + 1, 2):
        attempts += 1
        if n % trial == 0:
            break
    else:
        raise ValueError("no factor within the balanced interval")
    if [trial, n // trial] != discovered:
        raise AssertionError("direct division disagrees with the quotient methods")
    return {
        "factors": [str(value) for value in discovered],
        "keys_per_set": len(current),
        "sieve_updates": sieve_updates,
        "first_blocks": first_blocks,
        "second_blocks": blocks - first_blocks,
        "new_states": len(new_states),
        "trial_divisions": attempts,
    }


if __name__ == "__main__":
    for row in json.loads(FIXTURE.read_text()):
        observed = compare(int(row["n"]))
        for key, value in observed.items():
            if row[key] != value:
                raise AssertionError(f"{row['n']} {key}: {value} versus {row[key]}")
        print(row["n"], json.dumps(observed, sort_keys=True))
