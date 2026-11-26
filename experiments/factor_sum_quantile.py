"""A product-only split of the factor-sum interval for two equally wide primes."""

from math import isqrt

from experiments.streamed_sum_join import search


def sum_bounds(n, bits):
    """Inclusive lower, central and upper sums, with strict upper factor bound 2^bits."""
    if bits < 2 or n <= 0 or n.bit_length() != 2 * bits:
        raise ValueError('expected a full-width product of two equally wide primes')
    bound = 1 << bits
    lower = isqrt(4 * n - 1) + 1
    upper = (bound * bound + n - 1) // bound
    # For a sum s >= 2 sqrt(n), the central test is
    # bound^2 (s^2 - 2n)^2 <= n (bound^2 + n)^2.
    center = isqrt(2 * n + isqrt(n * (bound * bound + n)**2) // bound)
    return lower, min(upper, center), upper


def compare(n, bits, *, max_right, max_visited):
    """Compare the same capped join on the full interval and each of its two pieces."""
    lower, central, upper = sum_bounds(n, bits)
    options = dict(candidates=(2,), max_right=max_right, max_visited=max_visited,
                   folded=True, reverse=True)
    report = {}
    for name, interval in [('full', (lower, upper)), ('inner', (lower, central)),
                           ('outer', (central + 1, upper))]:
        run = search(n, **options, sum_interval=interval)
        work = run['work']
        # Large residues and sums stay decimal strings in the machine-readable results.
        report[name] = dict(lower=str(interval[0]), upper=str(interval[1]),
                            positions=str(max(0, interval[1] - interval[0] + 1)),
                            outcome=run['outcome'], factors=run['factors'],
                            right_potential=work['right_potential'], right_built=work['right_built'],
                            left_potential=work['left_potential'], left_visited=work['left_visited'],
                            left_unvisited=work['left_unvisited'], square_tests=work['square_tests'])
    return report
