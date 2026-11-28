"""Check the shared cycle against all retained positions of selected toy prefixes."""
from bisect import bisect_left
from math import prod

from experiments.six_square_prefix_counts import TESTS, prefix_counts
from experiments.stream_sum_scores import ROWS, bounds


def screen(discriminant, tests):
    for i, (modulus, squares) in enumerate(tests, start=1):
        if discriminant % modulus not in squares:
            return False, i
    return True, len(tests)


def cycle_entries(entries, period, shift, length):
    """Enumerate in order; two adjacent copies of the table meet at a wrap."""
    if not entries:
        return
    cycle, phase = divmod(shift, period)
    slot = bisect_left(entries, phase)
    if slot == len(entries):
        slot = 0
        cycle += 1
    while True:
        index = cycle * period + entries[slot] - shift
        if index >= length:
            return
        yield index
        slot += 1
        if slot == len(entries):
            slot = 0
            cycle += 1


def verify(p, q):
    n = p * q
    target = p + q
    lo, hi = bounds(n, p.bit_length())
    period = prod(m for m, _ in TESTS[:3])
    inverse = pow(100, -1, period)
    table = []
    setup = 0
    for j in range(period):
        passes, charge = screen((100*j)**2 - 4*n, TESTS[:3])
        setup += charge
        if passes:
            table.append(j)
    generated = squares = tail = 0
    row = ROWS[n % 100]
    limit = (dict(row)[target % 100] * (target**2 - 4*n), target)
    for r, scale in row:
        seed = lo + (r - lo) % 100
        length = 0
        expected = []
        for j, s in enumerate(range(seed, hi + 1, 100)):
            disc = s*s - 4*n
            if (scale*disc, s) > limit:
                break
            length += 1
            if screen(disc, TESTS[:3])[0]:
                expected.append(j)
        shift = seed * inverse % period
        emitted = list(cycle_entries(table, period, shift, length))
        if emitted != expected:
            raise AssertionError('Shared cycle and direct prefix disagree')
        for j in emitted:
            passes, charge = screen((seed + 100*j)**2 - 4*n, TESTS[3:])
            squares += passes
            tail += charge
        generated += len(emitted)
    prior, baseline_kept, _ = prefix_counts(p, q)
    if baseline_kept != squares:
        raise AssertionError('Changed the final set of retained square tests')
    # Exercise the last-to-first transition even if all the toy prefixes are short.
    shift = period - 1
    full = list(cycle_entries(table, period, shift, 2 * period + 3))
    expected = [j for j in range(2 * period + 3)
                if screen((100 * (j + shift))**2 - 4*n, TESTS[:3])[0]]
    if full != expected:
        raise AssertionError('Lost an entry across the end of the cycle')
    return dict(old=prior, generated=generated, exact=squares, tail_lookups=tail,
                table_entries=len(table), setup_lookups=setup)


if __name__ == '__main__':
    for p, q in [(521, 1013), (2053, 4091), (8233, 16369)]:
        print(f'{p} × {q}: {verify(p, q)}')
