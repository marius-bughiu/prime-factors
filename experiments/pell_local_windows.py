"""Find small lifted squares of signed products of nearby complete denominators."""

from argparse import ArgumentParser
from collections import deque
from json import dumps
from math import gcd, isqrt


SQUARE_RESIDUES = frozenset(x * x % 240 for x in range(240))


def search(n, max_steps=4096, depth=8):
    """Scan one regular continued fraction and retain the first hit of each type."""
    base = isqrt(n)
    if n < 3 or base * base == n:
        raise ValueError('expected a nonsquare integer greater than two')
    if max_steps < 0 or depth < 0:
        raise ValueError('budgets must be nonnegative')
    history = deque(maxlen=depth)
    p, q, a = 0, 1, base
    report = dict(steps=0, period_complete=False, pairs=0, candidates=0, root_tests=0,
                  ordinary_pair=None, shifted_pair=None)
    for j in range(1, max_steps + 1):
        # The quotient stored with a row is the one that led into that row.
        row_incoming = a
        p = a * q - p
        q = (n - p * p) // q
        a = (base + p) // q
        report['steps'] = j
        incoming = row_incoming
        u, v = 1, 0
        for distance, (start_p, start_q, start_incoming) in enumerate(reversed(history), 1):
            u, v = incoming * u + v, u
            incoming = start_incoming
            if (base + 1) * (v + 4) >= n:
                break
            report['pairs'] += 1
            product = (-1 if distance % 2 else 1) * start_q * q
            residue = product % n
            for radicand in range(residue, 4 * n, n):
                shift = (radicand - product) // n
                if shift == v * v:
                    continue
                report['candidates'] += 1
                if radicand % 240 not in SQUARE_RESIDUES:
                    continue
                report['root_tests'] += 1
                z = isqrt(radicand)
                if z * z != radicand:
                    continue
                w = abs(start_q * u - start_p * v)
                factor = gcd(w + z, n)
                if w*w - z*z != (v*v - shift)*n or not 1 < factor < n:
                    raise ArithmeticError('lifted square violated the window identity or height bound')
                kind = 'shifted_pair' if shift else 'ordinary_pair'
                if report[kind] is None:
                    report[kind] = dict(i=j-distance, j=j, v=v, w=w, z=z, k=shift,
                                        signed_product=product, factor=factor)
        history.append((p, q, row_incoming))
        if q == 1:
            report['period_complete'] = True
            break
    return report


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-steps', type=int, default=4096)
    parser.add_argument('--depth', type=int, default=8)
    options = parser.parse_args()
    print(dumps(search(options.n, options.max_steps, options.depth), indent=2))
