"""Count modular witnesses on product-only factor remainders in the balanced interval."""

import argparse
from hashlib import shake_256
import json
from math import isqrt
from pathlib import Path

from .modular_hyperbola import Work, floor_sum, high_interval


def lane(n, r, u):
    if n < 3 or n % 2 == 0 or r < 2 or r & (r-1) or u % 2 == 0 or not 0 < u < r:
        raise ValueError('expected an odd product, a dyadic radix and an odd reduced remainder')
    inv = pow(u, -1, r)
    w = n*inv % r
    a = -w*inv % r
    c = ((n-u*w)//r)*inv % r
    x0, x1 = high_interval(max(2, isqrt((n-1)//2)+1), isqrt(n)+1, u, r)
    y0, y1 = high_interval(isqrt(n-1)+1, isqrt(2*n)+1, w, r)
    return w, a, c, x0, x1, y0, y1


def count(n, r, u):
    _, a, c, x0, x1, y0, y1 = lane(n, r, u)
    work = Work()
    height = c+a*x0+r
    hits = (floor_sum(x1-x0, r, a, height-y0, work)
            - floor_sum(x1-x0, r, a, height-y1, work))
    return hits, work.euclidean_steps


def approximant(a, r, h):
    """Last convergent with denominator at most h, computed by Euclidean division."""
    if h < 1:
        raise ValueError('the denominator budget must be positive')
    p0, q0, p, q = 0, 1, 1, 0
    top, bottom = a, r
    while bottom:
        step, rem = divmod(top, bottom)
        if step*q+q0 > h:
            break
        p0, q0, p, q = p, q, step*p+p0, step*q+q0
        top, bottom = bottom, rem
    return p,q


def witness(n, r, u, h):
    """Construct one modular point when the reduced approximation covers the window."""
    w, a, c, x0, x1, y0, y1 = lane(n, r, u)
    p, q = approximant(a, r, h)
    if q > x1-x0 or y0 >= y1:
        return None
    center = (y0+y1-1)//2
    t = ((center-c-a*x0)*q)//r
    v = t*pow(p, -1, q) % q
    z = c+a*(x0+v)-r*((p*v-t)//q)
    if not y0 <= z < y1:
        return None
    x, y = u+r*(x0+v), w+r*z
    if (x*y-n) % (r*r):
        raise ArithmeticError('constructed point failed the product congruence')
    return x,y


def sample(n, r, size):
    """Choose distinct odd words deterministically using only the product and the sample index."""
    if size > r//2:
        raise ValueError('sample exceeds the number of odd words')
    words = set()
    i = 0
    while len(words) < size:
        seed = f'prime-factors/affine-window-occupancy/v1/{n}/{i}'.encode('ascii')
        word = int.from_bytes(shake_256(seed).digest((r.bit_length()+7)//8), 'big')
        words.add((word % r) | 1)
        i += 1
    return sorted(words)


def panel():
    directory = Path(__file__).resolve().parents[1]/'research'
    small = json.loads((directory/'quartic-lane-holdout.json').read_text())['rows']
    census = []
    for row in small:
        n = int(row['n'])
        e = (614*n.bit_length()+2047)//2048
        r = 1 << e
        counts = {u: count(n, r, u)[0] for u in range(1, r, 2)}
        u = min(map(int, row['expected_factors'])) % r
        hits = counts[u]
        census.append(dict(n=str(n), exponent=e, lanes=len(counts),
                           occupied=sum(k>0 for k in counts.values()), true_lane_count=hits,
                           lower=sum(k<hits for k in counts.values()), tied=sum(k==hits for k in counts.values())))
    control = json.loads((directory/'certified-control.json').read_text())
    n = int(control['product'])
    r, h = 1 << 614, 1 << 405
    words = sample(n, r, 256)
    counts = []
    steps = constructed = exact_pairs = 0
    for u in words:
        hits, divisions = count(n, r, u)
        xy = witness(n, r, u, h)
        steps += divisions
        constructed += xy is not None
        exact_pairs += xy is not None and xy[0]*xy[1] == n
        counts.append(hits)
    # Only now read the known construction labels to evaluate the count on the true smaller lane.
    p = min(int(chain[-1]['prime']) for chain in control['chains'].values())
    true_hits, _ = count(n, r, p%r)
    return dict(small=census, control=dict(n=str(n), exponent=614, sample_size=len(words),
                occupied=sum(k>0 for k in counts), min_count=str(min(counts)), max_count=str(max(counts)),
                true_smaller_count=str(true_hits), sample_below_true=sum(k<true_hits for k in counts),
                sample_equal_true=counts.count(true_hits), euclidean_steps=steps,
                constructed_modular_points=constructed, exact_products=exact_pairs))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='*', type=int, metavar='INTEGER',
                        help='supply N, radix, remainder, or omit all three for the fixed panel')
    args = parser.parse_args()
    if args.input and len(args.input) != 3:
        parser.error('expected N, radix, remainder')
    if args.input:
        hits, steps = count(*args.input)
        print(json.dumps(dict(count=str(hits), euclidean_steps=steps)))
    else:
        print(json.dumps(panel(), indent=2))
