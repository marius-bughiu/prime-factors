"""Compare local lifted squares, plain square rows, and Fermat on fixed prime pairs."""

import argparse
import hashlib
import json
import sys
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.pell_local_windows import search
from experiments.pell_pairs import convergents


def draw_prime(side, sample):
    prefix = b'pell-local-windows-v1\0' + side + sample.to_bytes(8, 'big')
    counter = 0
    while True:
        digest = hashlib.shake_256(prefix + counter.to_bytes(8, 'big')).digest(3)
        p = (int.from_bytes(digest, 'big') & ((1 << 21)-1)) | (1 << 20) | 1
        if all(p % d for d in range(3, isqrt(p)+1, 2)):
            return p
        counter += 1


def square_row(n, steps):
    for j, denominator, sign, numerator, _ in convergents(n, 1, steps):
        if sign == 1:
            z = isqrt(denominator)
            if z*z == denominator:
                for root in (z, -z):
                    f = gcd(numerator+root, n)
                    if 1 < f < n:
                        return dict(j=j, factor=f)
        if denominator == 1:
            break


def fermat(n, steps):
    a = isqrt(n-1) + 1
    for j in range(1, steps+1):
        d = a*a - n
        b = isqrt(d)
        if b*b == d and 1 < a-b < n:
            return dict(j=j, factor=a-b)
        a += 1


def run():
    rows = []
    sample = 0
    while len(rows) < 32:
        p, q = sorted(draw_prime(side, sample) for side in (b'p', b'q'))
        sample += 1
        if p == q:
            continue
        n = p*q
        windows = search(n)
        row = dict(sample=sample-1, n=str(n), factors=[str(p), str(q)], windows=windows,
                   square_row=square_row(n, 4096), fermat=fermat(n, 4096))
        for result in (windows['ordinary_pair'], windows['shifted_pair'], row['square_row'],
                       row['fermat']):
            if result and result['factor'] not in (p, q):
                raise ArithmeticError(f'incorrect factor in sample {sample-1}')
        rows.append(row)
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='check all prime factors in Lean')
    options = parser.parse_args()
    rows = run()
    if options.verify:
        from scripts.factor import render_certificate, verify_file
        directory = ROOT / 'build' / 'pell-window-holdout'
        directory.mkdir(parents=True, exist_ok=True)
        for row in rows:
            path = directory / f"case-{row['sample']}.lean"
            path.write_text(render_certificate(int(row['n']), [int(p) for p in row['factors']]))
            verify_file(path)
    print(json.dumps(rows, indent=2))
