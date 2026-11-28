"""Replay the quotient formula on the public transposed-block fixtures."""

import json
from math import isqrt
from pathlib import Path

from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'benchmarks/transposed-blocks.json'
PROOF = ROOT / 'build/site/proofs/transposed-blocks-2048.lean'


def read_factors(n, base):
    """Return the two factors if they have distinct positive blocks in reverse order."""
    if n < 1 or base < 2:
        return None
    last = n % base
    coarse = n // (base + 1) ** 2
    if coarse < last:
        return None
    block_product = last + base * ((coarse - last) // base)
    gap_square, remainder = divmod(n - (base + 1) ** 2 * block_product, base)
    if remainder:
        return None
    gap = isqrt(gap_square)
    total = isqrt(gap_square + 4 * block_product)
    a, b = (total - gap) // 2, (total + gap) // 2
    if 0 < a < b < base:
        p, q = base * a + b, base * b + a
        if p * q == n:
            return p, q
    return None


def main():
    cases = json.loads(FIXTURES.read_text())
    for case in cases:
        n = int(case['n'])
        base = int(case['radix']) if 'radix' in case else 1 << (n.bit_length() // 4)
        found = read_factors(n, base)
        expected = tuple(map(int, case['factors'])) if case['factors'] else None
        if found != expected:
            raise ValueError(f"Unexpected factor pair for {case['id']}")
        if case['id'] == 'constructed-half-width-2048':
            PROOF.parent.mkdir(parents=True, exist_ok=True)
            PROOF.write_text(render_certificate(n, list(found)))
            verify_file(PROOF)
        print(case['id'], 'recovered' if found is not None else 'miss')


if __name__ == '__main__':
    main()
