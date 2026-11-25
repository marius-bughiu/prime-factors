"""Replay the same one-residue guess on the full-size prime pairs in the earlier benchmark."""

import json
from pathlib import Path
import platform
from time import perf_counter

from .unit_factor_lane import search
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
# One entry per distinct completely certified balanced 2048-bit product at 4e5c2a6,
# plus the crossed comparison product on which this choice of remainder originated.
PANEL = [
    ('cases', 'fermat-maximal-score-2048'),
    ('continued-square', 'continued-square-2048'),
    ('gap-stride', 'gap-stride-2048'),
    ('line-powers', 'dickson-square-1-2048'),
    ('polynomial-packets', 'packet-square-2048'),
    ('predecessor-square', 'predecessor-square-2048'),
    ('reduced-orders', 'reduced-2048'),
    ('seed-gap-sieve', 'seed-gap-planted-2048'),
    ('shifted', 'shifted-2048'),
    ('line-powers', 'dickson-crossed-control-2048'),
]


def run():
    cases = {}
    for filename, name in PANEL:
        fixtures = json.loads((ROOT/'benchmarks'/f'{filename}.json').read_text())
        cases[name] = next(c for c in fixtures if c['id'] == name)

    rows = []
    for _, name in PANEL:
        n = int(cases[name]['n'])
        start = perf_counter()
        result = search(n)
        elapsed = perf_counter()-start
        rows.append(dict(source=name, search_seconds=elapsed, result=result))

    # Compare to the source labels only after finishing all product-only searches.
    primes = {int(p) for c in cases.values() for p in c.get('factors', [])}
    folder = ROOT/'build'/'unit-lane-panel'
    folder.mkdir(parents=True, exist_ok=True)
    for row in rows:
        result = row['result']
        n = int(result['n'])
        expected = sorted(p for p in primes if n % p == 0)
        if len(expected) != 2 or expected[0]*expected[1] != n:
            raise ValueError(f"missing reference prime pair for {row['source']}")
        hit = any(p % result['radix'] == 1 for p in expected)
        if result['pairs'] != ([list(map(str, expected))] if hit else []):
            raise ValueError(f"unexpected search outcome for {row['source']}")
        row['remaining'] = [] if hit else [str(n)]
        row['verified'] = False
        if hit:
            proof = folder/(row['source']+'.lean')
            proof.write_text(render_certificate(n, list(map(int, result['pairs'][0]))))
            verify_file(proof)
            row['verified'] = True
    return dict(platform=platform.platform(), python=platform.python_version(), rows=rows)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
