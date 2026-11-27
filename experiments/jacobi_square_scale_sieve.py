"""Measure square-root calls before and after sieving the first successful square scale."""

from bisect import bisect_right
import json
from math import isqrt
from pathlib import Path
from unittest.mock import patch

from experiments import predecessor_square


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-square-scale-sieve.json'
PERIOD = 900
SQUARES = (4, 9, 25)


def make_table():
    """Build the list once, recording the exact number of divisibility checks."""
    offsets = []
    divisions = 0
    for value in range(1, PERIOD+1):
        for square in SQUARES:
            divisions += 1
            if value % square == 0:
                break
        else:
            offsets.append(value)
    return offsets, divisions


def sieved_search(n, cap, offsets):
    evaluations = 0
    table_reads = 0
    for block in range(0, cap, PERIOD):
        for offset in offsets:
            table_reads += 1
            scale = block + offset
            if scale > cap:
                break
            evaluations += 1
            root = predecessor_square.isqrt(n) - 1 if scale == 1 else predecessor_square.isqrt(n//scale)
            factor = predecessor_square.factor_from_sum(n, n+1 - scale*root**2)
            if factor is not None:
                return factor, scale, evaluations, table_reads
    return None, cap, evaluations, table_reads


def compare(n, cap, offsets):
    # Count the calls in the original search, including its conditional
    # discriminant square root. The patch is local to this single-threaded checker.
    with patch.object(predecessor_square, 'isqrt', wraps=isqrt) as roots:
        plain = predecessor_square.search(n, cap)
        plain_roots = roots.call_count
    with patch.object(predecessor_square, 'isqrt', wraps=isqrt) as roots:
        factor, stop, evaluations, reads = sieved_search(n, cap, offsets)
        sieve_roots = roots.call_count
    assert (factor, stop) == (plain['factor'], plain['scales_tested'])
    assert evaluations == len(offsets)*(stop//PERIOD) + bisect_right(offsets, stop%PERIOD)
    return dict(n=n, cap=cap, factor=factor, covered_through=stop,
                plain_scale_roots=stop, plain_discriminant_roots=plain_roots-stop,
                sieved_scale_roots=evaluations, sieved_discriminant_roots=sieve_roots-evaluations,
                table_reads=reads)


def main():
    offsets, divisions = make_table()
    assert len(offsets) == 576
    print(json.dumps(dict(period=PERIOD, retained_offsets=len(offsets),
                          one_time_residues=PERIOD, one_time_modulo_checks=divisions)))
    for case in json.loads(FIXTURE.read_text()):
        n, cap = int(case['n']), case['cap']
        result = compare(n, cap, offsets)
        # Expected prime factors only validate the observed stop and split.
        p, q = map(int, case['factors'])
        assert p*q == n and 1 < p < q <= 2*p
        assert result['factor'] == (p if case['hit'] else None)
        for key in ('covered_through', 'sieved_scale_roots', 'plain_discriminant_roots',
                    'sieved_discriminant_roots'):
            assert result[key] == case[key], (n, cap, key, result[key])
        print(json.dumps(result))


if __name__ == '__main__':
    main()
