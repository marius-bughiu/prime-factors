"""Replay the suffix-ranking stopping inequality on four benchmark inputs."""

import json
from math import isqrt, lcm
from pathlib import Path

from experiments.high_word_suffix_ranking import allowed_gaps, propose, square_classes
from experiments.high_word_sum_ranking import check_midpoint, gap_interval


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks' / 'high-word-suffix-ranking.json'
# Expected (setup roots, class counts, stopping tests, first skipped row − floor).
CHECKS = {
    'word-suffix-ranked-gain': (5, 12, 2, 21),
    'word-suffix-ranked-misses': (5, 12, 2, 21),
    'word-suffix-ranked-fresh-2048': (3, 4, 1, 19),
    'word-suffix-ranked-crossed-2048': (3, 4, 1, 3),
}


def tail_test(width, top, midpoint, span):
    """Report strict diameter bound and bit lengths of both operands of each product."""
    square = span * span
    operands = [(span.bit_length(), span.bit_length())]
    if width < square:
        return True, operands

    depth = max(0, midpoint * midpoint - top)
    difference = width - square
    left = difference * difference
    right = (square * depth) << 2
    operands.extend([
        (midpoint.bit_length(), midpoint.bit_length()),
        (difference.bit_length(), difference.bit_length()),
        (square.bit_length(), depth.bit_length()),
    ])
    return left < right, operands


def rank(bits, word, modulus, residue):
    base = 1 << bits
    lower = word * base
    width = base - 1
    top = lower + width
    floor = isqrt(top)
    period = lcm(2, modulus)
    classes = square_classes(modulus)
    allowed = [allowed_gaps(classes, modulus, residue, s) for s in range(period)]
    multiplicity = max(map(len, allowed))

    winner = None
    best = 0
    roots = 1  # floor sqrt(top)
    counts = 0
    tests = []
    stop = None
    for midpoint in range(floor, floor + period + 1):
        residues = allowed[midpoint % period]
        if not residues:
            continue
        if best >= multiplicity:
            span = period * (best // multiplicity)
            smaller, operands = tail_test(width, top, midpoint, span)
            tests.append(operands)
            if smaller:
                stop = midpoint - floor
                break

        low, high, used = gap_interval(base, lower, top, midpoint)
        roots += used
        if low <= high:
            counts += len(residues)
            support = sum((high - r) // period - (low - 1 - r) // period for r in residues)
            if support > best:
                winner, best = midpoint, support

    return winner, best, roots, counts, tests, stop, multiplicity


def main():
    fixtures = {case['id']: case for case in json.loads(FIXTURE.read_text())}
    for name, expected in CHECKS.items():
        case = fixtures[name]
        number = int(case['n'])
        bits, modulus = case['factor_bits'], case['modulus']
        word, residue = number >> bits, number % modulus
        old = propose(bits, word, modulus, residue)
        winner, support, roots, counts, tests, stop, multiplicity = rank(bits, word, modulus, residue)
        if (winner, support) != (old['midpoint'], old['support']):
            raise ValueError(f'{name}: midpoint or support disagrees with the complete block')
        if (roots, counts, len(tests), stop) != expected:
            raise ValueError(f'{name}: unexpected work counts')
        factor, square_tests = check_midpoint(number, winner)
        found = str(factor) if factor is not None else None
        if found != case['checks']['ranked_factor'] or square_tests != case['checks']['square_tests']:
            raise ValueError(f'{name}: selected midpoint disagrees with the benchmark result')

        print(json.dumps({
            'case': name, 'setup_roots': [old['setup_roots'], roots],
            'residue_class_counts': [old['residue_class_counts'], counts],
            'stop_offset': stop, 'maximum_residue_count': multiplicity, 'stopping_tests': len(tests),
            'stop_product_operand_bits': tests, 'final_square_tests': square_tests,
            'factor': found, 'remaining': str(number) if factor is None else None,
        }))


if __name__ == '__main__':
    main()
