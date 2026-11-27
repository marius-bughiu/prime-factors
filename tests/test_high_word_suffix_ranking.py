import unittest
from collections import Counter, defaultdict
from itertools import combinations
from math import isqrt

from experiments.high_word_suffix_ranking import (
    census, local_prefix, prefix_count, propose, scan_fermat, search,
)


class HighWordSuffixRankingTests(unittest.TestCase):
    def test_block_ranking_against_all_odd_pairs_in_one_word(self):
        bits, word, modulus = 10, 519, 24
        base = 1 << bits
        start = isqrt(base * (word + 1) - 1)
        rows = defaultdict(Counter)
        for p, q in combinations(range(base // 2 + 1, base, 2), 2):
            n = p * q
            midpoint = (p + q) // 2
            if n // base == word and start <= midpoint <= start + modulus:
                rows[n % modulus][midpoint] += 1

        # This odd residue has no candidates. Another has a tie above its first occupied row.
        self.assertFalse(rows[13])
        self.assertLess(rows[15][min(rows[15])], max(rows[15].values()))
        self.assertGreater(list(rows[15].values()).count(max(rows[15].values())), 1)
        for residue in range(modulus):
            with self.subTest(residue=residue):
                counts = rows[residue]
                support = max(counts.values(), default=0)
                best = min((mid for mid in counts if counts[mid] == support), default=None)
                result = propose(bits, word, modulus, residue)
                self.assertEqual(result['midpoint'], best)
                self.assertEqual(result['earliest'], min(counts, default=None))
                self.assertEqual(result['support'], support)
                self.assertEqual(result['occupied'], len(counts))
                self.assertEqual(result['rows'], modulus + 1)
                self.assertFalse(result['maximum_proved'])

    def test_shared_66_bit_reading_and_matched_root_scan(self):
        bits, modulus = 33, 120
        first_n = 36893488155787837121
        second_n = 36893488155852544481
        self.assertEqual((first_n >> bits, first_n % modulus),
                         (second_n >> bits, second_n % modulus))
        choices = []
        for n, ranked, first, matched, tests in (
            (first_n, 6073583363, None, 6073583363, 2),
            (second_n, None, 6073682449, 6073682449, 1),
        ):
            with self.subTest(n=n):
                self.assertEqual(n.bit_length(), 66)
                found, work = search(n, bits, modulus)
                self.assertEqual(found, ranked)
                self.assertEqual((work['setup_roots'], work['square_tests']), (25, 1))
                choices.append(work['midpoint'])
                found_first, first_work = scan_fermat(n, modulus, 1)
                self.assertEqual((found_first, first_work['square_tests']), (first, 1))
                budget = work['setup_roots'] + work['square_tests'] - 1
                found_matched, matched_work = scan_fermat(n, modulus, budget)
                self.assertEqual(found_matched, matched)
                self.assertEqual(n % found_matched, 0)
                self.assertEqual((matched_work['setup_roots'], matched_work['square_tests']),
                                 (1, tests))
        self.assertEqual(choices[0], choices[1])

    def test_eight_bit_census_against_actual_filtered_fermat_scans(self):
        primes = [p for p in range(129, 256, 2)
                  if all(p % d for d in range(3, isqrt(p) + 1, 2))]
        for modulus in (24, 120):
            with self.subTest(modulus=modulus):
                observed = Counter()
                readings = set()
                for p, q in combinations(primes, 2):
                    n = p * q
                    if n.bit_length() != 16:
                        continue
                    midpoint = (p + q) // 2
                    readings.add((n >> 8, n % modulus))
                    ranked, work = search(n, 8, modulus)
                    first, _ = scan_fermat(n, modulus, 1)
                    budget = work['setup_roots'] + work['square_tests'] - 1
                    matched, matched_work = scan_fermat(n, modulus, budget)
                    for found in (ranked, first, matched):
                        self.assertIn(found, (None, p))

                    prefix = local_prefix(modulus, n % modulus)
                    start = isqrt(n - 1) + 1
                    needed = prefix_count(midpoint + 1, prefix) - prefix_count(start, prefix)
                    self.assertEqual(matched_work['square_tests'], min(needed, budget))
                    self.assertEqual(matched == p, needed <= budget)

                    earliest = midpoint == work['earliest']
                    observed.update(dict(
                        pairs=1, ranked=ranked == p, earliest=earliest,
                        fermat_with_remainder=first == p, ranked_only=ranked == p and first is None,
                        fermat_only=first == p and ranked is None,
                        gained_vs_earliest=ranked == p and not earliest,
                        lost_vs_earliest=earliest and ranked is None,
                        empty_block=work['midpoint'] is None,
                        fermat_at_ranked_root_budget=matched == p,
                        ranked_only_at_equal_budget=ranked == p and matched is None,
                    ))
                self.assertEqual(observed['pairs'], 148)
                self.assertEqual(observed['ranked_only_at_equal_budget'], 0)
                self.assertEqual(census(8, modulus), dict(
                    factor_bits=8, modulus=modulus, occupied_readings=len(readings), **observed))
