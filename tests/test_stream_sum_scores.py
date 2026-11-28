import unittest

from experiments.location_weighted_sum_order import replay
from experiments.stream_sum_scores import Counts, Head, ROWS, census, retrospective_ranks, search


class StreamSumScoresTests(unittest.TestCase):
    def test_discriminant_recurrence_and_exact_tie(self):
        counts = Counts()
        head = Head(47, 47**2 - 4*113, 4, counts)
        for s in (47, 147, 247):
            self.assertEqual((head.s, head.disc, head.delta, head.key),
                             (s, s*s-4*113, 200*s+10000, (4*(s*s-4*113), s)))
            head.advance()
        self.assertEqual(counts.recurrence_additions, 9)
        self.assertEqual(counts.key_multiplications, 4)
        self.assertLess(Head(5, 4, 25, counts), Head(6, 25, 4, counts))

    def test_empty_and_short_populations(self):
        self.assertEqual(census(2)['pairs'], 0)
        found, counts = search(35, 3, weighted=True)
        self.assertEqual(found, (5, 7))
        self.assertEqual((counts.row_entries, counts.seeds, counts.square_tests), (20, 1, 1))
        self.assertEqual((counts.heap_comparisons, counts.key_multiplications), (0, 0))
        self.assertEqual(max(len(row) for n, row in enumerate(ROWS) if n % 5), 10)
        with self.assertRaises(ValueError):
            search(35, 14, weighted=True)
        with self.assertRaises(ValueError):
            search(1 << 29, 15, weighted=True)

    def test_both_directions_and_equal_weight_branch(self):
        for n, bits in ((134599, 9), (132289, 9), (503*509, 9)):
            eager = replay(n, bits)
            ranks = []
            for name, weighted in (('ascending', False), ('weighted', True)):
                found, counts = search(n, bits, weighted=weighted)
                self.assertEqual(found, eager['factors'])
                self.assertEqual(counts.square_tests, eager['tests'][name])
                self.assertEqual(counts.heap_exhaustions + counts.heap_replacements + 1,
                                 counts.square_tests)
                ranks.append(counts.square_tests)
            self.assertEqual(tuple(ranks), retrospective_ranks(n, bits, sum(found)))
        self.assertEqual(search(503*509, 9, weighted=False), search(503*509, 9, weighted=True))

    def test_complete_nine_bit_census(self):
        row = census(9)
        self.assertEqual(row['pairs'], 543)
        self.assertEqual(row['ascending']['square_tests'], 749)
        self.assertEqual(row['weighted']['square_tests'], 735)
        for name in ('ascending', 'weighted'):
            self.assertLessEqual(row[name]['peak_heads'], 10)
            self.assertEqual(row[name]['heap_builds'], 543)
            self.assertEqual(row[name]['recurrence_additions'], 3*row[name]['heap_replacements'])


if __name__ == '__main__':
    unittest.main()
