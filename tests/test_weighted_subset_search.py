from math import gcd, isqrt
import unittest

from experiments.weighted_subset_search import operations, ordinary, search


class WeightedSubsetSearchTests(unittest.TestCase):
    def test_every_nonempty_mask_on_two_positive_products(self):
        for n, expected_size, expected_factor in ((2222417, 4, 1979), (8928473, 5, 3511)):
            with self.subTest(n=n):
                # Generate the labels by checking their two defining conditions.
                labels, excesses = [1], [1]
                for weight in range(1, 9):
                    stride = gcd(24, 2*(weight+n))
                    a = isqrt(4*weight*n)
                    while a*a < 4*weight*n or (a-weight-n) % stride:
                        a += 1
                    for b in (a, a+stride):
                        labels += [old*b for old in labels]
                        excesses += [old*(b*b-4*weight*n) for old in excesses]
                squares = []
                for mask in range(1, 65536):
                    root = isqrt(excesses[mask])
                    if root*root == excesses[mask]:
                        squares.append((mask, root))
                self.assertEqual(len(squares), 1)
                mask, root = squares[0]
                result = search(n)
                expected_rows = [[i//2+1, i%2] for i in range(16) if mask >> i & 1]
                self.assertEqual(result['witness']['rows'], expected_rows)
                self.assertEqual(result['minimum_rows'], expected_size)
                self.assertEqual(result['factor'], expected_factor)
                self.assertEqual(result['witness']['minus_gcd'], str(gcd(labels[mask]-root, n)))
                self.assertEqual(result['witness']['plus_gcd'], str(gcd(labels[mask]+root, n)))
                self.assertEqual(result['work']['square_subsets'], 1)
                self.assertEqual(result['work']['covered_subsets'], 65535)
                self.assertEqual(result['work']['remaining_subsets'], 0)

    def test_ordinary_matched_and_screened(self):
        n = 137649271
        result, costs = operations(search, n)
        self.assertEqual(result['minimum_rows'], 4)
        self.assertGreater(costs['gcd'], result['work']['label_gcds'])
        self.assertGreater(costs['isqrt'], 8)
        self.assertIsNone(ordinary(n, costs['isqrt']-8)['factor'])
        screened = ordinary(n, costs['isqrt']-8, sieve=True)
        self.assertEqual((screened['factor'], screened['labels'], screened['tests']), (9203, 190, 5))
        self.assertEqual(ordinary(n, 190)['factor'], 9203)

    def test_label_gcd_and_unvisited_subset_space(self):
        direct = search(49)
        self.assertEqual((direct['factor'], direct['outcome']), (7, 'label_gcd'))
        self.assertIsNone(direct['minimum_rows'])
        self.assertEqual(direct['work']['remaining_subsets'], 65535)
        self.assertIsNone(direct['work']['dimension'])
        with self.assertRaises(ValueError):
            search(15)
