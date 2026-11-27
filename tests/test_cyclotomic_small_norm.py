import unittest

from experiments.cyclotomic_small_norm import census, search


class CyclotomicSmallNorm(unittest.TestCase):
    def test_product_only_probe_and_zero_cap(self):
        factor, work = search(174719, 9, 0)
        self.assertIsNone(factor)
        self.assertEqual((work["outcome"], work["square_probes"], work["unvisited"]),
                         ("test_cap", 1, 1))
        factor, work = search(174719, 9, 1)
        self.assertEqual((factor, work["lower"], work["upper"], work["hit_sum"]),
                         (379, 836, 852, 840))
        self.assertEqual(search(174717, 9, 1)[1]["square_probes"], 0)
        self.assertEqual(search(174729, 9, 1)[1]["outcome"], "no_square")

    def test_complete_nine_bit_population(self):
        self.assertEqual(census(), dict(primes=43, pairs=903, probes=218,
                                       square_witnesses=1, hits=[174719]))
