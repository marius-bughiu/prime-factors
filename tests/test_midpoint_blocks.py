import unittest
from math import isqrt, prod
from random import Random

from experiments.midpoint_blocks import block_shape, masked_reading
from experiments.midpoint_readings import reading


class MidpointBlockTests(unittest.TestCase):
    def check_direct(self, n, start, length, seed, row_mask, col_mask):
        result = masked_reading(n, start, length, seed, row_mask, col_mask)
        signs = []
        for index in range(length):
            row, col = divmod(index, result['columns'])
            if row_mask & (1 << row) and col_mask & (1 << col):
                signs.append(reading((start+2*index)**2-n, seed))
        self.assertEqual(result['work']['selected_entries'], len(signs))
        self.assertEqual(result['sign_product'], prod(signs))
        self.assertEqual(result['pass_parity'], signs.count(1) % 2)
        return result

    def test_all_256_masks_of_published_fixture(self):
        hits = 0
        for rows in range(16):
            for cols in range(16):
                result = self.check_direct(1900014700027, 1378412, 16, 600600, rows, cols)
                hits += result['pass_parity']
        self.assertEqual(hits, 112)
        work = masked_reading(1900014700027, 1378412, 16, 600600)['work']
        self.assertEqual(work['selected_entries'], 16)
        self.assertEqual(work['exceptional_singletons'], 3)
        self.assertGreater(work['nonunit_blocks'], work['exceptional_singletons'])
        self.assertGreater(work['small_prime_signs'], 0)
        self.assertGreater(work['horner_steps'], work['polynomial_evaluations'])

    def test_bounded_composite_masks_against_scalar_readings(self):
        rng = Random(80567)
        for _ in range(1500):
            n = rng.randrange(4, 200000)
            length = rng.randrange(1, 100)
            rows, cols = block_shape(length)
            seed = rng.randrange(2, 151)*rng.randrange(2, 151)
            masks = rng.getrandbits(rows), rng.getrandbits(cols)
            with self.subTest(n=n, length=length, seed=seed, masks=masks):
                self.check_direct(n, isqrt(n)+1, length, seed, *masks)

    def test_partial_row_and_prime_powers(self):
        n, start, length = 101*149, 123, 17
        # The third row contains just its first column. All other bits are padding.
        for seed in (1, 2**9, 3**4*5**2, 5**3*11**2*13):
            for cols, expected in [(0xfe, 0), (0xff, 1)]:
                result = self.check_direct(n, start, length, seed, 0b100, cols)
                self.assertEqual(result['work']['tail_readings'], expected)
                self.assertEqual(result['work']['polynomial_evaluations'], 0)
        for seed in (1, 2**9, 3**4*5**2):
            result = self.check_direct(n, start, length, seed, 0b111, 0xff)
            self.assertEqual(result['work']['small_prime_signs'], 0)
            self.assertEqual(result['work']['polynomial_evaluations'], 0)

    def test_single_position_matching_whole_or_partial_residual_modulus(self):
        # 7² - 34 = 15; seeds share all, some, or none of its odd primes.
        for seed in (1, 2, 3**3*5**2, 5*7*11, 7*11):
            self.check_direct(34, 7, 1, seed, 1, 1)

    def test_input_bounds(self):
        for args in [(0, 3, 1, 1), (9, 3, 1, 1), (3, 2, 0, 1), (3, 2, 1, 0),
                     (3, 2, 1, 2, -1, 1), (3, 2, 1, 2, 1, 2)]:
            with self.assertRaises(ValueError):
                masked_reading(*args)
