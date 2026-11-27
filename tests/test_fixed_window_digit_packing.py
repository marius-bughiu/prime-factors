import unittest

from experiments.fixed_window_digit_packing import collision, index_window, recover_singleton


class FixedWindowDigitPackingTests(unittest.TestCase):
    def test_singleton_and_one_position_shift(self):
        n = 7294033
        self.assertEqual(recover_singleton(n, 12, 315), (5474, ['2293', '3181']))
        self.assertIsNone(recover_singleton(n, 12, 63))

        stride, start, count, mask = index_window(n, 12, 63)
        self.assertEqual((stride, start, count), (4, 1822107, 52))
        self.assertIsNone(collision(mask, count, stride//2, 8))
        shifted = mask[1:] + mask[:1]
        self.assertEqual(collision(shifted, count, stride//2, 8), (23, 51))
