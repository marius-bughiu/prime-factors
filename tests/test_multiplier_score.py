import unittest
from collections import Counter
from fractions import Fraction as F
from math import gcd

from experiments.multiplier_score import all_split_certificate, finite_menu, quantized_menu, variance_certificate


class MultiplierScoreTests(unittest.TestCase):
    def test_quantized_masks_match_direct_crt_count(self):
        choices = [1, 3, 5, 7, 11]
        seen = set()
        winners = Counter()
        gain = F(0)
        for n in range(1, 8*3*5*7):
            if gcd(n, 8*3*5*7) != 1:
                continue
            word = n % 8, *(pow(n, (p-1)//2, p) for p in (3, 5, 7))
            if word in seen:
                continue
            seen.add(word)
            scores = {}
            for m in choices:
                d = m*n
                s = 256 * F({1: 4, 3: 1, 5: 2, 7: 1}[d % 8], 3)
                for p in (3, 5, 7):
                    w = (p**256).bit_length()-1
                    if m % p == 0:
                        s += F(w, p+1)
                    elif any(x*x % p == d % p for x in range(1,p)):
                        s += F(2*p*w, p*p-1)
                scores[m] = s - F((m**256).bit_length()-1, 2)
            best = max(choices, key=lambda m: scores[m])
            winners[best] += 1
            gain += (scores[best]-scores[1])/256
        result = quantized_menu(7, 11)
        self.assertEqual(len(seen), result['words'])
        self.assertEqual(dict(winners), result['winners'])
        self.assertEqual(gain/len(seen), result['mean_bits'])

    def test_finite_constants_and_certified_log_intervals(self):
        self.assertLess(variance_certificate(), F(69, 100))
        self.assertLess(all_split_certificate(), F(1, 2**86))
        result = finite_menu()
        self.assertEqual(result['words'], 4096)
        self.assertEqual(result['winners'][1], 1866)
        lo, hi = result['mean_bits']
        self.assertGreater(lo, F(63977, 100000))
        self.assertLess(hi, F(63978, 100000))
