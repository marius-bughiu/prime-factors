import unittest
from collections import Counter
from itertools import combinations

from experiments.shifted_sum_divisors import _candidates, nine_bit_ceiling, search
from scripts.factor import primes_through


class ShiftedSumDivisorsTests(unittest.TestCase):
    def test_opaque_composite_and_interval_endpoints(self):
        residual = 37*41
        neighbor = 8*residual
        divisors = (1,2,4,8)
        expected = set(divisors) | {d*residual for d in divisors}
        for lo, hi in [(1,neighbor+1),(8,9),(9,residual),(residual,residual+1)]:
            work = Counter()
            actual = [d for d, _ in _candidates(neighbor,lo,hi,work,False)]
            self.assertEqual(len(actual), len(set(actual)))
            self.assertEqual({d for d in actual if lo<=d<hi}, {d for d in expected if lo<=d<hi})
            self.assertEqual(work['shifts_skipped_by_interval'], int(lo==9))
        work = Counter()
        fully_peeled = [d for d, _ in _candidates(360, 1,361,work,False)]
        self.assertEqual(sorted(fully_peeled),[d for d in range(1,361) if 360%d==0])
        self.assertEqual(work['divisor_multiplications'],len(fully_peeled)-1)

    def test_exact_completeness_when_all_possible_factors_are_peeled(self):
        # Each neighbor is < 37^2, so any residual is either one or a single prime.
        for p, q in combinations((p for p in primes_through(31) if p>=16),2):
            result = search(p*q,5)
            ceiling = nine_bit_ceiling([(p,q)])
            self.assertEqual(bool(result['pair']), bool(ceiling['recovered']))
            if result['pair']:
                self.assertEqual(result['pair'], [str(p),str(q)])
            self.assertEqual(bool(result['first_later']), bool(ceiling['later']))

    def test_heldout_hit_beyond_the_two_pieces(self):
        n = 10162903
        self.assertEqual(search(n,12,two_parts=True)['pair'], [])
        result = search(n,12)
        self.assertEqual(result['pair'], ['3167','3209'])
        witness = result['first_later']
        self.assertEqual(witness['shift'],41)
        p,q = map(int,result['pair'])
        self.assertEqual(int(witness['denominator'])*int(witness['exponent']),
                         int(witness['numerator'])*(p-1)*(q-1))
        self.assertEqual(result['work']['candidate_roots'],1)


if __name__ == '__main__':
    unittest.main()
