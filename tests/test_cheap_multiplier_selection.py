import unittest
from math import gcd
from experiments.cheap_multiplier_selection import LOOKUP, catalogue, choose, compile_lookup, evaluate, search, two_sided


class CheapMultiplierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tables = catalogue()

    def test_fixed_public_table_and_choice(self):
        self.assertEqual(compile_lookup(self.tables),6528)
        for n in range(513,4096,2):
            if gcd(n,6)!=1:
                continue
            hi = (1<<((n.bit_length()+1)//2))-1
            expected = 1
            for b,a,k in LOOKUP[n%24]:
                if a*n<=b*hi*hi:
                    expected = k
            self.assertEqual(choose(n)[0],expected)

    def test_prospective_split_and_matched_miss(self):
        n = 802471205089
        selected = search(n,self.tables)
        self.assertEqual(selected['k'],12)
        self.assertEqual(selected['factors'],[776429])
        ordinary = evaluate(n,[(1,33)],self.tables)
        self.assertEqual(ordinary['total_roots'],selected['total_roots'])
        self.assertEqual(ordinary['factors'],[])
        self.assertEqual(two_sided(0,0)['approx'],1)
        self.assertEqual(two_sided(2,0)['approx'],0.5)


if __name__ == '__main__':
    unittest.main()
