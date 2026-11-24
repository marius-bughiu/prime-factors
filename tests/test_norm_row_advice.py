from fractions import Fraction
from itertools import combinations
from math import gcd
import unittest

from experiments.gap_coverage import primes_through
from experiments.norm_band_product import search
from experiments.norm_row_advice import canonical_row, optimal, target_bound


class CanonicalNormRowsTests(unittest.TestCase):
    def test_unique_prime_occurrence_in_the_balanced_band(self):
        primes = primes_through(127)[1:]
        for p,q in combinations(primes,2):
            if q>2*p:
                continue
            n=p*q
            r=search(n,100,balanced=True,canonical=True)
            self.assertEqual(r['factor'],p)
            height, low, high = (int(r[key]) for key in ('side','smaller_lower','smaller_upper'))
            hits=[]
            for t in range(1,height+1,2):
                for a in range(1,height+1):
                    candidates = [(-2,t*t+2*a*a)] if a%2 else [(-1,t*t+a*a)]
                    if not a%2 and t<a:
                        candidates.append((2,2*a*a-t*t))
                    for d,value in candidates:
                        if low<=value<=high and gcd(value,n)>1:
                            hits.append((d,a))
            self.assertEqual(hits,[canonical_row(p)])

    def test_indefinite_duplicate(self):
        n=167*311
        self.assertEqual(canonical_row(167),(2,12))
        original=search(n,15,balanced=True)
        tight=search(n,15,balanced=True,canonical=True)
        self.assertEqual((original['allowed_pairs'],tight['allowed_pairs']),(30,29))
        self.assertEqual(2*14**2-15**2,167)

    def test_optimal_two_rows_against_exhaustive_portfolios(self):
        pairs=[(p*q,canonical_row(p)) for p,q in combinations(primes_through(63),2)
               if p>=32 and p*q>=2048]
        result=optimal(pairs,6,2,1,[2])
        buckets={}
        for n,row in pairs:
            buckets.setdefault(((n-2048)//512,(n%4)//2),[]).append(row)
        def best(rows):
            choices=list(set(rows))
            return max(sum(r in selected for r in rows)
                       for selected in combinations(choices,min(2,len(choices))))
        self.assertEqual(result['hits']['2'],sum(best(rows) for rows in buckets.values()))

    def test_finite_population_constants(self):
        self.assertLess(target_bound(0,1023,2**450),Fraction(1,2**36))
        self.assertLess(target_bound(1023,0,2**40),Fraction(1,2**446))
        self.assertLess(target_bound(1000,469,2**40),Fraction(1,2))
        self.assertGreaterEqual(target_bound(1000,470,2**40),Fraction(1,2))
